use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    rc::Rc,
};

use colored::Colorize;

use super::{hir, primitive::PrimitiveKind};
use crate::{
    frontend::{
        ast::{
            self, Block, FunctionDefinition, FunctionParameter, Local, Module, ModuleId, NodeId,
            visit::{self, Visitor},
        },
        intern::InternedSymbol,
        lexer::Span,
    },
    index::{Index, IndexVec},
    session::Session,
};

/// AST name resolver
///
/// Traverses the AST for a crate and creates a map from type and value names
/// to their definitions within the source code.
#[derive(Debug)]
pub struct Resolver<'a> {
    session: &'a Session,
    module_map: &'a IndexVec<ModuleId, Module>,

    /// A list of built-in function names which we allow resolutions for
    builtin_primitives: BTreeMap<InternedSymbol, PrimitiveKind>,

    /// A list of built-in function names which we allow resolutions for
    builtin_functions: BTreeSet<InternedSymbol>,

    // Used to keep track of the definitions that exist within the current crate
    next_local_def_id: hir::LocalDefId,
    // Maps the IDs of AST owners to the def IDs we've assign to them
    node_to_local_def_id_map: BTreeMap<NodeId, hir::LocalDefId>,

    /// constructed during definition collection
    local_definition_maps: BTreeMap<ModuleId, LocalDefinitionMap>,
    /// constructed during early resolution
    global_scopes: BTreeMap<ModuleId, GlobalScope>,

    // Maps name references to definitions
    value_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
    type_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
}

/// Tracks the value and type definitions within a particular module
/// (constructed during definition collection)
#[derive(Debug, Default)]
struct LocalDefinitionMap {
    values: BTreeMap<InternedSymbol, (hir::DefinitionKind, hir::LocalDefId)>,
    types: BTreeMap<InternedSymbol, (hir::DefinitionKind, hir::LocalDefId)>,

    /// Maps methods on type names to their definitions
    methods: BTreeMap<InternedSymbol, BTreeMap<InternedSymbol, hir::LocalDefId>>,
    /// Maps enum definition ids to lists of their members
    enum_members: BTreeMap<hir::LocalDefId, BTreeMap<InternedSymbol, hir::LocalDefId>>,
}

/// Map of identifiers in the global scope to their resolutions (constructed
/// during definition collection and import resolution)
#[derive(Debug, Default)]
struct GlobalScope {
    // Maps names of definitions in the global scope to their resolutions
    value_scope: BTreeMap<InternedSymbol, hir::Resolution<NodeId>>,
    type_scope: BTreeMap<InternedSymbol, hir::Resolution<NodeId>>,
}

/// The result of resolving everything in a module
#[derive(Debug)]
pub struct ResolutionMap {
    /// Maps AST item node ids to their def ids
    pub node_to_def_id_map: BTreeMap<NodeId, hir::LocalDefId>,
    /// Maps the usage of value identifiers (variable names) to their point of
    /// original definition
    pub value_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
    /// Maps the usage of type identifiers to their point of original definition
    pub type_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
}

impl<'a> Resolver<'a> {
    pub fn new(session: &'a Session, module_map: &'a IndexVec<ModuleId, Module>) -> Self {
        Self {
            session,
            module_map,
            builtin_primitives: BTreeMap::from_iter(
                PrimitiveKind::ALL
                    .iter()
                    .map(|p| (InternedSymbol::new(&p.to_string()), *p)),
            ),
            builtin_functions: BTreeSet::from([
                InternedSymbol::new("print"),
                InternedSymbol::new("exit"),
                InternedSymbol::new("str"),
                InternedSymbol::new("read"),
                InternedSymbol::new("open"),
                InternedSymbol::new("close"),
            ]),
            next_local_def_id: hir::LocalDefId::new(0), // TODO: should this be reserved for the module itself?
            node_to_local_def_id_map: BTreeMap::new(),
            local_definition_maps: BTreeMap::new(),
            global_scopes: BTreeMap::new(),
            value_name_resolutions: BTreeMap::new(),
            type_name_resolutions: BTreeMap::new(),
        }
    }

    /// The first step resolves imports and locates all the definitions of
    /// custom types and functions. These imports and custom types are then
    /// bound in the global value and type scopes
    pub fn collect_definitions(&mut self, module_id: ModuleId) {
        let module = &self.module_map[module_id];
        let mut def_collector = DefinitionCollector::new(self, module);
        visit::walk_module(&mut def_collector, module);
    }

    /// The second step traverses the AST and makes sure any references to types
    /// or values are defined in this module's scope or are imported. It also
    /// keeps track of function parameters and local variables to make sure all
    /// identifiers are valid. Field and method accesses are not checked at this
    /// stage and are resolved during module type checking.
    pub fn resolve_names(&mut self, module_id: ModuleId) {
        let module = &self.module_map[module_id];

        let mut early_resolver = EarlyResolveVisitor::new(self, module);
        visit::walk_module(&mut early_resolver, module);

        // TODO: now that we know which types are in scope, revisit all of the
        // method definitions to check for any duplicate definitions

        let mut late_resolver = LateResolveVisitor::new(self, module);
        visit::walk_module(&mut late_resolver, module);

        // TODO: warn about unused imports
    }

    /// Returns the useful output of the resolver after successfully completing
    /// resolutions and macro expansions in the requested modules
    pub fn into_outputs(self) -> ResolutionMap {
        ResolutionMap {
            node_to_def_id_map: self.node_to_local_def_id_map,
            value_name_resolutions: self.value_name_resolutions,
            type_name_resolutions: self.type_name_resolutions,
        }
    }

    /// Records a definition in several maps and adds the name to the
    /// appropriate global scope
    pub fn create_definition(
        &mut self,
        module_id: ModuleId,
        node_id: ast::NodeId,
        ty_name: Option<InternedSymbol>,
        parent: Option<hir::LocalDefId>,
        name: InternedSymbol,
        kind: hir::DefinitionKind,
    ) -> hir::LocalDefId {
        // TODO: check if this def already exists? may be needed for macro
        // expansion
        let local_def_id = self.next_local_def_id;
        self.next_local_def_id.increment_by(1);

        self.node_to_local_def_id_map.insert(node_id, local_def_id);

        let def_map = self.local_definition_maps.entry(module_id).or_default();

        match kind {
            // value ns
            hir::DefinitionKind::Function
            | hir::DefinitionKind::Constant
            | hir::DefinitionKind::Static => {
                def_map.values.insert(name, (kind, local_def_id.into()));
            }
            hir::DefinitionKind::AssociatedFunction => {
                def_map
                    .methods
                    .entry(ty_name.unwrap())
                    .or_default()
                    .insert(name, local_def_id);
            }
            hir::DefinitionKind::EnumVariant => {
                def_map
                    .enum_members
                    .entry(parent.unwrap())
                    .or_default()
                    .insert(name, local_def_id);
            }
            // type ns
            hir::DefinitionKind::Struct
            | hir::DefinitionKind::Enum
            | hir::DefinitionKind::Union
            | hir::DefinitionKind::Alias => {
                def_map.types.insert(name, (kind, local_def_id.into()));
            }
        }

        local_def_id
    }
}

struct DefinitionCollector<'session, 'res, 'ast> {
    resolver: &'res mut Resolver<'session>,
    module: &'ast ast::Module,
}

impl<'session, 'res, 'ast> DefinitionCollector<'session, 'res, 'ast>
where
    'session: 'res,
{
    fn new(resolver: &'res mut Resolver<'session>, module: &'ast ast::Module) -> Self {
        resolver
            .local_definition_maps
            .insert(module.id, Default::default());

        Self { resolver, module }
    }

    // fn global_scope_mut(&mut self) -> &GlobalScope {
    //     self.resolver
    //         .global_scopes
    //         .entry(self.module.id)
    //         .or_default()
    // }
    //

    fn local_definition_map(&self) -> &LocalDefinitionMap {
        self.resolver
            .local_definition_maps
            .get(&self.module.id)
            .unwrap()
    }

    fn report_duplicate_definition(&self, offending_span: Span) -> ! {
        let source_file = self
            .resolver
            .session
            .get_source_file(self.module.source_file)
            .unwrap();

        eprintln!(
            "{}: duplicate definition for global identifier `{}` (at {})",
            "error".red(),
            source_file.value_of_span(offending_span),
            source_file.format_span_position(offending_span)
        );
        source_file.highlight_span(offending_span);

        // TODO: show where the original was defined
        // TODO: recover from this error and keep moving

        std::process::exit(1);
    }

    fn report_illegal_function_name(&self, offending_span: Span) -> ! {
        let source_file = self
            .resolver
            .session
            .get_source_file(self.module.source_file)
            .unwrap();

        eprintln!(
            "{}: function name `{}` is malformed at {}",
            "error".red(),
            source_file.value_of_span(offending_span),
            source_file.format_span_position(offending_span)
        );
        source_file.highlight_span(offending_span);

        // TODO: show where the original was defined
        // TODO: recover from this error and keep moving

        std::process::exit(1);
    }
}

impl<'session, 'res, 'ast> Visitor<'ast> for DefinitionCollector<'session, 'res, 'ast> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        match &item.kind {
            ast::ItemKind::FunctionDefinition(function) => {
                match function.signature.name.segments.as_slice() {
                    // this is a normal function definition
                    [name] => {
                        if self
                            .local_definition_map()
                            .values
                            .contains_key(&name.symbol)
                        {
                            self.report_duplicate_definition(name.span)
                        }

                        let local_def_id = self.resolver.create_definition(
                            self.module.id,
                            item.id,
                            None,
                            None,
                            name.symbol,
                            hir::DefinitionKind::Function,
                        );

                        self.resolver.value_name_resolutions.insert(
                            name.id,
                            hir::Resolution::Definition(
                                hir::DefinitionKind::Function,
                                local_def_id.into(),
                            ),
                        );
                    }
                    // this is a method definition
                    [ty_name, method_name] => {
                        if self
                            .local_definition_map()
                            .methods
                            .get(&ty_name.symbol)
                            .is_some_and(|ty_scope| ty_scope.contains_key(&method_name.symbol))
                        {
                            self.report_duplicate_definition(function.signature.name.span)
                        }

                        self.resolver.create_definition(
                            self.module.id,
                            item.id,
                            Some(ty_name.symbol),
                            None,
                            method_name.symbol,
                            hir::DefinitionKind::AssociatedFunction,
                        );
                    }
                    _ => self.report_illegal_function_name(function.signature.name.span),
                }
            }
            ast::ItemKind::StructDefinition(struct_definition) => {
                if self
                    .local_definition_map()
                    .types
                    .contains_key(&struct_definition.name.symbol)
                {
                    self.report_duplicate_definition(struct_definition.name.span)
                }

                self.resolver.create_definition(
                    self.module.id,
                    item.id,
                    None,
                    None,
                    struct_definition.name.symbol,
                    hir::DefinitionKind::Struct,
                );
            }
            ast::ItemKind::EnumDefinition(enum_definition) => {
                if self
                    .local_definition_map()
                    .types
                    .contains_key(&enum_definition.name.symbol)
                {
                    self.report_duplicate_definition(enum_definition.name.span)
                }

                let parent = self.resolver.create_definition(
                    self.module.id,
                    item.id,
                    None,
                    None,
                    enum_definition.name.symbol,
                    hir::DefinitionKind::Enum,
                );

                for variant in &enum_definition.variants {
                    if self
                        .local_definition_map()
                        .enum_members
                        .get(&parent)
                        .is_some_and(|ty_scope| ty_scope.contains_key(&variant.name.symbol))
                    {
                        // TODO: nicer error for duplicate enum members
                        self.report_duplicate_definition(variant.span)
                    }

                    self.resolver.create_definition(
                        self.module.id,
                        variant.id,
                        None,
                        Some(parent),
                        variant.name.symbol,
                        hir::DefinitionKind::EnumVariant,
                    );
                }
            }
            ast::ItemKind::TypeAlias(type_alias) => {
                if self
                    .local_definition_map()
                    .types
                    .contains_key(&type_alias.name.symbol)
                {
                    self.report_duplicate_definition(type_alias.name.span)
                }

                self.resolver.create_definition(
                    self.module.id,
                    item.id,
                    None,
                    None,
                    type_alias.name.symbol,
                    hir::DefinitionKind::Alias,
                );
            }
            ast::ItemKind::Static(static_) => {
                if self
                    .local_definition_map()
                    .values
                    .contains_key(&static_.name.symbol)
                {
                    self.report_duplicate_definition(static_.name.span)
                }

                self.resolver.create_definition(
                    self.module.id,
                    item.id,
                    None,
                    None,
                    static_.name.symbol,
                    hir::DefinitionKind::Static,
                );
            }
            ast::ItemKind::Module(_) | ast::ItemKind::Import(_) => {}
        }

        visit::walk_item(self, item);
    }
}

/// Visits all the AST nodes after definitions have been collected to resolve
/// imports to their DefIds and populate the global scope with a map from names
/// to type and value definitions
pub struct EarlyResolveVisitor<'session, 'res, 'ast> {
    resolver: &'res mut Resolver<'session>,
    module: &'ast ast::Module,
}

impl<'session, 'res, 'ast> EarlyResolveVisitor<'session, 'res, 'ast>
where
    'session: 'res,
{
    pub fn new(resolver: &'res mut Resolver<'session>, module: &'ast ast::Module) -> Self {
        let scope = resolver.global_scopes.entry(module.id).or_default();

        for (name, (def_kind, local_def_id)) in &resolver.local_definition_maps[&module.id].types {
            scope.type_scope.insert(
                *name,
                hir::Resolution::Definition(*def_kind, (*local_def_id).into()),
            );
        }

        for (name, (def_kind, local_def_id)) in &resolver.local_definition_maps[&module.id].values {
            scope.value_scope.insert(
                *name,
                hir::Resolution::Definition(*def_kind, (*local_def_id).into()),
            );
        }

        Self { module, resolver }
    }

    fn global_scope_mut(&mut self) -> &mut GlobalScope {
        self.resolver
            .global_scopes
            .get_mut(&self.module.id)
            .unwrap()
    }

    pub fn lookup_crate_module_from_absolute_path(
        &self,
        path: &[InternedSymbol],
    ) -> Option<ModuleId> {
        assert!(!path.is_empty());

        let mut qualifier = &path[..];
        let mut current_id = ModuleId::CRATE_ROOT;

        while !qualifier.is_empty() {
            let current_node = &self.resolver.module_map[current_id];

            let name: Rc<str> = qualifier[0].value().into();

            let next = current_node.children.get(&name)?;

            current_id = *next;
            qualifier = &qualifier[1..];
        }

        Some(current_id)
    }

    fn report_unresolved(&self, offending_span: Span) -> ! {
        let source_file = self
            .resolver
            .session
            .get_source_file(self.module.source_file)
            .unwrap();

        eprintln!(
            "{}: failed to resolve import `{}` {}",
            "error".red(),
            source_file.value_of_span(offending_span),
            format!("(at {})", source_file.format_span_position(offending_span)).white()
        );
        source_file.highlight_span(offending_span);

        // TODO: recover from this error and keep moving

        std::process::exit(1);
    }
}

impl<'session, 'res, 'ast> Visitor<'ast> for EarlyResolveVisitor<'session, 'res, 'ast> {
    fn visit_import(&mut self, import: &'ast ast::Import) {
        if import.name.first().symbol == InternedSymbol::new("crate") {
            // lookup the module in the crate

            let segments = &import.name.segments[1..]
                .iter()
                .map(|i| i.symbol)
                .collect::<Vec<_>>();

            let Some((name, module_path)) = segments.split_last() else {
                self.report_unresolved(import.name.span)
            };

            let Some(module) = self.lookup_crate_module_from_absolute_path(module_path) else {
                // FIXME: create a better error message for this (resolve
                // intermediate module paths to see where it cuts off)
                self.report_unresolved(import.name.span)
            };

            // lookup the definition in the module using the module id

            let mut resolved = false;

            let type_res = self.resolver.local_definition_maps[&module]
                .types
                .get(name)
                .cloned();

            if let Some((kind, local_def_id)) = type_res {
                self.global_scope_mut().type_scope.insert(
                    *name,
                    hir::Resolution::Definition(kind, local_def_id.into()),
                );
                resolved = true;
            }

            let value_res = self.resolver.local_definition_maps[&module]
                .values
                .get(name)
                .cloned();

            if let Some((kind, local_def_id)) = value_res {
                self.global_scope_mut().value_scope.insert(
                    *name,
                    hir::Resolution::Definition(kind, local_def_id.into()),
                );
                resolved = true;
            }

            if !resolved {
                self.report_unresolved(import.name.span)
            }
        } else {
            todo!("resolve relative and external imports (use session information)")
        }

        // TODO
    }
}

/// Visits all the AST nodes after imports are resolved and all definitions are
/// collected to resolve references to types and values
pub struct LateResolveVisitor<'session, 'res, 'ast> {
    resolver: &'res mut Resolver<'session>,
    module: &'ast ast::Module,

    // Used to keep track of the lexical context
    value_scope_stack: ScopeStack<hir::Resolution<NodeId>>,
    type_scope_stack: ScopeStack<hir::Resolution<NodeId>>,
}

impl<'session, 'res, 'ast> LateResolveVisitor<'session, 'res, 'ast>
where
    'session: 'res,
{
    pub fn new(resolver: &'res mut Resolver<'session>, module: &'ast ast::Module) -> Self {
        Self {
            module,
            resolver,
            value_scope_stack: ScopeStack::new(),
            type_scope_stack: ScopeStack::new(),
        }
    }

    fn local_definition_map(&self) -> &LocalDefinitionMap {
        &self.resolver.local_definition_maps[&self.module.id]
    }

    fn global_scope(&self) -> &GlobalScope {
        &self.resolver.global_scopes[&self.module.id]
    }

    /// Resolves a name within the current lexical scope
    fn resolve_symbol(
        &self,
        name: InternedSymbol,
        namespace: Namespace,
    ) -> Option<hir::Resolution<NodeId>> {
        if namespace == Namespace::Type
            && let Some(p) = self.resolver.builtin_primitives.get(&name)
        {
            return Some(hir::Resolution::Primitive(*p));
        }

        if namespace == Namespace::Value && self.resolver.builtin_functions.contains(&name) {
            return Some(hir::Resolution::IntrinsicFunction(name));
        }

        let (scope_stack, global_scope) = match namespace {
            Namespace::Value => (
                &self.value_scope_stack,
                &self.resolver.global_scopes[&self.module.id].value_scope,
            ),
            Namespace::Type => (
                &self.type_scope_stack,
                &self.resolver.global_scopes[&self.module.id].type_scope,
            ),
        };

        scope_stack
            .get_binding(name)
            .or_else(|| global_scope.get(&name))
            .copied()
    }

    fn report_duplicate_binding(&self, offending_span: Span) -> ! {
        let source_file = self
            .resolver
            .session
            .get_source_file(self.module.source_file)
            .unwrap();

        eprintln!(
            "{}: duplicate definition for identifier `{}` (at {})",
            "error".red(),
            source_file.value_of_span(offending_span),
            source_file.format_span_position(offending_span)
        );
        source_file.highlight_span(offending_span);

        // TODO: show where the original binding was defined
        // TODO: recover from this error and keep moving

        std::process::exit(1);
    }

    #[track_caller]
    fn report_unresolved(&self, offending_span: Span) -> ! {
        #[cfg(feature = "error-backtrace")]
        {
            eprintln!(
                "{}: {}",
                "backtrace".cyan().bold(),
                std::panic::Location::caller()
            );

            let bt = std::backtrace::Backtrace::capture();
            if bt.status() == std::backtrace::BacktraceStatus::Captured {
                eprintln!("{bt}");
            }
        }

        let source_file = self
            .resolver
            .session
            .get_source_file(self.module.source_file)
            .unwrap();

        eprintln!(
            "{}: unresolved name for identifier `{}` {}",
            "error".red(),
            source_file.value_of_span(offending_span),
            format!("(at {})", source_file.format_span_position(offending_span)).white()
        );
        source_file.highlight_span(offending_span);

        // TODO: recover from this error and keep moving

        std::process::exit(1);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Namespace {
    Value,
    Type,
}

impl<'session, 'res, 'ast> Visitor<'ast> for LateResolveVisitor<'session, 'res, 'ast> {
    /// Walk the function with a fresh scope to bind parameters in
    fn visit_function_definition(&mut self, function: &'ast FunctionDefinition) {
        assert!(self.value_scope_stack.inner.is_empty());

        match function.signature.name.segments.as_slice() {
            [ty_name, method_name] => {
                let Some(ty_resolution) = self.resolve_symbol(ty_name.symbol, Namespace::Type)
                else {
                    self.report_unresolved(ty_name.span)
                };

                self.resolver
                    .type_name_resolutions
                    .insert(ty_name.id, ty_resolution);

                let local_def_id = *self
                    .local_definition_map()
                    .methods
                    .get(&ty_name.symbol)
                    .and_then(|ty_scope| ty_scope.get(&method_name.symbol))
                    .expect("missing def id for method");

                let method_resolution =
                    hir::Resolution::Definition(hir::DefinitionKind::Function, local_def_id.into());

                self.resolver
                    .value_name_resolutions
                    .insert(method_name.id, method_resolution);
            }
            _ => {}
        }

        self.value_scope_stack.push_shallow_scope();
        visit::walk_function_definition(self, function);
        self.value_scope_stack.pop_shallow_scope();
    }

    /// Binds function parameter names into the current function's scope
    fn visit_function_parameter(&mut self, parameter: &'ast FunctionParameter) {
        // Check that name is not already bound in the current scope
        if self
            .value_scope_stack
            .get_shallow_binding(parameter.name.symbol)
            .is_some()
        {
            self.report_duplicate_binding(parameter.name.span);
        }

        // Add the binding for the parameter name
        self.value_scope_stack
            .add_shallow_binding(parameter.name.symbol, hir::Resolution::Local(parameter.id));

        // Visit names and types
        visit::walk_function_parameter(self, parameter);
    }

    fn visit_static(&mut self, static_: &'ast ast::Static) {
        assert!(self.value_scope_stack.inner.is_empty());

        self.value_scope_stack.push_shallow_scope();
        visit::walk_static(self, static_);
        self.value_scope_stack.pop_shallow_scope();
    }

    /// Creates a new scope and walks the block
    fn visit_block(&mut self, block: &'ast Block) {
        self.value_scope_stack.push_shallow_scope();
        visit::walk_block(self, block);
        self.value_scope_stack.pop_shallow_scope();
    }

    /// Walks the local's type and expression before binding the name into the
    /// current lexical scope
    fn visit_local(&mut self, local: &'ast Local) {
        visit::walk_local(self, local);

        // FIXME: allow shadowing? would just require removing this check:

        // Check that name is not already bound in the current scope (allowed to
        // be bound in higher scopes and rebound in the current scope)
        if self
            .value_scope_stack
            .get_shallow_binding(local.name.symbol)
            .is_some()
        {
            self.report_duplicate_binding(local.name.span);
        }

        self.value_scope_stack
            .add_shallow_binding(local.name.symbol, hir::Resolution::Local(local.id));
    }

    fn visit_qualified_identifier(
        &mut self,
        qualified_ident: &'ast ast::QualifiedIdentifier,
        namespace: Option<Namespace>,
    ) {
        // we dont care about qpaths in ambiguous places like imports bc those
        // have already beem resolved
        let Some(namespace) = namespace else {
            return;
        };

        match namespace {
            Namespace::Value => {
                // There are 2 possibilities here:
                //   1) The ident has no qualifier and it refers to a local, function
                //      parameter, or local/imported definition
                //   2) The ident has a qualifier so we should start at the first segment
                //      and resolve from there

                // Case 1
                if let [ident] = qualified_ident.segments.as_slice() {
                    // Resolve from the global scope
                    let Some(resolution) = self.resolve_symbol(ident.symbol, Namespace::Value)
                    else {
                        self.report_unresolved(ident.span);
                    };

                    self.resolver
                        .value_name_resolutions
                        .insert(qualified_ident.id, resolution);
                    self.resolver
                        .value_name_resolutions
                        .insert(ident.id, resolution);
                }
                // Case 2
                else if let [first_ident, second_ident] = qualified_ident.segments.as_slice() {
                    let Some(first_resolution) =
                        self.resolve_symbol(first_ident.symbol, Namespace::Type)
                    else {
                        self.report_unresolved(first_ident.span);
                    };

                    self.resolver
                        .type_name_resolutions
                        .insert(first_ident.id, first_resolution);

                    // FIXME: should this be moved into the type checker to handle type aliases?

                    let res = if let Some(method_def_id) = self
                        .local_definition_map()
                        .methods
                        .get(&first_ident.symbol)
                        .and_then(|ty_scope| ty_scope.get(&second_ident.symbol))
                        .copied()
                    {
                        hir::Resolution::Definition(
                            hir::DefinitionKind::AssociatedFunction,
                            method_def_id.into(),
                        )
                    } else if let hir::Resolution::Definition(hir::DefinitionKind::Enum, def_id) =
                        first_resolution
                        && let Some(variant_local_def_id) = self
                            .local_definition_map()
                            .enum_members
                            .get(&def_id.index)
                            .and_then(|ty_scope| ty_scope.get(&second_ident.symbol))
                            .copied()
                    {
                        assert_eq!(
                            def_id.krate,
                            hir::CrateNum::LOCAL_CRATE,
                            "todo: external crates"
                        );

                        hir::Resolution::Definition(
                            hir::DefinitionKind::EnumVariant,
                            variant_local_def_id.into(),
                        )
                    } else {
                        self.report_unresolved(second_ident.span);
                    };

                    self.resolver
                        .value_name_resolutions
                        .insert(second_ident.id, res);
                    self.resolver
                        .value_name_resolutions
                        .insert(qualified_ident.id, res);
                } else {
                    todo!("resolve long paths")
                }
            }
            Namespace::Type => {
                // There are 2 possibilities here:
                //   1) The identifier only has one segment and must be a
                //      primitive or local/imported custom type (alias, struct, enum,
                //      etc.). This can be resolved by checking if it's a primitive
                //      and then checking the global scope if that fails
                //  2) The identifier has more than one segment and we must start
                //      from the first and resolve from there

                // Case 1
                if let [ident] = qualified_ident.segments.as_slice() {
                    // Resolve from the global scope
                    let Some(resolution) = self.resolve_symbol(ident.symbol, Namespace::Type)
                    else {
                        self.report_unresolved(ident.span);
                    };

                    self.resolver
                        .type_name_resolutions
                        .insert(qualified_ident.id, resolution);
                    self.resolver
                        .type_name_resolutions
                        .insert(ident.id, resolution);
                }
                // Case 2
                else {
                    todo!("Resolve type identifier by traversing qualified identifier segments")
                }
            }
        }

        visit::walk_qualified_identifier(self, qualified_ident);
    }
}

/// A data structure to assist in traversing AST scopes within a specific
/// namespace (values or types)
#[derive(Debug)]
struct ScopeStack<R> {
    inner: VecDeque<BTreeMap<InternedSymbol, R>>,
}

impl<R> ScopeStack<R> {
    fn new() -> Self {
        Self {
            inner: VecDeque::new(),
        }
    }

    /// Creates a new block or function scope
    fn push_shallow_scope(&mut self) {
        self.inner.push_back(BTreeMap::new());
    }

    /// Destroys the current block or function scope
    fn pop_shallow_scope(&mut self) {
        assert!(
            !self.inner.is_empty(),
            "Attempted to pop a shallow scope from the global context"
        );

        self.inner.pop_back();
    }

    /// Looks for a binding only within the current (most nested) scope
    fn get_shallow_binding(&self, symbol: InternedSymbol) -> Option<&R> {
        assert!(
            !self.inner.is_empty(),
            "Tried to get a shallow binding from the global context"
        );

        let shallow_scope = self.inner.back().unwrap();

        shallow_scope.get(&symbol)
    }

    /// Adds a binding only within the current (most nested) scope
    fn add_shallow_binding(&mut self, symbol: InternedSymbol, name_resolution: R) {
        assert!(
            !self.inner.is_empty(),
            "Tried to add a shallow binding in the global context"
        );

        let shallow_scope = self.inner.back_mut().unwrap();

        shallow_scope.insert(symbol, name_resolution);
    }

    /// Traverses the scope stack from back to front looking for bindings
    fn get_binding(&self, symbol: InternedSymbol) -> Option<&R> {
        for scope in self.inner.iter().rev() {
            if let Some(binding) = scope.get(&symbol) {
                return Some(binding);
            }
        }

        None
    }
}
