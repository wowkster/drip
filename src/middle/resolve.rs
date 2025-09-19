use std::collections::{BTreeMap, BTreeSet, VecDeque};

use colored::Colorize;

use super::{hir, primitive::PrimitiveKind};
use crate::{
    frontend::{
        ast::{
            self, Block, FunctionDefinition, FunctionParameter, Local, Module, NodeId,
            visit::{self, Visitor},
        },
        intern::InternedSymbol,
        lexer::Span,
    },
    index::Index,
};

/// AST Module name resolver
///
/// Traverses the AST for a module and creates a map from type and value names
/// to their definitions within the source code.
#[derive(Debug)]
pub struct Resolver {
    /// A list of built-in function names which we allow resolutions for
    builtin_primitives: BTreeMap<InternedSymbol, PrimitiveKind>,

    /// A list of built-in function names which we allow resolutions for
    builtin_functions: BTreeSet<InternedSymbol>,

    // Used to keep track of the definitions that exist within the current
    next_def_id: hir::LocalDefId,
    // Maps the IDs of AST owners to the def IDs we've assign to them
    node_to_def_id_map: BTreeMap<NodeId, hir::LocalDefId>,

    // Maps names of definitions in the global scope to their resolutions
    // TODO: scope these to the modules they are defined in with the module
    // graph
    global_value_scope: BTreeMap<InternedSymbol, hir::Resolution<NodeId>>,
    global_type_scope: BTreeMap<InternedSymbol, hir::Resolution<NodeId>>,

    /// Maps methods on types to their definitions
    global_method_scopes: BTreeMap<InternedSymbol, BTreeMap<InternedSymbol, hir::LocalDefId>>,

    // Maps name references to definitions
    value_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
    type_name_resolutions: BTreeMap<NodeId, hir::Resolution<NodeId>>,
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

impl<'ast> Resolver {
    pub fn new() -> Self {
        Self {
            builtin_primitives: BTreeMap::from_iter(
                PrimitiveKind::ALL
                    .iter()
                    .map(|p| (InternedSymbol::new(&p.to_string()), *p)),
            ),
            builtin_functions: BTreeSet::from([
                InternedSymbol::new("print"),
                InternedSymbol::new("exit"),
            ]),
            next_def_id: hir::LocalDefId::new(0), // TODO: should this be reserved for the module itself?
            node_to_def_id_map: BTreeMap::new(),
            global_value_scope: BTreeMap::new(),
            global_type_scope: BTreeMap::new(),
            global_method_scopes: BTreeMap::new(),
            value_name_resolutions: BTreeMap::new(),
            type_name_resolutions: BTreeMap::new(),
        }
    }

    /// Resolves all names within a module in 2 steps.
    ///
    /// The first step resolves imports and locates all the definitions of
    /// custom types and functions. These imports and custom types are then
    /// bound in the global value and type scopes
    ///
    /// The second step traverses the AST and makes sure any references to types
    /// or values are defined in this module's scope or are imported. It also
    /// keeps track of function parameters and local variables to make sure all
    /// identifiers are valid. Field and method accesses are not checked at this
    /// stage and are resolved during module type checking.
    pub fn resolve_module(&mut self, module: &'ast Module) {
        /* Step 1 */

        // TODO: resolve imports and add to import maps

        /* Step 2 */

        // Collect names of definitions
        let mut def_collector = DefinitionCollector::new(self, module);
        visit::walk_module(&mut def_collector, module);

        // Resolve name references
        let mut late_resolver = LateResolveVisitor::new(self, module);
        visit::walk_module(&mut late_resolver, module);

        // TODO: warn about unused imports
    }

    /// Returns the useful output of the resolver after successfully completing
    /// resolutions and macro expansions in the requested modules
    pub fn into_outputs(self) -> ResolutionMap {
        ResolutionMap {
            node_to_def_id_map: self.node_to_def_id_map,
            value_name_resolutions: self.value_name_resolutions,
            type_name_resolutions: self.type_name_resolutions,
        }
    }

    /// Records a definition in several maps and adds the name to the
    /// appropriate global scope
    pub fn create_definition(
        &mut self,
        node_id: ast::NodeId,
        name: InternedSymbol,
        kind: hir::DefinitionKind,
    ) -> hir::LocalDefId {
        // TODO: check if this def already exists? may be needed for macro
        // expansion
        let owner_id = self.next_def_id;
        self.next_def_id.increment_by(1);

        self.node_to_def_id_map.insert(node_id, owner_id);

        match kind {
            hir::DefinitionKind::Function
            | hir::DefinitionKind::Constant
            | hir::DefinitionKind::Static => {
                self.global_value_scope
                    .insert(name, hir::Resolution::Definition(kind, owner_id));
            }
            hir::DefinitionKind::Struct
            | hir::DefinitionKind::Enum
            | hir::DefinitionKind::Union
            | hir::DefinitionKind::Alias => {
                self.global_type_scope
                    .insert(name, hir::Resolution::Definition(kind, owner_id));
            }
        }

        owner_id
    }

    pub fn create_method_definition(
        &mut self,
        node_id: ast::NodeId,
        ty_name: InternedSymbol,
        method_name: InternedSymbol,
    ) {
        let owner_id = self.next_def_id;
        self.next_def_id.increment_by(1);

        self.node_to_def_id_map.insert(node_id, owner_id);

        self.global_method_scopes
            .entry(ty_name)
            .or_default()
            .insert(method_name, owner_id);
    }
}

struct DefinitionCollector<'res, 'ast> {
    resolver: &'res mut Resolver,
    module: &'ast ast::Module<'ast>,
}

impl<'res, 'ast> DefinitionCollector<'res, 'ast> {
    fn new(resolver: &'res mut Resolver, module: &'ast ast::Module<'ast>) -> Self {
        Self { resolver, module }
    }

    fn report_duplicate_definition(&self, offending_span: Span) -> ! {
        eprintln!(
            "{}: duplicate definition for global identifier `{}` (at {})",
            "error".red(),
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.format_span_position(offending_span)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: show where the original was defined
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }

    fn report_illegal_function_name(&self, offending_span: Span) -> ! {
        eprintln!(
            "{}: function name `{}` is malformed at {}",
            "error".red(),
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.format_span_position(offending_span)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: show where the original was defined
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }
}

impl<'res, 'ast> Visitor<'ast> for DefinitionCollector<'res, 'ast> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        match &item.kind {
            ast::ItemKind::FunctionDefinition(function) => {
                match function.signature.name.segments.as_slice() {
                    // this is a normal function definition
                    [name] => {
                        if self.resolver.global_value_scope.contains_key(&name.symbol) {
                            self.report_duplicate_definition(name.span)
                        }

                        let def_id = self.resolver.create_definition(
                            item.id,
                            name.symbol,
                            hir::DefinitionKind::Function,
                        );

                        self.resolver.value_name_resolutions.insert(
                            name.id,
                            hir::Resolution::Definition(hir::DefinitionKind::Function, def_id),
                        );
                    }
                    // this is a method definition
                    [ty_name, method_name] => {
                        if self
                            .resolver
                            .global_method_scopes
                            .get(&ty_name.symbol)
                            .is_some_and(|ty_scope| ty_scope.contains_key(&method_name.symbol))
                        {
                            self.report_duplicate_definition(function.signature.name.span)
                        }

                        self.resolver.create_method_definition(
                            item.id,
                            ty_name.symbol,
                            method_name.symbol,
                        );
                    }
                    _ => self.report_illegal_function_name(function.signature.name.span),
                }
            }
            ast::ItemKind::StructDefinition(struct_definition) => {
                if self
                    .resolver
                    .global_type_scope
                    .contains_key(&struct_definition.name.symbol)
                {
                    self.report_duplicate_definition(struct_definition.name.span)
                }

                self.resolver.create_definition(
                    item.id,
                    struct_definition.name.symbol,
                    hir::DefinitionKind::Struct,
                );
            }
            ast::ItemKind::TypeAlias(type_alias) => {
                if self
                    .resolver
                    .global_type_scope
                    .contains_key(&type_alias.name.symbol)
                {
                    self.report_duplicate_definition(type_alias.name.span)
                }

                self.resolver.create_definition(
                    item.id,
                    type_alias.name.symbol,
                    hir::DefinitionKind::Alias,
                );
            }
            ast::ItemKind::Static(static_) => {
                if self
                    .resolver
                    .global_value_scope
                    .contains_key(&static_.name.symbol)
                {
                    self.report_duplicate_definition(static_.name.span)
                }

                self.resolver.create_definition(
                    item.id,
                    static_.name.symbol,
                    hir::DefinitionKind::Static,
                );
            }
        }

        visit::walk_item(self, item);
    }
}

/// Visits all the AST nodes after macros have been expanded to resolve
/// references to types and values
pub struct LateResolveVisitor<'res, 'ast> {
    resolver: &'res mut Resolver,
    module: &'ast ast::Module<'ast>,

    // Used to keep track of the lexical context
    value_scope_stack: ScopeStack<hir::Resolution<NodeId>>,
    type_scope_stack: ScopeStack<hir::Resolution<NodeId>>,
}

impl<'res, 'ast> LateResolveVisitor<'res, 'ast> {
    pub fn new(resolver: &'res mut Resolver, module: &'ast ast::Module<'ast>) -> Self {
        Self {
            resolver,
            module,
            value_scope_stack: ScopeStack::new(),
            type_scope_stack: ScopeStack::new(),
        }
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
            Namespace::Value => (&self.value_scope_stack, &self.resolver.global_value_scope),
            Namespace::Type => (&self.type_scope_stack, &self.resolver.global_type_scope),
        };

        scope_stack
            .get_binding(name)
            .or_else(|| global_scope.get(&name))
            .copied()
    }

    fn report_duplicate_binding(&self, offending_span: Span) -> ! {
        eprintln!(
            "{}: duplicate definition for identifier `{}` (at {})",
            "error".red(),
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.format_span_position(offending_span)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: show where the original binding was defined
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }

    fn report_unresolved(&self, offending_span: Span) -> ! {
        eprintln!(
            "{}: unresolved name for identifier `{}` {}",
            "error".red(),
            self.module.source_file.value_of_span(offending_span),
            format!(
                "(at {})",
                self.module.source_file.format_span_position(offending_span)
            )
            .white()
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Namespace {
    Value,
    Type,
}

impl<'res, 'ast> Visitor<'ast> for LateResolveVisitor<'res, 'ast> {
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

                let def_id = self
                    .resolver
                    .global_method_scopes
                    .get(&ty_name.symbol)
                    .and_then(|ty_scope| ty_scope.get(&method_name.symbol))
                    .expect("missing def id for method");

                let method_resolution =
                    hir::Resolution::Definition(hir::DefinitionKind::Function, *def_id);

                self.resolver
                    .value_name_resolutions
                    .insert(ty_name.id, method_resolution);
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
        namespace: Namespace,
    ) {
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

                    let Some(second_resolution) = self
                        .resolver
                        .global_method_scopes
                        .get(&first_ident.symbol)
                        .and_then(|ty_scope| ty_scope.get(&second_ident.symbol))
                    else {
                        self.report_unresolved(second_ident.span);
                    };

                    let res = hir::Resolution::Definition(
                        hir::DefinitionKind::Function,
                        *second_resolution,
                    );

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
