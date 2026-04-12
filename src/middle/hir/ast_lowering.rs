//! This module contains all the code related to lowering an AST into HIR
//!
//! This involves indexing the AST and resolving all names within types and
//! function bodies

use std::{collections::BTreeMap, panic::Location, rc::Rc};

use colored::Colorize;

use crate::{
    frontend::{ast, lexer::Span},
    index::{Index, IndexVec},
    middle::{
        hir::{self, HirId, visit::Visitor},
        primitive::UIntKind,
        resolve::{Namespace, ResolutionMap, Resolver},
    },
};

pub struct ItemLoweringContext<'a, 'ast> {
    // Global refs
    module: &'ast ast::Module<'ast>,
    resolver: &'a ResolutionMap,

    // Context specific to this owner
    owner_id: hir::LocalDefId,
    next_local_id: hir::ItemLocalId,
    body: Option<Rc<hir::Body>>,
    /// Maps IDs of local (let) bindings to their allocated hir item local ids
    local_id_map: BTreeMap<ast::NodeId, hir::ItemLocalId>,

    // Definitions collected so far in lowering (used for adding non owner node
    // definitions to the map)
    definitions: &'a mut BTreeMap<hir::LocalDefId, hir::MaybeOwner>,
}

impl<'a, 'ast> ItemLoweringContext<'a, 'ast> {
    fn new(
        module: &'ast ast::Module<'ast>,
        resolver: &'a ResolutionMap,
        owner_id: hir::LocalDefId,
        definitions: &'a mut BTreeMap<hir::LocalDefId, hir::MaybeOwner>,
    ) -> Self {
        Self {
            module,
            resolver,
            owner_id,
            next_local_id: hir::ItemLocalId::new(1),
            body: None,
            local_id_map: BTreeMap::new(),
            definitions,
        }
    }

    fn next_id(&mut self) -> hir::HirId {
        assert_ne!(self.next_local_id, hir::ItemLocalId::ZERO);
        let id = hir::HirId::new(self.owner_id, self.next_local_id);
        self.next_local_id.increment_by(1);
        id
    }

    fn set_body(&mut self, body: hir::Body) -> hir::BodyId {
        assert!(self.body.is_none(), "tried to set body more than once");

        let body_id = body.id();
        self.body = Some(Rc::new(body));
        body_id
    }

    fn lower_item(&mut self, item: &'ast ast::Item) -> Rc<hir::Item> {
        let kind = match &item.kind {
            ast::ItemKind::FunctionDefinition(f) => {
                let mut name_segments = Vec::new();

                match f.signature.name.segments.as_slice() {
                    [identifier] => {
                        let resolution = hir::Resolution::Definition(
                            hir::DefinitionKind::Function,
                            self.owner_id,
                        );

                        name_segments.push(Rc::new(hir::PathSegment {
                            hir_id: self.next_id(),
                            span: identifier.span,
                            identifier: self.lower_ident(identifier),
                            resolution: self.lower_resolution(&resolution),
                        }));
                    }
                    [ty_name, method_name] => {
                        let ty_resolution = self
                            .resolver
                            .type_name_resolutions
                            .get(&ty_name.id)
                            .expect("method type name had no resolution");

                        name_segments.push(Rc::new(hir::PathSegment {
                            hir_id: self.next_id(),
                            span: ty_name.span,
                            identifier: self.lower_ident(ty_name),
                            resolution: self.lower_resolution(ty_resolution),
                        }));

                        let method_resolution = hir::Resolution::Definition(
                            hir::DefinitionKind::Function,
                            self.owner_id,
                        );

                        name_segments.push(Rc::new(hir::PathSegment {
                            hir_id: self.next_id(),
                            span: ty_name.span,
                            identifier: self.lower_ident(method_name),
                            resolution: self.lower_resolution(&method_resolution),
                        }));
                    }
                    _ => unreachable!(),
                }

                let name = hir::Path {
                    segments: name_segments.into(),
                    span: f.signature.name.span,
                };
                let signature = self.lower_function_signature(&f.signature);

                // NOTE: must lower parameters first to bind names
                let params = self.lower_function_parameters(&f.signature.parameters);
                let block = self.lower_block(&f.body);

                let body = self.set_body(hir::Body { params, block });

                hir::ItemKind::Function {
                    name,
                    signature,
                    body,
                }
            }
            ast::ItemKind::StructDefinition(struct_definition) => {
                let name = self.lower_ident(&struct_definition.name);
                let fields = self.lower_struct_fields(&struct_definition.fields);

                hir::ItemKind::Struct { name, fields }
            }
            ast::ItemKind::EnumDefinition(enum_definition) => {
                let name = self.lower_ident(&enum_definition.name);
                let variants = self.lower_enum_variants(&enum_definition.variants);

                hir::ItemKind::Enum { name, variants }
            }
            ast::ItemKind::TypeAlias(type_alias) => {
                let name = self.lower_ident(&type_alias.name);
                let ty = self.lower_type(&type_alias.ty);

                hir::ItemKind::TypeAlias { name, ty }
            }
            ast::ItemKind::Static(static_) => {
                let name = self.lower_ident(&static_.name);
                let ty = self.lower_type(&static_.ty);
                let initializer = self.lower_expression(&static_.initializer);

                hir::ItemKind::Static {
                    is_mutable: static_.is_mutable,
                    name,
                    ty,
                    initializer,
                }
            }
        };

        Rc::new(hir::Item {
            owner_id: self.owner_id,
            kind,
            span: item.span,
        })
    }

    fn lower_function_signature(
        &mut self,
        signature: &'ast ast::FunctionSignature,
    ) -> hir::FunctionSignature {
        hir::FunctionSignature {
            self_parameter: signature.parameters.self_parameter.map(|sp| match sp {
                ast::SelfParameter::Owned => hir::SelfParameter::Owned,
                ast::SelfParameter::Pointer { is_mutable } => {
                    hir::SelfParameter::Pointer { is_mutable }
                }
            }),
            parameters: self.lower_function_parameters_as_types(&signature.parameters),
            variadic_type: None, // TODO
            return_type: signature.return_type.as_ref().map(|ty| self.lower_type(ty)),
            span: signature.span,
        }
    }

    fn lower_ident(&mut self, ident: &'ast ast::Identifier) -> hir::Identifier {
        hir::Identifier {
            symbol: ident.symbol,
            span: ident.span,
        }
    }

    fn lower_function_parameters_as_types(
        &mut self,
        params: &'ast ast::FunctionParameterList,
    ) -> Rc<[Rc<hir::Type>]> {
        params
            .parameters
            .iter()
            .map(|param| self.lower_type(&param.ty))
            .collect()
    }

    fn lower_type(&mut self, ty: &'ast ast::Type) -> Rc<hir::Type> {
        let kind = match &ty.kind {
            ast::TypeKind::Unit => hir::TypeKind::Unit,
            ast::TypeKind::QualifiedIdentifier(qualified_identifier) => {
                // There are 2 possibilities here:
                //   1) The identifier only has one segment and must be a
                //      primitive or local/imported custom type (alias, struct, enum,
                //      etc.). This can be resolved by checking if it's a primitive
                //      and then checking the global scope if that fails
                //  2) The identifier has more than one segment and we must start
                //      from the first and resolve from there

                let mut segments = Vec::new();

                if let [identifier] = qualified_identifier.segments.as_slice() {
                    let resolution = self
                        .resolver
                        .type_name_resolutions
                        .get(&identifier.id)
                        .unwrap_or_else(|| {
                            panic!("type identifier had no resolution: {identifier:#?}")
                        });

                    segments.push(Rc::new(hir::PathSegment {
                        hir_id: self.next_id(),
                        span: identifier.span,
                        identifier: self.lower_ident(identifier),
                        resolution: self.lower_resolution(resolution),
                    }));
                } else {
                    todo!("Resolve identifiers with multiple segments")
                }

                hir::TypeKind::Path(hir::Path {
                    segments: segments.into(),
                    span: qualified_identifier.span,
                })
            }
            ast::TypeKind::Pointer(ty) => hir::TypeKind::Pointer(self.lower_type(ty)),
            ast::TypeKind::Slice(ty) => hir::TypeKind::Slice(self.lower_type(ty)),
            ast::TypeKind::Array { ty, length } => {
                let ty = self.lower_type(ty);
                let length = match length.kind {
                    ast::LiteralKind::Integer => length
                        .symbol
                        .value()
                        .parse()
                        // TODO: handle errors here
                        .expect("Failed to parse array length"),
                    _ => {
                        self.report_error(length.span, "Array length must be an integer literal");
                    }
                };

                hir::TypeKind::Array { ty, length }
            }
            ast::TypeKind::Tuple(types) => {
                if let [single] = types.as_ref() {
                    return self.lower_type(single);
                } else {
                    hir::TypeKind::Tuple(types.iter().map(|ty| self.lower_type(ty)).collect())
                }
            }
            ast::TypeKind::Any => hir::TypeKind::Any,
        };

        Rc::new(hir::Type {
            hir_id: self.next_id(),
            kind,
            span: ty.span,
        })
    }

    fn lower_resolution(&mut self, resolution: &hir::Resolution<ast::NodeId>) -> hir::Resolution {
        match resolution {
            hir::Resolution::Definition(definition_kind, local_def_id) => {
                hir::Resolution::Definition(*definition_kind, *local_def_id)
            }
            hir::Resolution::Local(node_id) => hir::Resolution::Local(
                *self
                    .local_id_map
                    .get(node_id)
                    .expect("node id for local (let) binding was not found"),
            ),
            hir::Resolution::IntrinsicFunction(name) => hir::Resolution::IntrinsicFunction(*name),
            hir::Resolution::Primitive(kind) => hir::Resolution::Primitive(*kind),
        }
    }

    /// Lowers the function parameter and binds all the names into the current
    /// value resolution scope
    fn lower_function_parameters(
        &mut self,
        params: &'ast ast::FunctionParameterList,
    ) -> Rc<[Rc<hir::FunctionParameter>]> {
        params
            .parameters
            .iter()
            .map(|p| {
                let param = hir::FunctionParameter {
                    hir_id: self.next_id(),
                    name: self.lower_ident(&p.name),
                    ty_span: p.ty.span,
                    span: p.span,
                };

                self.local_id_map.insert(p.id, param.hir_id.local_id);

                param
            })
            .map(Rc::new)
            .collect()
    }

    fn lower_struct_fields(
        &mut self,
        fields: &'ast [ast::StructField],
    ) -> Rc<[Rc<hir::StructField>]> {
        fields
            .iter()
            .map(|f| {
                let field = hir::StructField {
                    hir_id: self.next_id(),
                    name: self.lower_ident(&f.name),
                    ty: self.lower_type(&f.ty),
                    span: f.span,
                };

                self.local_id_map.insert(f.id, field.hir_id.local_id);

                field
            })
            .map(Rc::new)
            .collect()
    }

    fn lower_enum_variants(
        &mut self,
        variants: &'ast [ast::EnumVariant],
    ) -> Rc<[Rc<hir::EnumVariant>]> {
        variants
            .iter()
            .map(|v| {
                let local_def_id = self.resolver.node_to_def_id_map[&v.id];

                let variant = hir::EnumVariant {
                    def_id: local_def_id,
                    hir_id: self.next_id(),
                    name: self.lower_ident(&v.name),
                    span: v.span,
                };

                self.local_id_map.insert(v.id, variant.hir_id.local_id);
                self.definitions
                    .insert(local_def_id, hir::MaybeOwner::NonOwner(variant.hir_id));

                variant
            })
            .map(Rc::new)
            .collect()
    }

    fn lower_block(&mut self, block: &'ast ast::Block) -> Rc<hir::Block> {
        let (statements, expr) = self.lower_statements(&block.statements);

        Rc::new(hir::Block {
            hir_id: self.next_id(),
            statements,
            expression: expr,
            is_const: false, // TODO: constexpr
            span: block.span,
        })
    }

    /// Lowers the provided statement unless it is an empty statement, in which
    /// case None is returned (we discard these during lowering)
    fn lower_statements(
        &mut self,
        statements: &'ast [ast::Statement],
    ) -> (Rc<[Rc<hir::Statement>]>, Option<Rc<hir::Expression>>) {
        let len = statements.len();

        let mut result = Vec::new();
        let mut expr = None;

        for (i, statement) in statements.iter().enumerate() {
            let kind = match &statement.kind {
                ast::StatementKind::Local(local) => {
                    let initializer = match &local.kind {
                        ast::LocalKind::Declaration => None,
                        ast::LocalKind::Initialization(expression) => {
                            Some(self.lower_expression(expression))
                        }
                    };

                    let let_stmt = hir::LetStatement {
                        hir_id: self.next_id(),
                        is_mutable: local.is_mutable,
                        name: self.lower_ident(&local.name),
                        ty: local.ty.as_ref().map(|ty| self.lower_type(ty)),
                        initializer,
                        span: local.span,
                    };

                    self.local_id_map.insert(local.id, let_stmt.hir_id.local_id);

                    hir::StatementKind::Let(Rc::new(let_stmt))
                }
                ast::StatementKind::BareExpr(expression) => {
                    let expression = self.lower_expression(expression);

                    if i == len - 1 {
                        expr = Some(expression);
                        break;
                    }

                    hir::StatementKind::BareExpression(expression)
                }
                ast::StatementKind::SemiExpr(expression) => {
                    hir::StatementKind::SemiExpression(self.lower_expression(expression))
                }
                ast::StatementKind::Empty => continue,
            };

            result.push(Rc::new(hir::Statement {
                hir_id: self.next_id(),
                kind,
                span: statement.span,
            }));
        }

        (result.into(), expr)
    }

    fn lower_qualified_identifier(
        &mut self,
        qualified_identifier: &'ast ast::QualifiedIdentifier,
        namespace: Namespace,
    ) -> hir::Path {
        // There are 2 possibilities here:
        //   1) The ident has no qualifier and it refers to a local, function
        //      parameter, or local/imported definition
        //   2) The ident has a qualifier so we should start at the first segment
        //      and resolve from there

        let mut segments = Vec::new();

        match qualified_identifier.segments.as_slice() {
            [identifier] => {
                let map = match namespace {
                    Namespace::Value => &self.resolver.value_name_resolutions,
                    Namespace::Type => &self.resolver.type_name_resolutions,
                };

                let resolution = map
                    .get(&identifier.id)
                    .unwrap_or_else(|| panic!("identifier had no resolution: {identifier:#?}"));

                segments.push(Rc::new(hir::PathSegment {
                    hir_id: self.next_id(),
                    span: identifier.span,
                    identifier: self.lower_ident(identifier),
                    resolution: self.lower_resolution(resolution),
                }));
            }
            [ty_name, method_name] => {
                let ty_resolution = self
                    .resolver
                    .type_name_resolutions
                    .get(&ty_name.id)
                    .unwrap_or_else(|| {
                        self.report_bug(ty_name.span, "type name had no resolution")
                    });

                segments.push(Rc::new(hir::PathSegment {
                    hir_id: self.next_id(),
                    span: ty_name.span,
                    identifier: self.lower_ident(ty_name),
                    resolution: self.lower_resolution(ty_resolution),
                }));

                let map = match namespace {
                    Namespace::Value => &self.resolver.value_name_resolutions,
                    Namespace::Type => &self.resolver.type_name_resolutions,
                };

                let method_resolution = map.get(&method_name.id).unwrap_or_else(|| {
                    self.report_bug(method_name.span, "method name had no resolution")
                });

                segments.push(Rc::new(hir::PathSegment {
                    hir_id: self.next_id(),
                    span: method_name.span,
                    identifier: self.lower_ident(method_name),
                    resolution: self.lower_resolution(method_resolution),
                }));
            }
            _ => todo!("resolve identifier expressions with multiple segments"),
        }

        hir::Path {
            segments: segments.into(),
            span: qualified_identifier.span,
        }
    }

    fn lower_expression(&mut self, expression: &'ast ast::Expression) -> Rc<hir::Expression> {
        let kind = match &expression.kind {
            ast::ExpressionKind::Literal(literal) => {
                hir::ExpressionKind::Literal(self.lower_literal(literal))
            }
            ast::ExpressionKind::QualifiedIdentifier(qualified_identifier) => {
                hir::ExpressionKind::Path(
                    self.lower_qualified_identifier(qualified_identifier, Namespace::Value),
                )
            }
            ast::ExpressionKind::This => hir::ExpressionKind::This,
            ast::ExpressionKind::Grouping(expression) => return self.lower_expression(expression),
            ast::ExpressionKind::Tuple(expressions) => hir::ExpressionKind::Tuple(
                expressions
                    .iter()
                    .map(|e| self.lower_expression(e))
                    .collect(),
            ),
            ast::ExpressionKind::Array(array_initializer) => {
                match array_initializer.as_ref() {
                    ast::ArrayInitializer::Repeated { value, length } => {
                        let value = self.lower_expression(value);
                        let length = match length.kind {
                            ast::LiteralKind::Integer => length
                                .symbol
                                .value()
                                .parse()
                                // TODO: handle errors here
                                .expect("Failed to parse array length"),
                            _ => {
                                self.report_error(
                                    length.span,
                                    "Array length must be an integer literal",
                                );
                            }
                        };

                        hir::ExpressionKind::Array(hir::ArrayInitializer::Repeated {
                            value,
                            length,
                        })
                    }
                    ast::ArrayInitializer::Specific(expressions) => {
                        hir::ExpressionKind::Array(hir::ArrayInitializer::Specific(
                            expressions
                                .iter()
                                .map(|e| self.lower_expression(e))
                                .collect(),
                        ))
                    }
                }
            }
            ast::ExpressionKind::Struct { name, fields } => {
                let name = self.lower_qualified_identifier(name, Namespace::Type);

                let fields = fields
                    .iter()
                    .map(|field| {
                        let name = self.lower_ident(&field.name);
                        let value = self.lower_expression(&field.value);

                        Rc::new(hir::StructInitializerField {
                            hir_id: self.next_id(),
                            name,
                            value,
                            span: field.span,
                        })
                    })
                    .collect();

                hir::ExpressionKind::Struct { name, fields }
            }
            ast::ExpressionKind::Block(block) => {
                hir::ExpressionKind::Block(self.lower_block(block))
            }
            ast::ExpressionKind::FieldAccess {
                target,
                name,
                is_method_call,
            } => hir::ExpressionKind::FieldAccess {
                target: self.lower_expression(target),
                name: self.lower_ident(name),
                is_method_call: *is_method_call,
            },
            ast::ExpressionKind::FunctionCall { target, arguments } => {
                hir::ExpressionKind::FunctionCall {
                    target: self.lower_expression(target),
                    arguments: self.lower_function_call_argument_list(arguments),
                }
            }
            ast::ExpressionKind::Subscript { target, index } => hir::ExpressionKind::Subscript {
                target: self.lower_expression(target),
                index: self.lower_expression(index),
            },
            ast::ExpressionKind::Binary { lhs, operator, rhs } => hir::ExpressionKind::Binary {
                lhs: self.lower_expression(lhs),
                operator: operator.kind,
                rhs: self.lower_expression(rhs),
            },
            ast::ExpressionKind::Unary { operator, operand } => hir::ExpressionKind::Unary {
                operator: operator.kind,
                operand: self.lower_expression(operand),
            },
            ast::ExpressionKind::Cast { expression, ty } => hir::ExpressionKind::Cast {
                expression: self.lower_expression(expression),
                ty: self.lower_type(ty),
            },
            ast::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => hir::ExpressionKind::If {
                condition: self.lower_expression(condition),
                positive: self.lower_block(positive),
                negative: negative.as_ref().map(|e| self.lower_expression(e)),
            },
            ast::ExpressionKind::While { condition, block } => hir::ExpressionKind::While {
                condition: self.lower_expression(condition),
                block: self.lower_block(block),
            },
            ast::ExpressionKind::Assignment { lhs, rhs } => hir::ExpressionKind::Assignment {
                lhs: self.lower_expression(lhs),
                rhs: self.lower_expression(rhs),
            },
            ast::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                hir::ExpressionKind::OperatorAssignment {
                    operator: operator.kind,
                    lhs: self.lower_expression(lhs),
                    rhs: self.lower_expression(rhs),
                }
            }
            ast::ExpressionKind::Break => hir::ExpressionKind::Break,
            ast::ExpressionKind::Continue => hir::ExpressionKind::Continue,
            ast::ExpressionKind::Return(expression) => {
                hir::ExpressionKind::Return(expression.as_ref().map(|e| self.lower_expression(e)))
            }
        };

        Rc::new(hir::Expression {
            hir_id: self.next_id(),
            kind,
            span: expression.span,
        })
    }

    fn lower_literal(&mut self, literal: &'ast ast::Literal) -> hir::Literal {
        // FIXME: it feels like a lot of the work in this function should
        // probably be moved to the parser, but to make the experience nicer we
        // should only do that if we can gracefully recover from errors like
        // integers being too large

        let value = literal.symbol.value();

        match literal.kind {
            ast::LiteralKind::Boolean => {
                hir::Literal::Boolean(value.parse().unwrap_or_else(|_| {
                    unreachable!("invalid boolean literal value in AST: {value}")
                }))
            }
            ast::LiteralKind::Byte => {
                // TODO: parse escaped byte chars like b'\n' which may be
                // multiple characters. should the parser do this for us?

                let v = &value[2..value.len() - 1];

                let b = match v.chars().count() {
                    1 => v.as_bytes()[0],
                    2 => {
                        assert_eq!(v.as_bytes()[0], b'\\');

                        match v.as_bytes()[1] {
                            b'n' => b'\n',
                            b'r' => b'\r',
                            b'0' => b'\0',
                            _ => todo!(),
                        }
                    }
                    _ => unreachable!(),
                };

                hir::Literal::Integer(b as _, hir::LiteralIntegerKind::Unsigned(UIntKind::U8))
            }
            ast::LiteralKind::Char => {
                // TODO: parse escaped chars like '\n' which may be multiple
                // characters. should the parser do this for us?

                let v = &value[1..value.len() - 1];

                let c = match v.chars().count() {
                    1 => v.chars().next().unwrap(),
                    2 => {
                        assert_eq!(v.as_bytes()[0], b'\\');

                        let b = match v.as_bytes()[1] {
                            b'n' => '\n',
                            b'r' => '\r',
                            b'0' => '\0',
                            _ => todo!(),
                        };

                        b as _
                    }
                    _ => unreachable!(),
                };

                hir::Literal::Char(c)
            }
            ast::LiteralKind::Integer => {
                let value = value
                    .parse::<u64>()
                    .expect("Failed to parse integer literal");

                // TODO: detect suffix (should parser do this?)
                hir::Literal::Integer(value, hir::LiteralIntegerKind::Unsuffixed)
            }
            ast::LiteralKind::Float => {
                // TODO: detect suffix (should parser do this?)
                hir::Literal::Float(literal.symbol, hir::LiteralFloatKind::Unsuffixed)
            }
            // TODO: parse out escaped chars? should the parser do this to
            // validate escape sequences? should this be a recoverable error?
            ast::LiteralKind::String => hir::Literal::String(literal.symbol),
            ast::LiteralKind::ByteString => hir::Literal::ByteString(value.as_bytes().into()),
            ast::LiteralKind::CString => hir::Literal::CString(value.as_bytes().into()),
        }
    }

    fn lower_function_call_argument_list(
        &mut self,
        arguments: &'ast ast::FunctionCallArgumentList,
    ) -> Rc<[Rc<hir::Expression>]> {
        arguments
            .arguments
            .iter()
            .map(|e| self.lower_expression(e))
            .collect()
    }

    fn report_error(&self, offending_span: Span, message: &str) -> ! {
        eprintln!(
            "{} (at {})",
            message,
            self.module.source_file.format_span_position(offending_span)
        );
        self.module.source_file.highlight_span(offending_span);
        std::process::exit(1);
    }

    #[track_caller]
    fn report_bug(&self, offending_span: Span, message: &str) -> ! {
        #[cfg(feature = "error-backtrace")]
        eprintln!("{} {}", "error backtrace:".cyan(), Location::caller());

        eprintln!(
            "{} {} (at {})",
            "[==BUG==]".bold().red(),
            message,
            self.module.source_file.format_span_position(offending_span),
        );
        self.module.source_file.highlight_span(offending_span);
        std::process::exit(1);
    }
}

struct ItemLowerer<'a, 'ast> {
    module: &'ast ast::Module<'ast>,
    ast_index: &'a IndexVec<hir::LocalDefId, AstOwner<'ast>>,
    resolver: &'a ResolutionMap,
    definitions: &'a mut BTreeMap<hir::LocalDefId, hir::MaybeOwner>,
}

impl<'a, 'ast> ItemLowerer<'a, 'ast> {
    // Invokes the given lowering function using the provided ID to construct
    // new HIR nodes
    fn with_lctx(
        &mut self,
        local_def_id: hir::LocalDefId,
        f: impl FnOnce(&mut ItemLoweringContext<'_, 'ast>) -> hir::OwnerNode,
    ) {
        let mut lctx = ItemLoweringContext::new(
            self.module,
            self.resolver,
            local_def_id,
            &mut self.definitions,
        );

        // invoke the function after preparing the context for this owner
        let node = f(&mut lctx);

        let (nodes, parenting) = index_hir(&node, lctx.next_local_id.index(), lctx.body.clone());

        let body = lctx.body;

        // store the resulting owner
        self.definitions.insert(
            local_def_id,
            hir::MaybeOwner::Owner(hir::Owner {
                nodes,
                parenting,
                body,
            }),
        );
    }

    pub fn lower_node(&mut self, def_id: hir::LocalDefId) {
        let owner = &self.ast_index[def_id];

        match owner {
            AstOwner::NonOwner => {}
            AstOwner::Item(item) => {
                self.with_lctx(def_id, |lctx| hir::OwnerNode::Item(lctx.lower_item(*item)));
            }
        }
    }
}

pub fn lower_to_hir<'ast>(module: &'ast ast::Module<'ast>) -> hir::Module {
    let mut resolver = Resolver::new();
    resolver.resolve_module(module);
    let resolver = resolver.into_outputs();

    let index = index_ast(&resolver.node_to_def_id_map, module);
    let mut definitions = BTreeMap::new();

    let mut lowerer = ItemLowerer {
        module,
        ast_index: &index,
        resolver: &resolver,
        definitions: &mut definitions,
    };

    // lower nodes one at a time, resolving names and constructing HIR
    for def_id in index.indices() {
        lowerer.lower_node(def_id);
    }

    hir::Module { definitions }
}

/// Pulls out the items from the AST and indexes them based on their assigned
/// local def ID
pub fn index_ast<'ast>(
    node_to_def_id_map: &BTreeMap<ast::NodeId, hir::LocalDefId>,
    module: &'ast ast::Module,
) -> IndexVec<hir::LocalDefId, AstOwner<'ast>> {
    let mut indexer = AstIndexer {
        node_to_def_id_map,
        index: IndexVec::new(),
    };

    ast::visit::walk_module(&mut indexer, module);

    indexer.index
}

pub enum AstOwner<'ast> {
    NonOwner,
    Item(&'ast ast::Item),
}

pub struct AstIndexer<'a, 'ast> {
    node_to_def_id_map: &'a BTreeMap<ast::NodeId, hir::LocalDefId>,
    index: IndexVec<hir::LocalDefId, AstOwner<'ast>>,
}

impl<'a, 'ast> ast::visit::Visitor<'ast> for AstIndexer<'a, 'ast> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let def_id = *self.node_to_def_id_map.get(&item.id).unwrap();

        *self
            .index
            .ensure_contains_elem(def_id, || AstOwner::NonOwner) = AstOwner::Item(item);

        ast::visit::walk_item(self, item);
    }
}

pub fn index_hir(
    node: &hir::OwnerNode,
    node_count: usize,
    body: Option<Rc<hir::Body>>,
) -> (
    IndexVec<hir::ItemLocalId, hir::ParentedNode>,
    BTreeMap<hir::LocalDefId, hir::ItemLocalId>,
) {
    let mut indexer = HirIndexer {
        nodes: BTreeMap::new(),
        parenting: BTreeMap::new(),
        parent_node: hir::ItemLocalId::INVALID,
        owner: node.hir_id().owner,
        body,
    };

    match node {
        hir::OwnerNode::Item(item) => indexer.visit_item(item.clone()),
    }

    // collect map into index vec

    let mut index = IndexVec::new();

    for (local_id, node) in indexer.nodes {
        assert_eq!(
            local_id,
            index.next_index(),
            "missed node id during indexing"
        );
        index.push(node);
    }

    assert_eq!(
        index.next_index().index(),
        node_count,
        "less nodes indexed than expected"
    );

    (index, indexer.parenting)
}

pub struct HirIndexer {
    nodes: BTreeMap<hir::ItemLocalId, hir::ParentedNode>,
    parenting: BTreeMap<hir::LocalDefId, hir::ItemLocalId>,

    /// The parent of this node
    parent_node: hir::ItemLocalId,

    owner: hir::LocalDefId,
    body: Option<Rc<hir::Body>>,
}

impl HirIndexer {
    fn insert(&mut self, hir_id: hir::HirId, node: hir::Node) {
        self.nodes.insert(
            hir_id.local_id,
            hir::ParentedNode {
                parent: self.parent_node,
                node,
            },
        );
    }

    fn with_parent(&mut self, parent_id: hir::HirId, f: impl FnOnce(&mut Self)) {
        assert_eq!(parent_id.owner, self.owner);

        let parent_node = self.parent_node;
        self.parent_node = parent_id.local_id;
        f(self);
        self.parent_node = parent_node;
    }
}

impl hir::visit::Visitor for HirIndexer {
    fn visit_body(&mut self, body_id: hir::BodyId) {
        let Some(body) = &self.body else {
            unreachable!()
        };

        assert_eq!(body.id(), body_id);

        hir::visit::walk_body(self, body.clone());
    }

    fn visit_item(&mut self, item: Rc<hir::Item>) {
        assert_eq!(self.nodes.len(), 0);
        assert_eq!(self.parent_node, hir::ItemLocalId::INVALID);

        self.insert(item.hir_id(), hir::Node::Item(item.clone()));
        self.with_parent(item.hir_id(), |this| {
            hir::visit::walk_item(this, item);
        });
    }

    fn visit_function_parameter(&mut self, parameter: Rc<hir::FunctionParameter>) {
        self.insert(parameter.hir_id, hir::Node::FunctionParameter(parameter));
    }

    fn visit_struct_field(&mut self, field: Rc<hir::StructField>) {
        self.insert(field.hir_id, hir::Node::StructField(field.clone()));
        self.with_parent(field.hir_id, |this| {
            hir::visit::walk_struct_field(this, field);
        });
    }

    fn visit_enum_variant(&mut self, variant: Rc<hir::EnumVariant>) {
        self.insert(variant.hir_id, hir::Node::EnumVariant(variant.clone()));
        self.with_parent(variant.hir_id, |this| {
            hir::visit::walk_enum_variant(this, variant);
        });
    }

    fn visit_expression(&mut self, expression: Rc<hir::Expression>) {
        self.insert(expression.hir_id, hir::Node::Expression(expression.clone()));
        self.with_parent(expression.hir_id, |this| {
            hir::visit::walk_expression(this, expression);
        });
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, _context: hir::visit::BlockContext) {
        self.insert(block.hir_id, hir::Node::Block(block.clone()));
        self.with_parent(block.hir_id, |this| {
            hir::visit::walk_block(this, block);
        });
    }

    fn visit_statement(&mut self, statement: Rc<hir::Statement>) {
        self.insert(statement.hir_id, hir::Node::Statement(statement.clone()));
        self.with_parent(statement.hir_id, |this| {
            hir::visit::walk_statement(this, statement);
        });
    }

    fn visit_let_statement(&mut self, let_stmt: Rc<hir::LetStatement>) {
        self.insert(let_stmt.hir_id, hir::Node::LetStatement(let_stmt.clone()));
        self.with_parent(let_stmt.hir_id, |this| {
            hir::visit::walk_let_statement(this, let_stmt);
        });
    }

    fn visit_type(&mut self, ty: Rc<hir::Type>) {
        self.insert(ty.hir_id, hir::Node::Type(ty.clone()));
        self.with_parent(ty.hir_id, |this| {
            hir::visit::walk_type(this, ty);
        });
    }

    fn visit_path_segment(&mut self, segment: Rc<hir::PathSegment>) {
        self.insert(segment.hir_id, hir::Node::PathSegment(segment.clone()));
        self.with_parent(segment.hir_id, |this| {
            hir::visit::walk_path_segment(this, segment);
        });
    }

    fn visit_struct_initializer_field(&mut self, field: Rc<hir::StructInitializerField>) {
        self.insert(
            field.hir_id,
            hir::Node::StructInitializerField(field.clone()),
        );
        self.with_parent(field.hir_id, |this| {
            hir::visit::walk_struct_initializer_field(this, field);
        });
    }
}
