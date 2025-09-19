//! Drip Type Checker
//!
//! Type checking the HIR has 2 main components:
//!
//!   1) analyzing type definitions and function signatures to build up a typing
//!      environment
//!   2) type checking all the executable bodies in the HIR to make sure they
//!      comply with our type system's rules
//!
//! The first step is fairly strait-forward since its mostly get collecting
//! information. The second step is more involved and can be further broken down
//! into 2 more main steps:
//!
//!   1) traversing the body, assigning type variables to HIR nodes and
//!      collecting inference constraints
//!   2) solving the collected constraints and substituting types in the HIR
//!      until we either catch a type error or all constraints are satisfied
//!      and no more free type variables exist
//!
//! After we have verified that our program is type safe, we should no longer
//! report any errors since the input source code has been fully validated. From
//! there, the next step is to use the computed types to lower the HIR to LIR.

use std::{cell::OnceCell, collections::BTreeMap, panic::Location, rc::Rc};

use colored::Colorize;
use hashbrown::{HashMap, HashSet};

use super::{
    hir,
    primitive::{PrimitiveKind, UIntKind},
};
use crate::{
    frontend::{
        SourceFile,
        ast::{AssignmentOperatorClass, BinaryOperatorClass, UnaryOperatorKind},
        intern::InternedSymbol,
        lexer::Span,
    },
    index::Index,
    middle::{
        hir::DefinitionKind,
        primitive::{FloatKind, IntKind},
        ty::{FloatVariableId, IntVariableId, StructField, Type, TypeKind, TypeVariable},
    },
};

#[derive(Debug)]
struct TypeContext<'hir> {
    /// Module we are type checking
    module: &'hir hir::Module,
    /// Used for error reporting
    source_file: &'hir SourceFile,
    /// Type interning table to prevent duplicate types
    type_table: HashSet<Rc<TypeKind>>,
    /// Stores the computed types of top level items in the module
    def_id_to_type_map: BTreeMap<hir::LocalDefId, Type>,
}

impl<'hir> TypeContext<'hir> {
    fn new(module: &'hir hir::Module, source_file: &'hir SourceFile) -> Self {
        Self {
            module,
            source_file,
            type_table: HashSet::new(),
            def_id_to_type_map: BTreeMap::new(),
        }
    }

    pub fn intern_type(&mut self, kind: TypeKind) -> Type {
        let rc = self.type_table.get_or_insert(Rc::new(kind));
        Type::new_from_reference_only_for_interning(rc.clone())
    }

    pub fn get_error_type(&mut self) -> Type {
        self.intern_type(TypeKind::Error)
    }

    pub fn get_unit_type(&mut self) -> Type {
        self.get_primitive_type(PrimitiveKind::Unit)
    }

    pub fn get_primitive_type(&mut self, primitive: PrimitiveKind) -> Type {
        match primitive {
            PrimitiveKind::Never => self.intern_type(TypeKind::Never),
            PrimitiveKind::Unit => self.intern_type(TypeKind::Unit),
            PrimitiveKind::Int(int_kind) => self.intern_type(TypeKind::Integer(int_kind)),
            PrimitiveKind::UInt(uint_kind) => {
                self.intern_type(TypeKind::UnsignedInteger(uint_kind))
            }
            PrimitiveKind::Float(float_kind) => self.intern_type(TypeKind::Float(float_kind)),
            PrimitiveKind::Bool => self.intern_type(TypeKind::Bool),
            PrimitiveKind::Char => self.intern_type(TypeKind::Char),
            PrimitiveKind::Str => self.intern_type(TypeKind::Str),
            PrimitiveKind::CStr => self.intern_type(TypeKind::CStr),
        }
    }

    fn compute_hir_type(&mut self, ty: Rc<hir::Type>) -> Type {
        match &ty.kind {
            hir::TypeKind::Unit => self.get_unit_type(),
            hir::TypeKind::Path(path) => self.compute_hir_resolution_type(*path.resolution()),
            hir::TypeKind::Pointer(ty) => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Pointer(inner))
            }
            hir::TypeKind::Slice(ty) => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Slice(inner))
            }
            hir::TypeKind::Array { ty, length } => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Array {
                    ty: inner,
                    length: *length,
                })
            }
            hir::TypeKind::Tuple(types) => {
                let types = types
                    .iter()
                    .map(|ty| self.compute_hir_type(ty.clone()))
                    .collect();

                self.intern_type(TypeKind::Tuple(types))
            }
            hir::TypeKind::FunctionPointer {
                parameters,
                return_type,
                is_variadic,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|ty| self.compute_hir_type(ty.clone()))
                    .collect();

                let return_type = return_type
                    .as_ref()
                    .map(|ty| self.compute_hir_type(ty.clone()))
                    .unwrap_or_else(|| self.get_unit_type());

                self.intern_type(TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic: *is_variadic,
                })
            }
            hir::TypeKind::Any => self.intern_type(TypeKind::Any),
        }
    }

    fn compute_hir_resolution_type(&mut self, resolution: hir::Resolution) -> Type {
        match resolution {
            hir::Resolution::Definition(_definition_kind, local_def_id) => {
                let owner = &self.module.owners[local_def_id];

                match owner.node() {
                    hir::OwnerNode::Item(item) => self.def_id_to_type_map[&item.owner_id].clone(),
                }
            }
            hir::Resolution::Primitive(primitive_kind) => self.get_primitive_type(primitive_kind),
            hir::Resolution::IntrinsicFunction(name) => match name.value() {
                "print" => {
                    let ret_ty = self.get_primitive_type(PrimitiveKind::Int(IntKind::I64));
                    let str_ty = self.get_primitive_type(PrimitiveKind::Str);

                    self.intern_type(TypeKind::FunctionPointer {
                        parameters: [str_ty].into(),
                        return_type: ret_ty,
                        is_variadic: true,
                    })
                }
                "exit" => {
                    let ret_ty = self.get_primitive_type(PrimitiveKind::Never);
                    let u8_ty = self.get_primitive_type(PrimitiveKind::UInt(UIntKind::U8));

                    self.intern_type(TypeKind::FunctionPointer {
                        parameters: [u8_ty].into(),
                        return_type: ret_ty,
                        is_variadic: false,
                    })
                }
                name => unreachable!("unknown intrinsic function `{name}`"),
            },
            r => unreachable!("encountered value resolution in type namespace: {r:?}"),
        }
    }

    fn compute_self_type(
        &mut self,
        name: &hir::Path,
        signature: &hir::FunctionSignature,
    ) -> Option<Type> {
        let Some(self_parameter) = signature.self_parameter else {
            return None;
        };

        let hir::Resolution::Definition(hir::DefinitionKind::Struct, implementor_id) =
            &name.segments[0].resolution
        else {
            unreachable!()
        };

        let owned_ty = self.def_id_to_type_map[implementor_id].clone();

        let self_ty = match self_parameter {
            hir::SelfParameter::Owned => owned_ty,
            hir::SelfParameter::Pointer { is_mutable: _ } => {
                self.intern_type(TypeKind::Pointer(owned_ty))
            }
        };

        Some(self_ty)
    }

    #[track_caller]
    fn report_bug(&self, offending_span: Span, message: &str) -> ! {
        eprintln!(
            "{}: {} {}",
            "bug".green(),
            message,
            format!(
                "(at {})",
                self.source_file.format_span_position(offending_span),
            )
            .white()
        );

        #[cfg(feature = "error-backtrace")]
        eprintln!("{} {}", "backtrace:".cyan(), Location::caller());

        self.source_file.highlight_span(offending_span);

        std::process::exit(1);
    }

    fn report_error(&self, error: TypeError) {
        let message = match error.kind {
            TypeErrorKind::TypeMismatch { expected, actual } => match error.origin.kind {
                TypeBoundary::LetStatement => {
                    format!(
                        "let binding initializer type {actual} does not match explicit type {expected}"
                    )
                }
                TypeBoundary::FunctionArgument => {
                    format!("expected function argument to be {expected} but found {actual}")
                }
                TypeBoundary::Cast => {
                    format!("{actual} cannot be trivially cast to {expected}")
                }
                TypeBoundary::IfCondition => {
                    format!("expected if condition type to be {expected} but found {actual}")
                }
                TypeBoundary::IfBlock => {
                    format!(
                        "expected positive type of if condition {expected} to match negative type {actual}"
                    )
                }
                TypeBoundary::WhileCondition => {
                    format!("expected while condition type to be {expected} but found {actual}")
                }
                TypeBoundary::BareExpression => {
                    format!("expected bare expression type to be {expected} but found {actual}")
                }
                TypeBoundary::BinaryOp => format!(
                    "expected left-hand side of binary op {expected} to match right-hand side {actual}"
                ),
                TypeBoundary::Assignment => {
                    format!("cannot assign {actual} to variable with type {expected}")
                }
                TypeBoundary::OpAssignment => format!(
                    "cannot use {actual} in operator assignment to variable with type {expected}"
                ),
                TypeBoundary::ExplicitReturn => format!(
                    "explicit return type {actual} does not match the function signature's return type {expected}"
                ),
                TypeBoundary::ImplicitReturn => format!(
                    "implicit return type {actual} does not match the function signature's return type {expected}"
                ),
                TypeBoundary::ArrayInitializer => format!(
                 "array element type {actual} does not match the expected type {expected}"
                ),
                TypeBoundary::StructInitializer => format!(
                 "field type {actual} does not match the expected type {expected}"
                ),
                TypeBoundary::FieldAccess
                | TypeBoundary::FunctionCall
                | TypeBoundary::Deref
                | TypeBoundary::LogicalOp
                | TypeBoundary::ArithmeticOp | TypeBoundary::LoopControlFlow | TypeBoundary::SelfExpression  => {
                    unreachable!("these are not used with type mismatch")
                }
            },
            // TODO: use error.origin.kind for even better error reporting in some cases
            TypeErrorKind::InvalidOperation {
                attempted_usage,
                provided,
            } => match attempted_usage {
                TypeUsage::ArithmeticOperation => {
                    format!("cannot use type {provided} in an arithmetic context")
                }
                TypeUsage::LogicalOperation => {
                    format!("cannot use type {provided} in a logical context")
                }
                    TypeUsage::FieldAccess => {
                    format!("{provided} does not support field access")
                }
                TypeUsage::FunctionCall => {
                    format!("cannot use type {provided} as the target of a function call")
                }
                TypeUsage::Deref => {
                    format!("type {provided} cannot be dereferenced")
                }
            },
            TypeErrorKind::InfinitelyRecursiveType { variable, ty } => {
                // I'm fairly certain that this is impossible, so if we catch it
                // in the wild then I will be impressed
                format!("type {ty} is infinitely recursive (variable = {variable:?})")
            }
            TypeErrorKind::ArgumentLengthMismatch { expected, actual } => {
                format!("expected {expected} argument(s) to this function but found {actual}")
            }
            TypeErrorKind::CannotInfer => match error.origin.kind {
                TypeBoundary::LetStatement => "cannot infer the type of this binding without an explicit type or initializer expression".to_string(),
                _ => unreachable!()
            },
            TypeErrorKind::IllegalLoopControlFlow(LoopControlFlowKind::Break) => "`break` statement can only be used within loops".to_string(),
            TypeErrorKind::IllegalLoopControlFlow(LoopControlFlowKind::Continue) => "`continue` statement can only be used within loops".to_string(),
            TypeErrorKind::MissingReturnValue { expected } => match error.origin.kind {
                TypeBoundary::ExplicitReturn =>  format!("explicit return type does not match the expected type {expected}"),
                TypeBoundary::ImplicitReturn =>  format!("expected function to return type {expected} but no implicit or explicit returns found"),
                _ => unreachable!()
            },
            TypeErrorKind::InvalidCast { from, to } => format!("non-trivial cast from {from} to {to}"),
            TypeErrorKind::TupleLengthMismatch { expected, actual } => format!("tuples have different arity, expected {expected} parameters but found {actual}"),
             TypeErrorKind::ArrayLengthMismatch { expected, actual } => format!("arrays have different length, expected {expected} parameters but found {actual}"),
            TypeErrorKind::IllegalMutation => "cannot mutate immutable variable".to_string(),
            TypeErrorKind::InvalidAssignment => "invalid left-hand side of assignment".to_string(),
            TypeErrorKind::UnknownFieldAccess {target, name } => format!("field `{name}` does not exist on type {target}"),
            TypeErrorKind::MissingStructField { name } => format!("missing field `{name}`"),
            TypeErrorKind::ExtraStructField { name } => format!("unexpected field `{name}`"),
            TypeErrorKind::IllegalSelfUsage => format!("`self` may only not be used in functions without a `self` parameter"),
        };

        eprintln!(
            "{}: {} {}",
            "error".red(),
            message,
            format!(
                "(at {})",
                self.source_file.format_span_position(error.origin.span),
            )
            .white()
        );
        self.source_file.highlight_span(error.origin.span);
    }
}

/// Traverses the top level items in a module and computes their types, adding
/// them to a type resolution map
#[derive(Debug)]
struct GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    type_context: &'tcx mut TypeContext<'hir>,
}

impl<'tcx, 'hir> GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    fn compute_type_for_function_signature(
        &mut self,
        name: &hir::Path,
        signature: &hir::FunctionSignature,
    ) -> Type {
        let self_ty = self.type_context.compute_self_type(name, signature);

        let parameters = self_ty
            .into_iter()
            .chain(
                signature
                    .parameters
                    .iter()
                    .map(|ty| self.type_context.compute_hir_type(ty.clone())),
            )
            .collect();

        let return_type = signature
            .return_type
            .as_ref()
            .map(|ty| self.type_context.compute_hir_type(ty.clone()))
            .unwrap_or_else(|| self.type_context.get_unit_type());

        self.type_context.intern_type(TypeKind::FunctionPointer {
            parameters,
            return_type,
            is_variadic: signature.variadic_type.is_some(),
        })
    }
}

impl<'tcx, 'hir> hir::visit::Visitor for GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    fn visit_item(&mut self, item: Rc<hir::Item>) {
        match &item.kind {
            hir::ItemKind::Function {
                name, signature, ..
            } => {
                let ty = self.compute_type_for_function_signature(name, signature);
                self.type_context
                    .def_id_to_type_map
                    .insert(item.owner_id, ty);
            }
            hir::ItemKind::Struct { name, fields } => {
                let name = name.symbol;
                let fields = fields
                    .iter()
                    .map(|field| StructField {
                        name: field.name.symbol,
                        ty: self.type_context.compute_hir_type(field.ty.clone()),
                    })
                    .collect();

                let ty = self.type_context.intern_type(TypeKind::Struct {
                    def_id: item.owner_id,
                    name,
                    fields,
                });
                self.type_context
                    .def_id_to_type_map
                    .insert(item.owner_id, ty);
            }
            hir::ItemKind::TypeAlias { ty, .. } => {
                let ty = self.type_context.compute_hir_type(ty.clone());
                self.type_context
                    .def_id_to_type_map
                    .insert(item.owner_id, ty);
            }
            hir::ItemKind::Static {
                is_mutable,
                name,
                ty,
                initializer,
            } => {
                let ty = self.type_context.compute_hir_type(ty.clone());
                self.type_context
                    .def_id_to_type_map
                    .insert(item.owner_id, ty);
            }
        }
    }
}

/// The context associated with type checking an individual executable body
struct TypeChecker<'tcx, 'hir> {
    type_context: &'tcx mut TypeContext<'hir>,
    owner_id: hir::LocalDefId,

    /// Stores what types we've assigned to HIR nodes so far. This is
    /// effectively the type environment Γ from type theory just without using
    /// the names directly (resolved during ast lowering)
    node_to_type_map: BTreeMap<hir::ItemLocalId, Type>,
    /// Stores the method resolutions we computed for each field access
    /// expression within a function call expression
    method_resolution_map: BTreeMap<hir::ItemLocalId, hir::LocalDefId>,

    /// A list of accumulated constraints on the existing free type variables
    constraints: Vec<TypeConstraint>,
    /// Errors we've collected while type checking
    errors: Vec<TypeError>,

    /// Keeps track of whether we are in a loop context (for break and continue)
    within_loop: bool,
    self_type: OnceCell<Type>,
    return_type: OnceCell<Type>,

    next_integer_variable_id: IntVariableId,
    next_float_variable_id: FloatVariableId,
}

#[derive(Debug)]
struct TypeConstraint {
    kind: TypeConstraintKind,
    origin: TypeConstraintOrigin,
}

#[derive(Debug)]
enum TypeConstraintKind {
    Equal { left: Type, right: Type },
    Cast { from: Type, to: Type },
}

#[derive(Debug)]
struct TypeConstraintOrigin {
    /// The span enclosing the entire node which generated the constraint in the
    /// original traversal
    span: Span,
    /// Used to format error messages better
    kind: TypeBoundary,
}

/// A kind of place in the source code where a constraint may be generated
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeBoundary {
    /// If an explicit type is specified for a let binding, the expression must
    /// have that type
    LetStatement,
    /// If a field is accessed, it must exist on the target type
    FieldAccess,
    /// Function arguments must match the expected number
    FunctionCall,
    /// Function argument type must match function parameter type
    FunctionArgument,
    /// Cast operand must match target type
    Cast,
    /// If conditions must be the bool type
    IfCondition,
    /// Blocks of an if statement must have the same type
    IfBlock,
    /// While conditions must be the bool type
    WhileCondition,
    /// Bare expressions in a block which are not the last in the block must
    /// have be unit type
    BareExpression,
    /// Dereferencing can only be done on pointer types
    Deref,
    /// Cannot use non-boolean types in a logical context
    LogicalOp,
    /// Cannot use non-arithmetic types in arithmetic contexts
    ArithmeticOp,
    /// Sides of binary op must have the same type
    BinaryOp,
    /// Sides of assignment must have the same type
    Assignment,
    /// Sides of op assignment must have the same type
    OpAssignment,
    /// Break or continue statement
    LoopControlFlow,
    /// Return value type must match body return type
    ExplicitReturn,
    /// Implicit return type must match function signature type
    ImplicitReturn,
    /// All elements of an array initializer must be of the same type
    ArrayInitializer,
    /// All fields in a struct must be present, all fields must be of the
    /// expected type, and there must not be any extra fields
    StructInitializer,
    /// Self expression is only valid in functions with a self parameter
    SelfExpression,
}

impl<'tcx, 'hir> TypeChecker<'tcx, 'hir> {
    fn insert_type(&mut self, hir_id: hir::HirId, ty: Type) -> Type {
        assert_eq!(hir_id.owner, self.owner_id);

        self.node_to_type_map.insert(hir_id.local_id, ty.clone());
        ty
    }

    #[track_caller]
    fn copy_type_from(&mut self, dest_id: hir::HirId, src_id: impl Into<hir::ItemLocalId>) -> Type {
        assert_eq!(dest_id.owner, self.owner_id);

        let shared = self.node_to_type_map[&src_id.into()].clone();
        self.node_to_type_map
            .insert(dest_id.local_id, shared.clone());
        shared
    }

    #[track_caller]
    fn get_type(&mut self, id: impl Into<hir::ItemLocalId>) -> Type {
        self.node_to_type_map[&id.into()].clone()
    }

    /// Adds a constraint that the left type should equal the right type
    fn add_equality_constraint(&mut self, left: Type, right: Type, origin: TypeConstraintOrigin) {
        self.constraints.push(TypeConstraint {
            kind: TypeConstraintKind::Equal { left, right },
            origin,
        });
    }

    /// Adds a constraint that `from` needs to be able to be cast to `to`
    fn add_cast_constraint(&mut self, from: Type, to: Type, origin: TypeConstraintOrigin) {
        self.constraints.push(TypeConstraint {
            kind: TypeConstraintKind::Cast { from, to },
            origin,
        });
    }

    fn create_fresh_integer_var(&mut self) -> Type {
        let id = self.next_integer_variable_id;
        self.next_integer_variable_id.increment_by(1);

        self.type_context
            .intern_type(TypeKind::Infer(TypeVariable::Int(id)))
    }

    fn create_fresh_float_var(&mut self) -> Type {
        let id = self.next_float_variable_id;
        self.next_float_variable_id.increment_by(1);

        self.type_context
            .intern_type(TypeKind::Infer(TypeVariable::Float(id)))
    }

    fn compute_type_for_literal(&mut self, literal: &hir::Literal) -> Type {
        match literal {
            hir::Literal::Boolean(_) => self.type_context.get_primitive_type(PrimitiveKind::Bool),
            hir::Literal::Char(_) => self.type_context.get_primitive_type(PrimitiveKind::Char),
            hir::Literal::Integer(_, literal_integer_kind) => match literal_integer_kind {
                hir::LiteralIntegerKind::Unsigned(uint_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::UInt(*uint_kind)),
                hir::LiteralIntegerKind::Signed(int_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::Int(*int_kind)),
                hir::LiteralIntegerKind::Unsuffixed => self.create_fresh_integer_var(),
            },
            hir::Literal::Float(_, literal_float_kind) => match literal_float_kind {
                hir::LiteralFloatKind::Suffixed(float_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::Float(*float_kind)),
                hir::LiteralFloatKind::Unsuffixed => self.create_fresh_float_var(),
            },
            hir::Literal::String(_) => self.type_context.get_primitive_type(PrimitiveKind::Str),
            hir::Literal::ByteString(_) => {
                let inner = self
                    .type_context
                    .get_primitive_type(PrimitiveKind::UInt(UIntKind::U8));
                self.type_context.intern_type(TypeKind::Slice(inner))
            }
            hir::Literal::CString(_) => self.type_context.get_primitive_type(PrimitiveKind::CStr),
        }
    }

    fn solve_constraints(&mut self) -> (SubstitutionMap, Vec<TypeError>) {
        let mut substitution_map = SubstitutionMap::new();
        let mut deferred_casts: Vec<TypeConstraint> = vec![];
        let mut errors = vec![];

        for constraint in core::mem::take(&mut self.constraints) {
            match &constraint.kind {
                TypeConstraintKind::Equal { left, right } => {
                    if let Err(e) = self.unify(left.clone(), right.clone(), &mut substitution_map) {
                        errors.push(TypeError {
                            origin: constraint.origin,
                            kind: e,
                        })
                    }
                }
                TypeConstraintKind::Cast { from, to } => {
                    if self
                        .solve_cast(from.clone(), to.clone(), &mut substitution_map, false)
                        .is_err()
                    {
                        deferred_casts.push(constraint);
                    }
                }
            }
        }

        // Do a second pass after we've done all our substitutions
        for constraint in deferred_casts {
            let TypeConstraintKind::Cast { from, to } = constraint.kind else {
                unreachable!()
            };

            if let Err(e) = self.solve_cast(from, to, &mut substitution_map, true) {
                errors.push(TypeError {
                    origin: constraint.origin,
                    kind: e,
                })
            }
        }

        (substitution_map, errors)
    }

    /// Attempts to equate the provided types using our type system's inference
    /// and coercion rules. For any recursive unifications, we only return the
    /// top most error to provide the most context
    fn unify(
        &mut self,
        t1: Type,
        t2: Type,
        substitution_map: &mut SubstitutionMap,
    ) -> Result<(), TypeErrorKind> {
        let t1 = self.apply_substitution(substitution_map, t1);
        let t2 = self.apply_substitution(substitution_map, t2);

        match (&*t1, &*t2) {
            // Both already the same type (trivial)
            (t1, t2) if t1 == t2 => Ok(()),

            // One is a a type variable
            (TypeKind::Infer(variable), ty_kind) | (ty_kind, TypeKind::Infer(variable)) => {
                // It is guaranteed that this type is already interned, but I
                // cant figure out a nicer way to write this
                let ty = self.type_context.intern_type(ty_kind.clone());

                // This is where we define our inference coercion rules
                let coercible = match variable {
                    TypeVariable::Int(_) => ty_kind.is_integer_like(),
                    TypeVariable::Float(_) => ty_kind.is_float_like(),
                };

                if !coercible {
                    return Err(TypeErrorKind::TypeMismatch {
                        expected: t1,
                        actual: t2,
                    });
                }

                if self.occurs_in(*variable, ty.clone(), substitution_map) {
                    return Err(TypeErrorKind::InfinitelyRecursiveType {
                        variable: *variable,
                        ty,
                    });
                }

                substitution_map.insert(*variable, ty);

                Ok(())
            }

            // Pointee types need to be equal
            (TypeKind::Pointer(left), TypeKind::Pointer(right))
            | (TypeKind::Slice(left), TypeKind::Slice(right)) => {
                if self
                    .unify(left.clone(), right.clone(), substitution_map)
                    .is_err()
                {
                    return Err(TypeErrorKind::TypeMismatch {
                        expected: t1,
                        actual: t2,
                    });
                }

                Ok(())
            }

            // Must have same inner type and length
            (
                TypeKind::Array {
                    ty: left_ty,
                    length: left_len,
                },
                TypeKind::Array {
                    ty: right_ty,
                    length: right_len,
                },
            ) => {
                if left_len != right_len {
                    return Err(TypeErrorKind::ArrayLengthMismatch {
                        expected: *left_len,
                        actual: *right_len,
                    });
                }

                if self
                    .unify(left_ty.clone(), right_ty.clone(), substitution_map)
                    .is_err()
                {
                    return Err(TypeErrorKind::TypeMismatch {
                        expected: t1,
                        actual: t2,
                    });
                }

                Ok(())
            }

            // For tuple types, all sub types need to be equal too
            (TypeKind::Tuple(types1), TypeKind::Tuple(types2)) => {
                if types1.len() != types2.len() {
                    return Err(TypeErrorKind::TupleLengthMismatch {
                        expected: types1.len(),
                        actual: types2.len(),
                    });
                }

                for (left, right) in types1.iter().zip(types2.iter()) {
                    if self
                        .unify(left.clone(), right.clone(), substitution_map)
                        .is_err()
                    {
                        return Err(TypeErrorKind::TypeMismatch {
                            expected: t1,
                            actual: t2,
                        });
                    }
                }

                Ok(())
            }

            (TypeKind::FunctionPointer { .. }, TypeKind::FunctionPointer { .. }) => {
                todo!("unify function pointer types")
            }

            // Array pointers can be coerced to slices
            (TypeKind::Slice(left), TypeKind::Pointer(right))
                if matches!(&**right, TypeKind::Array { .. }) =>
            {
                let TypeKind::Array { ty: right, .. } = &**right else {
                    unreachable!()
                };

                if self
                    .unify(left.clone(), right.clone(), substitution_map)
                    .is_err()
                {
                    return Err(TypeErrorKind::TypeMismatch {
                        expected: t1,
                        actual: t2,
                    });
                }

                Ok(())
            }

            // Any other type combination
            _ => Err(TypeErrorKind::TypeMismatch {
                expected: t1,
                actual: t2,
            }),
        }
    }

    /// Checks that `from` may be cast to `to`, potentially coercing `from` if
    /// it is a free type variable
    fn solve_cast(
        &mut self,
        from: Type,
        to: Type,
        substitution_map: &mut SubstitutionMap,
        coerce_type_variables: bool,
    ) -> Result<(), TypeErrorKind> {
        assert!(
            to.free_type_variables().is_empty(),
            "attempted to solve cast to non-concrete type: {to}"
        );

        let from = self.apply_substitution(substitution_map, from);

        match (&*from, &*to) {
            (_, TypeKind::Infer(_)) => unreachable!(),
            // Trivially possible case
            (from_kind, to_kind) if from_kind == to_kind => Ok(()),
            // If the source type is a free type variable, just coerce it into
            // the target type if allowed for the variable kind and coersion is
            // enabled
            (TypeKind::Infer(variable), ty_kind) => {
                let coercible = {
                    match variable {
                        TypeVariable::Int(_) => {
                            ty_kind.is_integer_like()
                                | matches!(ty_kind, TypeKind::Pointer(_) | TypeKind::Any)
                        }
                        TypeVariable::Float(_) => ty_kind.is_float_like(),
                    }
                };

                if coercible && coerce_type_variables {
                    substitution_map.insert(*variable, to);
                    return Ok(());
                }

                Err(TypeErrorKind::InvalidCast { from, to })
            }
            // Allow casting between any numeric types
            (
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Float(_),
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Float(_),
            ) => Ok(()),
            // Allow casting between integer types and bools
            (
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Bool,
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Bool,
            ) => Ok(()),
            (TypeKind::Char, TypeKind::UnsignedInteger(UIntKind::U32)) => Ok(()),
            // Allow casting properly sized integers to pointers
            (TypeKind::UnsignedInteger(UIntKind::USize), TypeKind::Pointer(_) | TypeKind::Any) => {
                Ok(())
            }
            // Allow pointer type hacking
            (TypeKind::Pointer(_) | TypeKind::Any, TypeKind::Pointer(_) | TypeKind::Any) => Ok(()),
            // Anything not explicitly allowed is an error
            _ => Err(TypeErrorKind::InvalidCast { from, to }),
        }
    }

    fn occurs_in(
        &mut self,
        var: TypeVariable,
        ty: Type,
        substitution_map: &SubstitutionMap,
    ) -> bool {
        match &*self.apply_substitution(substitution_map, ty) {
            TypeKind::Infer(id) => *id == var,
            TypeKind::Pointer(inner)
            | TypeKind::Slice(inner)
            | TypeKind::Array { ty: inner, .. } => {
                self.occurs_in(var, inner.clone(), substitution_map)
            }
            TypeKind::Tuple(types) => types
                .iter()
                .any(|ty| self.occurs_in(var, ty.clone(), substitution_map)),
            TypeKind::FunctionPointer {
                parameters,
                return_type,
                ..
            } => {
                parameters
                    .iter()
                    .any(|ty| self.occurs_in(var, ty.clone(), substitution_map))
                    || self.occurs_in(var, return_type.clone(), substitution_map)
            }
            _ => false,
        }
    }

    /// Recursively applies substitutions to the provided type to generate a new
    /// type with less or ideally no type variables
    fn apply_substitution(&mut self, substitution_map: &SubstitutionMap, ty: Type) -> Type {
        match &*ty {
            TypeKind::Infer(TypeVariable::Int(id)) => {
                if let Some(t) = substitution_map.int_map.get(id) {
                    self.apply_substitution(substitution_map, t.clone())
                } else {
                    ty
                }
            }
            TypeKind::Infer(TypeVariable::Float(id)) => {
                if let Some(t) = substitution_map.float_map.get(id) {
                    self.apply_substitution(substitution_map, t.clone())
                } else {
                    ty
                }
            }
            TypeKind::Pointer(inner) => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context
                    .intern_type(TypeKind::Pointer(substituted))
            }
            TypeKind::Slice(inner) => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context.intern_type(TypeKind::Slice(substituted))
            }
            TypeKind::Array { ty: inner, length } => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context.intern_type(TypeKind::Array {
                    ty: substituted,
                    length: *length,
                })
            }
            TypeKind::Tuple(types) => {
                let types = types
                    .iter()
                    .map(|ty| self.apply_substitution(substitution_map, ty.clone()))
                    .collect();

                self.type_context.intern_type(TypeKind::Tuple(types))
            }
            TypeKind::FunctionPointer {
                parameters,
                return_type,
                is_variadic,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|ty| self.apply_substitution(substitution_map, ty.clone()))
                    .collect();
                let return_type = self.apply_substitution(substitution_map, return_type.clone());

                self.type_context.intern_type(TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic: *is_variadic,
                })
            }
            _ => ty,
        }
    }

    /// Attempts to solve type constraints, returning type check results if it
    /// was able to do so successfully
    pub fn into_output(mut self) -> Result<TypeCheckResults, Vec<TypeError>> {
        // Solve the collected constraints
        let (substitution_map, mut errors) = self.solve_constraints();
        self.errors.append(&mut errors);

        // If we unified successfully but had other problems before, stop here
        if !self.errors.is_empty() {
            let mut errors = core::mem::take(&mut self.errors);

            // Apply substitutions on types in the collected errors to generate
            // more useful output
            for err in &mut errors {
                for ty in err.kind.get_substitutable_types_mut() {
                    *ty = self.apply_substitution(&substitution_map, ty.clone());
                }
            }

            return Err(errors);
        }

        // FIXME: we could optimize this by first only applying substitutions to
        // the set of unique types, create a map of the resulting substitutions,
        // and then apply those computed recursive substitutions to all the
        // types in the node type map.

        // Apply all the substitutions we calculated to all the nodes in the type
        let mut node_types = core::mem::take(&mut self.node_to_type_map);

        for ty in node_types.values_mut() {
            *ty = self.apply_substitution(&substitution_map, ty.clone());
        }

        // Apply default substitutions to any remaining free type variables
        let mut default_substitutions = SubstitutionMap::new();
        let mut unconstrained_nodes = HashSet::new();

        for (id, ty) in &mut node_types {
            let free_type_variables = ty.free_type_variables();

            if free_type_variables.is_empty() {
                continue;
            }

            for ftv in free_type_variables {
                let default_ty = match ftv {
                    TypeVariable::Int(_) => self
                        .type_context
                        .get_primitive_type(PrimitiveKind::Int(IntKind::I32)),
                    TypeVariable::Float(_) => self
                        .type_context
                        .get_primitive_type(PrimitiveKind::Float(FloatKind::F32)),
                };

                default_substitutions.insert(ftv, default_ty);
            }

            unconstrained_nodes.insert(*id);
        }

        for (id, ty) in &mut node_types {
            // Simple optimization to not check nodes which we know dont have
            // any unconstrained types
            if !unconstrained_nodes.contains(id) {
                continue;
            }

            *ty = self.apply_substitution(&default_substitutions, ty.clone());
        }

        self.node_to_type_map = node_types;

        for (id, node) in self
            .type_context
            .module
            .get_owner(self.owner_id)
            .nodes
            .enumerate()
        {
            // Skip the owner node
            if id == hir::ItemLocalId::ZERO {
                continue;
            }

            assert!(
                self.node_to_type_map.contains_key(&id),
                "missing type for node {id:#?} = {node:#?}"
            );
            assert!(
                self.get_type(id).free_type_variables().is_empty(),
                "node {id:?} has remaining free type variables in its type"
            );
        }

        Ok(TypeCheckResults {
            owner_id: self.owner_id,
            node_types: self.node_to_type_map,
            method_resolutions: self.method_resolution_map,
            self_type: self.self_type.get().cloned(),
        })
    }
}

#[derive(Debug)]
struct SubstitutionMap {
    int_map: HashMap<IntVariableId, Type>,
    float_map: HashMap<FloatVariableId, Type>,
}

impl SubstitutionMap {
    fn new() -> Self {
        Self {
            int_map: HashMap::new(),
            float_map: HashMap::new(),
        }
    }

    fn insert(&mut self, variable: TypeVariable, ty: Type) {
        match variable {
            TypeVariable::Int(id) => {
                self.int_map.insert(id, ty);
            }
            TypeVariable::Float(id) => {
                self.float_map.insert(id, ty);
            }
        }
    }
}

#[derive(Debug)]
struct TypeError {
    origin: TypeConstraintOrigin,
    kind: TypeErrorKind,
}

#[derive(Debug)]
enum TypeErrorKind {
    /// The expected type did not match the actual type we found in that
    /// position (semantics depend a lot on the constraint origin which caused
    /// this error). This only applies when we know exactly what the target type
    /// should be, not for generic requirements like "binary ops should have
    /// arithmetic types". For that, we use
    /// [`InvalidOperation`](`Self::InvalidOperation`)
    TypeMismatch { expected: Type, actual: Type },
    /// The provided type does not support the operation it is used in. For
    /// example, using a str in an arithmetic expression, or using an int as the
    /// target of a function call expression.
    InvalidOperation {
        attempted_usage: TypeUsage,
        provided: Type,
    },
    /// A type variable whose type contains itself. Not sure if this is actually
    /// possible to happen in our type system, but maybe it could happen in the
    /// future depending on the features we add so its good to implement it
    /// early on
    InfinitelyRecursiveType { variable: TypeVariable, ty: Type },
    /// Number of args provided to function do not match its call signature
    ArgumentLengthMismatch { expected: usize, actual: usize },
    /// Local binding declared with no explicit type and no initializer
    CannotInfer,
    /// Tried to use break or continue outside loop context
    IllegalLoopControlFlow(LoopControlFlowKind),
    /// If function's return type is not `()`, return expressions must contain a
    /// value
    MissingReturnValue { expected: Type },
    /// Tried to perform non-trivial cast
    InvalidCast { from: Type, to: Type },
    /// Tuples that should compare equal had different arity
    TupleLengthMismatch { expected: usize, actual: usize },
    /// Arrays that should compare equal need to be of the same length
    ArrayLengthMismatch { expected: usize, actual: usize },
    /// Only mutable values can be mutated
    IllegalMutation,
    /// Only certain types of values may be on the lhs of an assignment
    InvalidAssignment,
    /// Accessed fields must exist
    UnknownFieldAccess { target: Type, name: InternedSymbol },
    /// All struct fields must be present
    MissingStructField { name: InternedSymbol },
    /// No extra struct fields may be specified
    ExtraStructField { name: InternedSymbol },
    /// The "self" expression ay only be used in functions with a self parameter
    IllegalSelfUsage,
}

impl TypeErrorKind {
    pub fn get_substitutable_types_mut(&mut self) -> Vec<&mut Type> {
        match self {
            TypeErrorKind::TypeMismatch { expected, actual } => vec![expected, actual],
            TypeErrorKind::InvalidOperation { provided, .. } => vec![provided],
            TypeErrorKind::MissingReturnValue { expected } => vec![expected],
            TypeErrorKind::InfinitelyRecursiveType { .. }
            | TypeErrorKind::ArgumentLengthMismatch { .. }
            | TypeErrorKind::CannotInfer
            | TypeErrorKind::IllegalLoopControlFlow(_)
            | TypeErrorKind::InvalidCast { .. }
            | TypeErrorKind::TupleLengthMismatch { .. }
            | TypeErrorKind::ArrayLengthMismatch { .. }
            | TypeErrorKind::IllegalMutation
            | TypeErrorKind::InvalidAssignment
            | TypeErrorKind::UnknownFieldAccess { .. }
            | TypeErrorKind::MissingStructField { .. }
            | TypeErrorKind::ExtraStructField { .. }
            | TypeErrorKind::IllegalSelfUsage => vec![],
        }
    }
}

#[derive(Debug)]
enum TypeUsage {
    ArithmeticOperation,
    LogicalOperation,
    FieldAccess,
    FunctionCall,
    Deref,
}

#[derive(Debug)]
enum LoopControlFlowKind {
    Continue,
    Break,
}

impl<'tcx, 'hir> hir::visit::Visitor for TypeChecker<'tcx, 'hir> {
    /// Bind the types for function parameters
    fn visit_function_definition(
        &mut self,
        name: &hir::Path,
        signature: &hir::FunctionSignature,
        body: hir::BodyId,
    ) {
        hir::visit::walk_path(self, name);

        // Collect self type

        if let Some(self_ty) = self.type_context.compute_self_type(name, signature) {
            self.self_type.set(self_ty).unwrap();
        }

        // Collect parameter types
        hir::visit::walk_function_signature(self, signature);

        // Default return type is unit if none specified
        let return_ty = if let Some(r) = &signature.return_type {
            self.get_type(r.hir_id)
        } else {
            self.type_context.get_unit_type()
        };
        self.return_type.set(return_ty.clone()).unwrap();

        // Assign types to function parameters
        let body = self.type_context.module.get_body(body);
        for (name, ty) in body.params.iter().zip(signature.parameters.iter()) {
            self.copy_type_from(name.hir_id, ty.hir_id);
        }

        // Type check the function body
        hir::visit::walk_body(self, body.clone());

        // Validate that either the implicit return type matches the expected
        // type or that there are no code paths laeading to the end of the
        // function
        if let Some(last_expr) = &body.block.expression {
            // The body's implicit return type needs to match the function's signature

            let last_expr_ty = self.get_type(last_expr.hir_id);
            self.add_equality_constraint(
                return_ty,
                last_expr_ty,
                TypeConstraintOrigin {
                    span: if let Some(e) = &body.block.expression {
                        e.span
                    } else if let Some(r) = &signature.return_type {
                        r.span
                    } else {
                        // NOTE: this should never actually happen because this
                        // constraint would never be violated with both
                        // (both default to unit in that case and the constraint is
                        // upheld), but we need to provide a span here so just use
                        // the name bc thats fine
                        Span::INVALID
                    },
                    kind: TypeBoundary::ImplicitReturn,
                },
            );
        } else if let Some(ret) = &signature.return_type {
            // If there is no implicit return and a diverging path inside the
            // function, we can never reach the end of the body and don't need
            // to generate an error

            let has_explicit_return = body.block.statements.iter().any(|stmt| {
                // Any statement that propogates a never type up from any of its
                // subexpressions must have a return somewhere within it
                match &stmt.kind {
                    hir::StatementKind::Let(let_statement) => {
                        if let Some(initializer) = &let_statement.initializer
                            && self.get_type(initializer.hir_id).is_never()
                        {
                            return true;
                        }
                    }
                    hir::StatementKind::BareExpression(expression)
                    | hir::StatementKind::SemiExpression(expression) => {
                        if self.get_type(expression.hir_id).is_never() {
                            return true;
                        }
                    }
                }

                false
            });

            if !has_explicit_return {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        span: ret.span,
                        kind: TypeBoundary::ImplicitReturn,
                    },
                    kind: TypeErrorKind::MissingReturnValue {
                        expected: return_ty,
                    },
                });
            }
        }
    }

    fn visit_struct_field(&mut self, field: Rc<hir::StructField>) {
        hir::visit::walk_struct_field(self, field.clone());
        // FIXME: can we use the cached type info from when we indexed the struct?

        let computed_ty = self.type_context.compute_hir_type(field.ty.clone());
        self.insert_type(field.hir_id, computed_ty);
    }

    /// Precompute types in function parameters and local bindings
    fn visit_type(&mut self, ty: Rc<hir::Type>) {
        hir::visit::walk_type(self, ty.clone());

        let computed_ty = self.type_context.compute_hir_type(ty.clone());
        self.insert_type(ty.hir_id, computed_ty);
    }

    fn visit_path_segment(&mut self, segment: Rc<hir::PathSegment>) {
        if let hir::Resolution::Local(local_id) = &segment.resolution {
            self.copy_type_from(segment.hir_id, *local_id);
            return;
        }

        let computed_ty = self
            .type_context
            .compute_hir_resolution_type(segment.resolution);
        self.insert_type(segment.hir_id, computed_ty);
    }

    fn visit_let_statement(&mut self, let_stmt: Rc<hir::LetStatement>) {
        // 4 cases:
        //   1) no type no   initializer -> recoverable error
        //   2)    type no   initializer -> assign type to binding
        //   3) no type with initializer -> assign initializer type to binding
        //   4)    type with initializer -> assign type to binding + add constraint on initializer

        hir::visit::walk_let_statement(self, let_stmt.clone());

        // Compute and insert the explicit type
        let explicit_type = let_stmt.ty.as_ref().map(|ty| self.get_type(ty.hir_id));

        // Determine the type of the RHS expression
        let initializer_type = let_stmt
            .initializer
            .as_ref()
            .map(|init| self.get_type(init.hir_id));

        // Assign the type of the let based on the combination of explicit type
        // and initializer type using the rules we defined above
        match (explicit_type, initializer_type) {
            (None, None) => {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        span: let_stmt.span,
                        kind: TypeBoundary::LetStatement,
                    },
                    kind: TypeErrorKind::CannotInfer,
                });

                let error_ty = self.type_context.get_error_type();
                self.insert_type(let_stmt.hir_id, error_ty);
            }
            (None, Some(initializer)) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, initializer);
            }
            (Some(explicit), None) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, explicit);
            }
            (Some(explicit), Some(initializer)) => {
                self.add_equality_constraint(
                    explicit.clone(),
                    initializer,
                    TypeConstraintOrigin {
                        span: let_stmt.span,
                        kind: TypeBoundary::LetStatement,
                    },
                );
                self.insert_type(let_stmt.hir_id, explicit);
            }
        }
    }

    fn visit_struct_initializer_field(&mut self, field: Rc<hir::StructInitializerField>) {
        hir::visit::walk_struct_initializer_field(self, field.clone());

        self.copy_type_from(field.hir_id, field.value.hir_id);
    }

    fn visit_expression(&mut self, expression: Rc<hir::Expression>) {
        hir::visit::walk_expression(self, expression.clone());

        match &expression.kind {
            hir::ExpressionKind::Literal(literal) => {
                let ty = self.compute_type_for_literal(literal);
                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Path(path) => match path.resolution() {
                hir::Resolution::Definition(_, def_id) => {
                    let ty = self.type_context.def_id_to_type_map[def_id].clone();
                    self.insert_type(expression.hir_id, ty);
                }
                hir::Resolution::Local(local_id) => {
                    self.copy_type_from(expression.hir_id, *local_id);
                }
                hir::Resolution::IntrinsicFunction(_) => {
                    self.copy_type_from(expression.hir_id, path.segments.last().unwrap().hir_id);
                }
                _ => unreachable!("encountered type resolution in value namespace"),
            },
            hir::ExpressionKind::This => {
                let Some(self_ty) = self.self_type.get() else {
                    let err = self.type_context.get_error_type();
                    self.insert_type(expression.hir_id, err);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::SelfExpression,
                        },
                        kind: TypeErrorKind::IllegalSelfUsage,
                    });
                    return;
                };

                self.insert_type(expression.hir_id, self_ty.clone());
            }
            hir::ExpressionKind::Array(array_initializer) => match array_initializer {
                hir::ArrayInitializer::Repeated { value, length } => {
                    let value_ty = self.get_type(value.hir_id);

                    let ty = self.type_context.intern_type(TypeKind::Array {
                        ty: value_ty,
                        length: *length,
                    });

                    self.insert_type(expression.hir_id, ty);
                }
                hir::ArrayInitializer::Specific(expressions) => {
                    let expression_tys: Rc<[Type]> = expressions
                        .iter()
                        .map(|e| self.get_type(e.hir_id))
                        .collect();

                    let inner_ty = expression_tys
                        .first()
                        .expect("arrays must have at least one element for now")
                        .clone();

                    for (e, ty) in expressions.iter().zip(expression_tys.iter()).skip(1) {
                        self.add_equality_constraint(
                            inner_ty.clone(),
                            ty.clone(),
                            TypeConstraintOrigin {
                                span: e.span,
                                kind: TypeBoundary::ArrayInitializer,
                            },
                        );
                    }

                    let ty = self.type_context.intern_type(TypeKind::Array {
                        ty: inner_ty,
                        length: expression_tys.len(),
                    });

                    self.insert_type(expression.hir_id, ty);
                }
            },
            hir::ExpressionKind::Tuple(expressions) => {
                let expression_tys = expressions
                    .iter()
                    .map(|e| self.get_type(e.hir_id))
                    .collect();
                let ty = self
                    .type_context
                    .intern_type(TypeKind::Tuple(expression_tys));

                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Struct {
                name,
                fields: actual_fields,
            } => {
                let ty = self
                    .type_context
                    .compute_hir_resolution_type(*name.resolution());

                let TypeKind::Struct {
                    fields: expected_fields,
                    ..
                } = &*ty
                else {
                    unreachable!()
                };

                let expected_field_set: HashSet<InternedSymbol> =
                    HashSet::from_iter(expected_fields.iter().map(|f| f.name));
                let actual_field_set: HashSet<InternedSymbol> =
                    HashSet::from_iter(actual_fields.iter().map(|f| f.name.symbol));

                let expected_field_map: HashMap<InternedSymbol, Type> =
                    HashMap::from_iter(expected_fields.iter().map(|f| (f.name, f.ty.clone())));

                // check no missing fields

                for missing_field in expected_field_set.difference(&actual_field_set) {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::StructInitializer,
                        },
                        kind: TypeErrorKind::MissingStructField {
                            name: *missing_field,
                        },
                    });
                }

                // check no extra fields

                for extra_field in actual_field_set.difference(&expected_field_set) {
                    let field = actual_fields
                        .iter()
                        .find(|f| f.name.symbol == *extra_field)
                        .unwrap();

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: field.span,
                            kind: TypeBoundary::StructInitializer,
                        },
                        kind: TypeErrorKind::ExtraStructField { name: *extra_field },
                    });
                }

                // check all fields are expected type

                for field in actual_fields.iter() {
                    let field_ty = self.get_type(field.hir_id);
                    let expected_ty = expected_field_map.get(&field.name.symbol).unwrap().clone();

                    self.add_equality_constraint(
                        field_ty,
                        expected_ty,
                        TypeConstraintOrigin {
                            span: field.span,
                            kind: TypeBoundary::StructInitializer,
                        },
                    );
                }

                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Block(block) => {
                self.copy_type_from(expression.hir_id, block.hir_id);
            }
            hir::ExpressionKind::FieldAccess {
                target,
                name,
                is_method_call,
            } => {
                let target_ty = self.get_type(target.hir_id);

                match &*target_ty {
                    TypeKind::Str => match (name.symbol.value(), *is_method_call) {
                        ("ptr", false) => {
                            let u8_ty = self
                                .type_context
                                .get_primitive_type(PrimitiveKind::UInt(UIntKind::U8));
                            let ty = self.type_context.intern_type(TypeKind::Pointer(u8_ty));

                            self.insert_type(expression.hir_id, ty);
                        }
                        ("len", false) => {
                            let ty = self
                                .type_context
                                .get_primitive_type(PrimitiveKind::UInt(UIntKind::USize));

                            self.insert_type(expression.hir_id, ty);
                        }
                        _ => {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: target.span,
                                    kind: TypeBoundary::FieldAccess,
                                },
                                kind: TypeErrorKind::UnknownFieldAccess {
                                    target: target_ty,
                                    name: name.symbol,
                                },
                            });
                        }
                    },
                    TypeKind::Pointer(_) => self
                        .type_context
                        .report_bug(expression.span, "todo: pointer auto deref"),
                    TypeKind::Slice(inner_ty) => match (name.symbol.value(), *is_method_call) {
                        ("ptr", false) => {
                            let ty = self
                                .type_context
                                .intern_type(TypeKind::Pointer(inner_ty.clone()));

                            self.insert_type(expression.hir_id, ty);
                        }
                        ("len", false) => {
                            let ty = self
                                .type_context
                                .get_primitive_type(PrimitiveKind::UInt(UIntKind::USize));

                            self.insert_type(expression.hir_id, ty);
                        }
                        _ => {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: target.span,
                                    kind: TypeBoundary::FieldAccess,
                                },
                                kind: TypeErrorKind::UnknownFieldAccess {
                                    target: target_ty,
                                    name: name.symbol,
                                },
                            });
                        }
                    },
                    TypeKind::Array { ty, length } => todo!(),
                    TypeKind::Tuple(items) => todo!(),
                    TypeKind::Struct {
                        def_id,
                        name: _,
                        fields,
                    } => {
                        if *is_method_call {
                            let Some(resolution) = self
                                .type_context
                                .module
                                .get_owners()
                                .filter_map(|owner_id| {
                                    self.type_context
                                        .module
                                        .get_owner(owner_id)
                                        .node()
                                        .as_item()
                                })
                                .find_map(|item| {
                                    let hir::ItemKind::Function {
                                        name: fn_name,
                                        ..
                                    } = &item.kind
                                    else {
                                        return None;
                                    };

                                    if !(matches!(fn_name.segments[0].resolution, hir::Resolution::Definition(_, id) if id == *def_id)
                                        && fn_name.segments[1].identifier.symbol == name.symbol)
                                    {
                                        return None;
                                    }

                                    Some(*fn_name.resolution())
                                })
                            else {
                                let err = self.type_context.get_error_type();
                                self.insert_type(expression.hir_id, err);

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: name.span,
                                        kind: TypeBoundary::FieldAccess,
                                    },
                                    kind: TypeErrorKind::UnknownFieldAccess {
                                        target: target_ty.clone(),
                                        name: name.symbol,
                                    },
                                });
                                return;
                            };

                            let ty = self.type_context.compute_hir_resolution_type(resolution);

                            self.method_resolution_map.insert(
                                expression.hir_id.local_id,
                                resolution.as_function_definition().unwrap(),
                            );
                            self.insert_type(expression.hir_id, ty);
                        } else {
                            let Some(field) = fields.iter().find(|f| f.name == name.symbol) else {
                                let err = self.type_context.get_error_type();
                                self.insert_type(expression.hir_id, err);

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: name.span,
                                        kind: TypeBoundary::FieldAccess,
                                    },
                                    kind: TypeErrorKind::UnknownFieldAccess {
                                        target: target_ty.clone(),
                                        name: name.symbol,
                                    },
                                });
                                return;
                            };

                            self.insert_type(expression.hir_id, field.ty.clone());
                        }
                    }
                    TypeKind::Error => todo!(),
                    _ => {
                        // All other types do not support field access
                        let err = self.type_context.get_error_type();
                        self.insert_type(expression.hir_id, err);

                        self.errors.push(TypeError {
                            origin: TypeConstraintOrigin {
                                span: target.span,
                                kind: TypeBoundary::FieldAccess,
                            },
                            kind: TypeErrorKind::InvalidOperation {
                                attempted_usage: TypeUsage::FieldAccess,
                                provided: target_ty.clone(),
                            },
                        });
                    }
                }
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                // check that the target of the call is a function pointer

                let target_ty = self.get_type(target.hir_id);

                let TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic,
                } = &*target_ty
                else {
                    let err = self.type_context.get_error_type();
                    self.insert_type(expression.hir_id, err);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: target.span,
                            kind: TypeBoundary::FunctionCall,
                        },
                        kind: TypeErrorKind::InvalidOperation {
                            attempted_usage: TypeUsage::FunctionCall,
                            provided: target_ty.clone(),
                        },
                    });
                    return;
                };

                // expression has the same type as the function's return type
                self.insert_type(expression.hir_id, return_type.clone());

                let mut expected_parameters = &parameters[..];

                // for method calls, the self argument is passed implicitly
                if let hir::ExpressionKind::FieldAccess {
                    is_method_call: true,
                    ..
                } = &target.kind
                {
                    expected_parameters = &parameters[1..];
                }

                // Make sure the passed number of arguments matches the expected
                // number (allowing variadics if applicable)
                if arguments.len() < expected_parameters.len()
                    || (arguments.len() > expected_parameters.len() && !*is_variadic)
                {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::FunctionCall,
                        },
                        kind: TypeErrorKind::ArgumentLengthMismatch {
                            expected: expected_parameters.len(),
                            actual: arguments.len(),
                        },
                    });
                    return;
                }

                // check that argument types match the target's call signature
                for (parameter_ty, argument) in expected_parameters.iter().zip(arguments.iter()) {
                    let argument_ty = self.get_type(argument.hir_id);

                    self.add_equality_constraint(
                        parameter_ty.clone(),
                        argument_ty,
                        TypeConstraintOrigin {
                            span: argument.span,
                            kind: TypeBoundary::FunctionArgument,
                        },
                    );
                }
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);

                match operator.class() {
                    // If this is an arithmetic operator, require that both
                    // types are arithmetic
                    BinaryOperatorClass::Arithmetic => {
                        let mut error = false;

                        if !lhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::BinaryOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::BinaryOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }

                        // For arithmetic operations the result is always the same as the inputs
                        self.insert_type(expression.hir_id, lhs_ty.clone());

                        // pointer arithmetic

                        match (&*lhs_ty, &*rhs_ty) {
                            (
                                TypeKind::Pointer(_) | TypeKind::Any,
                                TypeKind::Infer(TypeVariable::Int(_)),
                            ) => {
                                let usize_ty = self
                                    .type_context
                                    .get_primitive_type(PrimitiveKind::UInt(UIntKind::USize));

                                self.add_equality_constraint(
                                    rhs_ty.clone(),
                                    usize_ty,
                                    TypeConstraintOrigin {
                                        span: expression.span,
                                        kind: TypeBoundary::BinaryOp,
                                    },
                                );
                                return;
                            }
                            (
                                TypeKind::Pointer(_) | TypeKind::Any,
                                TypeKind::UnsignedInteger(UIntKind::USize),
                            ) => return,
                            _ => {}
                        }
                    }
                    // If this is a logical operator, require that both types
                    // are bools
                    class @ (BinaryOperatorClass::Logical | BinaryOperatorClass::Comparison) => {
                        let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                        // should this be a type constraint? maybe but it seems
                        // like we can do all the logic here instead and
                        // possibly report better errors
                        if class == BinaryOperatorClass::Logical {
                            let mut error = false;

                            if !lhs_ty.is_bool() {
                                error = true;

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: lhs.span,
                                        kind: TypeBoundary::BinaryOp,
                                    },
                                    kind: TypeErrorKind::InvalidOperation {
                                        attempted_usage: TypeUsage::LogicalOperation,
                                        provided: lhs_ty.clone(),
                                    },
                                });
                            }

                            if !rhs_ty.is_bool() {
                                error = true;

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: rhs.span,
                                        kind: TypeBoundary::BinaryOp,
                                    },
                                    kind: TypeErrorKind::InvalidOperation {
                                        attempted_usage: TypeUsage::LogicalOperation,
                                        provided: rhs_ty.clone(),
                                    },
                                });
                            }

                            if error {
                                let error_ty = self.type_context.get_error_type();
                                self.insert_type(expression.hir_id, error_ty);

                                return;
                            }
                        }

                        // For logical operations, the result is always a
                        // boolean no matter what
                        self.insert_type(expression.hir_id, bool_ty);
                    }
                }

                // For operators like && and ||, the types need to be
                // bools. For operators like == and !=, the types need
                // to be the same. In either case we need to add this
                // equality constraint.
                self.add_equality_constraint(
                    lhs_ty.clone(),
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::BinaryOp,
                    },
                );
            }
            hir::ExpressionKind::Unary { operator, operand } => {
                let operand_ty = self.get_type(operand.hir_id);

                match operator {
                    UnaryOperatorKind::Deref => {
                        let TypeKind::Pointer(inner_ty) = &*operand_ty else {
                            if operand_ty.is_error() {
                                self.copy_type_from(expression.hir_id, operand.hir_id);
                                return;
                            }

                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::Deref,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::Deref,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        };

                        self.insert_type(expression.hir_id, inner_ty.clone());
                    }
                    UnaryOperatorKind::AddressOf { is_mutable } => {
                        // FIXME: \/ \/ \/ implement this \/ \/ \/
                        // assert!(!is_mutable, "type check mutability");

                        // TODO: can all types have their address taken? this is
                        // unclear. what about error types? what about zero
                        // sized types? (rust returns 0x1 for ZSTs).

                        // only some values may have their addresses taken. For
                        // example, local variables, statics, field members, and
                        // subscript expressions. It may be possible to take the
                        // address of some intermediate values, but that adds
                        // constraints on our LIR generation and optimization
                        // since it forces the intermediate to be spilled on to
                        // the stack.

                        // if operand_ty.is_never() {
                        //     unreachable!("cannot take the address of a never type")
                        // }

                        // if operand_ty.is_unit() {
                        //     unreachable!("cannot take the address of a unit type")
                        // }

                        // match &operand.kind {
                        //     hir::ExpressionKind::Literal(literal) => todo!(),
                        //     hir::ExpressionKind::Path(path) => todo!(),
                        //     hir::ExpressionKind::This => todo!(),
                        //     hir::ExpressionKind::Array(array_initializer) => todo!(),
                        //     hir::ExpressionKind::Tuple(expressions) => todo!(),
                        //     hir::ExpressionKind::Struct { name, fields } => todo!(),
                        //     hir::ExpressionKind::Block(block) => todo!(),
                        //     hir::ExpressionKind::FieldAccess {
                        //         target,
                        //         name,
                        //         is_method_call,
                        //     } => todo!(),
                        //     hir::ExpressionKind::FunctionCall { target, arguments } => todo!(),
                        //     hir::ExpressionKind::Binary { lhs, operator, rhs } => todo!(),
                        //     hir::ExpressionKind::Unary { operator, operand } => todo!(),
                        //     hir::ExpressionKind::Cast { expression, ty } => todo!(),
                        //     hir::ExpressionKind::If {
                        //         condition,
                        //         positive,
                        //         negative,
                        //     } => todo!(),
                        //     hir::ExpressionKind::While { condition, block } => todo!(),
                        //     hir::ExpressionKind::Assignment { lhs, rhs } => todo!(),
                        //     hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                        //         todo!()
                        //     }
             
                        //     _ => todo!()
                        // }

                        let pointer_ty =
                            self.type_context.intern_type(TypeKind::Pointer(operand_ty));
                        self.insert_type(expression.hir_id, pointer_ty);
                    }
                    UnaryOperatorKind::LogicalNot => {
                        if !operand_ty.is_bool() {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::LogicalOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        }

                        self.insert_type(expression.hir_id, operand_ty);
                    }
                    UnaryOperatorKind::BitwiseNot | UnaryOperatorKind::Negate => {
                        if !operand_ty.is_arithmetic() {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::ArithmeticOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        }

                        self.insert_type(expression.hir_id, operand_ty);
                    }
                }
            }
            hir::ExpressionKind::Cast {
                expression: castee,
                ty,
            } => {
                let castee_ty = self.get_type(castee.hir_id);
                let target_ty = self.get_type(ty.hir_id);

                // We know that the target type cannot have any free type
                // variables because it can only be a named concrete type. This
                // may change however if we add a "typeof" mechanism or
                // equivalent.
                self.add_cast_constraint(
                    castee_ty,
                    target_ty.clone(),
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::Cast,
                    },
                );
                self.insert_type(expression.hir_id, target_ty);
            }
            hir::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                let condition_ty = self.get_type(condition.hir_id);
                let positive_ty = self.get_type(positive.hir_id);

                if !condition_ty.is_bool() && !condition_ty.is_error() {
                    let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::IfCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: bool_ty,
                            actual: condition_ty,
                        },
                    });
                }

                if let Some(n) = negative.as_ref() {
                    let negative_ty = self.get_type(n.hir_id);

                    // If either branch diverges, we dont care to make sure that
                    // the types match
                    if !positive_ty.is_never() && !negative_ty.is_never() {
                        self.add_equality_constraint(
                            positive_ty.clone(),
                            negative_ty,
                            TypeConstraintOrigin {
                                // TODO: use the span of the last expr in the block chain (lol)
                                span: n.span,
                                kind: TypeBoundary::IfBlock,
                            },
                        );
                    }
                }

                self.insert_type(expression.hir_id, positive_ty);
            }
            hir::ExpressionKind::While { condition, block } => {
                let condition_ty = self.get_type(condition.hir_id);
                let block_ty = self.get_type(block.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                if !condition_ty.is_bool() && !condition_ty.is_error() {
                    let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::WhileCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: bool_ty,
                            actual: condition_ty,
                        },
                    });
                }

                if !block_ty.is_unit() && !block_ty.is_never() {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::WhileCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: unit_ty.clone(),
                            actual: block_ty,
                        },
                    });
                }

                self.insert_type(expression.hir_id, unit_ty);
            }
            hir::ExpressionKind::Assignment { lhs, rhs } => {
                let mut error = None;

                match &lhs.kind {
                    hir::ExpressionKind::Path(path) => match path.resolution() {
                        hir::Resolution::Local(id) => {
                            let local = self.type_context.module.get_owner(self.owner_id).nodes
                                [*id]
                                .node
                                .as_let_statement()
                                .unwrap();

                            if !local.is_mutable {
                                error = Some(TypeErrorKind::IllegalMutation)
                            }
                        }
                        hir::Resolution::Definition(DefinitionKind::Static, def_id) => {
                            let hir::ItemKind::Static {
                                is_mutable,
                                name,
                                ty,
                                initializer,
                            } = &self
                                .type_context
                                .module
                                .get_owner(*def_id)
                                .node()
                                .as_item()
                                .unwrap()
                                .kind
                            else {
                                unreachable!()
                            };

                            if !is_mutable {
                                error = Some(TypeErrorKind::IllegalMutation)
                            }
                        }
                        _ => error = Some(TypeErrorKind::InvalidAssignment),
                    },
                    hir::ExpressionKind::Unary {
                        operator: UnaryOperatorKind::Deref,
                        operand,
                    } => {
                        // FIXME: check if deref can be mutated

                        let operand_ty = self.get_type(operand.hir_id);

                        if operand_ty.is_error() {
                            return;
                        }

                        if !matches!(&*operand_ty, TypeKind::Pointer(_)) {
                            error = Some(TypeErrorKind::InvalidAssignment);
                        }
                    }
                    hir::ExpressionKind::FieldAccess {
                        target,
                        name,
                        is_method_call,
                    } => {
                        // FIXME: check if value can be mutated
                    }
                    _ => error = Some(TypeErrorKind::InvalidAssignment),
                }

                if let Some(kind) = error {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: lhs.span,
                            kind: TypeBoundary::Assignment,
                        },
                        kind,
                    });

                    let error_ty = self.type_context.get_error_type();
                    self.insert_type(expression.hir_id, error_ty);
                    return;
                }

                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                self.add_equality_constraint(
                    lhs_ty,
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::Assignment,
                    },
                );

                self.insert_type(expression.hir_id, unit_ty);
            }
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                match operator.class() {
                    // If this is an arithmetic operator, require that both
                    // types are arithmetic
                    AssignmentOperatorClass::Arithmetic => {
                        let mut error = false;

                        if !lhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }
                    }
                    // If this is a logical operator, require that both
                    // types are bools
                    AssignmentOperatorClass::Logical => {
                        let mut error = false;

                        if !lhs_ty.is_bool() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_bool() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }
                    }
                }

                // For operators like &&= and ||=, the types need to be
                // bools. For operators like += and -=, the types need
                // to be the same. In either case we need to add this
                // equality constraint.
                self.add_equality_constraint(
                    lhs_ty.clone(),
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::OpAssignment,
                    },
                );
                self.insert_type(expression.hir_id, unit_ty);
            }
            kind @ (hir::ExpressionKind::Break | hir::ExpressionKind::Continue) => {
                let kind = if matches!(kind, hir::ExpressionKind::Break) {
                    LoopControlFlowKind::Break
                } else {
                    LoopControlFlowKind::Continue
                };

                if !self.within_loop {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::LoopControlFlow,
                        },
                        kind: TypeErrorKind::IllegalLoopControlFlow(kind),
                    });
                }

                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Return(value) => {
                let return_ty = self.return_type.get().unwrap().clone();

                if let Some(v) = value {
                    let value_ty = self.get_type(v.hir_id);

                    if value_ty != return_ty {
                        self.add_equality_constraint(
                            value_ty,
                            return_ty,
                            TypeConstraintOrigin {
                                span: expression.span,
                                kind: TypeBoundary::ExplicitReturn,
                            },
                        );
                    }
                } else if !return_ty.is_unit() {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::ExplicitReturn,
                        },
                        kind: TypeErrorKind::MissingReturnValue {
                            expected: return_ty,
                        },
                    });
                }

                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
        }
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, context: hir::visit::BlockContext) {
        // Add to loop context if necessary
        {
            let previous = self.within_loop;
            self.within_loop = self.within_loop || context == hir::visit::BlockContext::Loop;

            hir::visit::walk_block(self, block.clone());

            self.within_loop = previous;
        }

        for stmt in block.statements.iter() {
            let hir::StatementKind::BareExpression(e) = &stmt.kind else {
                continue;
            };

            let expr_ty = self.get_type(e.hir_id);
            let unit_ty = self.type_context.get_unit_type();

            if !expr_ty.is_unit() && !expr_ty.is_never() && !expr_ty.is_error() {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        // TODO: use the span of the last expr in the block
                        span: e.span,
                        kind: TypeBoundary::BareExpression,
                    },
                    kind: TypeErrorKind::TypeMismatch {
                        expected: unit_ty,
                        actual: expr_ty,
                    },
                });
            }
        }

        if let Some(e) = &block.expression {
            self.copy_type_from(block.hir_id, e.hir_id);
        } else {
            let unit_ty = self.type_context.get_unit_type();
            self.insert_type(block.hir_id, unit_ty);
        }
    }

    fn visit_statement(&mut self, statement: Rc<hir::Statement>) {
        hir::visit::walk_statement(self, statement.clone());

        let unit_ty = self.type_context.get_unit_type();
        self.insert_type(statement.hir_id, unit_ty);
    }
}

#[derive(Debug)]
pub struct ModuleTypeCheckResults {
    pub item_types: BTreeMap<hir::LocalDefId, Type>,
    pub function_results: BTreeMap<hir::LocalDefId, TypeCheckResults>,
}

impl ModuleTypeCheckResults {
    #[track_caller]
    pub fn get_type(&self, hir_id: hir::HirId) -> Type {
        self.function_results[&hir_id.owner].node_types[&hir_id.local_id].clone()
    }
}

#[derive(Debug)]
pub struct TypeCheckResults {
    pub owner_id: hir::LocalDefId,
    pub node_types: BTreeMap<hir::ItemLocalId, Type>,
    pub method_resolutions: BTreeMap<hir::ItemLocalId, hir::LocalDefId>,
    pub self_type: Option<Type>,
}

pub fn type_check_module(module: &hir::Module, source_file: &SourceFile) -> ModuleTypeCheckResults {
    let mut ctx = TypeContext::new(module, source_file);

    // Compute types for top level items we might reference in body contexts
    let mut global_indexer = GlobalTypeEnvironmentIndexer {
        type_context: &mut ctx,
    };
    hir::visit::walk_module(&mut global_indexer, module);

    let mut function_results = BTreeMap::new();

    let mut tainted_with_errors = false;

    // Check the content of bodies and assign types to all nodes
    for owner_id in module.get_owners() {
        let mut body_ctx = TypeChecker {
            type_context: &mut ctx,
            owner_id,
            node_to_type_map: BTreeMap::new(),
            method_resolution_map: BTreeMap::new(),
            constraints: Vec::new(),
            errors: Vec::new(),
            within_loop: false,
            self_type: OnceCell::new(),
            return_type: OnceCell::new(),
            next_integer_variable_id: IntVariableId::new(0),
            next_float_variable_id: FloatVariableId::new(0),
        };

        let hir::OwnerNode::Item(item) = module.get_owner(owner_id).node();
        hir::visit::walk_item(&mut body_ctx, item);

        match body_ctx.into_output() {
            Ok(output) => {
                for (id, ty) in &output.node_types {
                    if ty.is_error() {
                        eprintln!(
                            "ERROR: unknown type left after type checking without any errors being reported (local_def_id = {id:?})"
                        );
                        tainted_with_errors = true;
                    }
                }

                function_results.insert(owner_id, output);
            }
            Err(errors) => {
                tainted_with_errors = true;

                for err in errors {
                    ctx.report_error(err);
                }
            }
        }
    }

    if tainted_with_errors {
        std::process::exit(1);
    }

    ModuleTypeCheckResults {
        item_types: ctx.def_id_to_type_map,
        function_results,
    }
}
