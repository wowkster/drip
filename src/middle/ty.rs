use std::rc::Rc;

use colored::Colorize;
use hashbrown::HashSet;

use crate::{
    frontend::intern::InternedSymbol,
    index::{Index, simple_index},
    middle::{
        hir,
        primitive::{FloatKind, IntKind, UIntKind},
    },
};

#[doc(hidden)]
mod private {
    #[doc(hidden)]
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct PrivateZst;
}

/// Thin pointer to an interned type kind. Do not construct directly. Instead,
/// use [`TypeContext::insert_type`]
///
/// FIXME: we could use referential equality here since types are interned and
/// guaranteed to be unique
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Type(Rc<TypeKind>, private::PrivateZst);

impl Type {
    pub fn new_from_reference_only_for_interning(kind: Rc<TypeKind>) -> Self {
        Self(kind, private::PrivateZst)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// !
    Never,
    /// ()
    Unit,
    // true, false
    Bool,
    // 'a', '\n'
    Char,
    /// i32, i64, etc.
    Integer(IntKind),
    /// u8, u32, etc.
    UnsignedInteger(UIntKind),
    /// f32, f64
    Float(FloatKind),
    /// str
    ///
    /// A pointer and length to some UTF-8 data
    Str,
    /// cstr
    ///
    /// A raw pointer which is guaranteed to point to a valid, null terminated,
    /// ASCII C-style string
    CStr,
    /// *T
    ///
    /// A raw pointer to a T
    Pointer(Type),
    /// [T]
    ///
    /// A pointer and length to some amount of T's
    Slice(Type),
    /// [T; <length>]
    ///
    /// A raw pointer to a fixed size allocation of T's
    Array {
        ty: Type,
        length: usize,
    },
    /// (f32, u8, str)
    ///
    /// A fixed size list of different types
    Tuple(Rc<[Type]>),
    /// struct T {
    ///     a: i32,
    ///     b: f64,
    ///     b: (bool, String)
    /// }
    ///
    /// A user defined type with named fields
    Struct {
        /// Allows structs with the same layout to be distinct types
        def_id: hir::LocalDefId,
        name: InternedSymbol,
        fields: Rc<[StructField]>,
    },
    /// enum T {
    ///     A.
    ///     B.
    ///     C.
    /// }
    ///
    /// A user defined discrete set of allowed values
    Enum {
        def_id: hir::LocalDefId,
        name: InternedSymbol,
    },
    /// fn(i32, str, *T) -> u8
    ///
    /// A raw pointer to a function body
    FunctionPointer {
        parameters: Rc<[Type]>,
        return_type: Type,
        is_variadic: bool,
    },
    /// *any
    ///
    /// A raw pointer to some data of an unknown type. `any` can not be used on
    /// its own since it has an unknown size, so it must be used as a pointer.
    Any,
    /// An unresolved type variable whose type must be inferred
    Infer(TypeVariable),
    /// The type which is created as a result of some illegal operation which we
    /// can't compute the type of. If you find this in your type, there is no
    /// use emitting another error since one has already been created.
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: InternedSymbol,
    pub ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeVariable {
    Int(IntVariableId),
    Float(FloatVariableId),
}

simple_index! {
    /// An integral type variable to be inferred
    pub struct IntVariableId;
}

simple_index! {
    /// A floating point type variable to be inferred
    pub struct FloatVariableId;
}

impl core::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Type").field(&self.0).finish()
    }
}

impl core::ops::Deref for Type {
    type Target = TypeKind;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl TypeKind {
    pub fn is_arithmetic(&self) -> bool {
        match self {
            TypeKind::Char
            | TypeKind::Integer(_)
            | TypeKind::UnsignedInteger(_)
            | TypeKind::Float(_)
            | TypeKind::Infer(_)
            | TypeKind::Pointer(_)
            | TypeKind::Any => true,
            TypeKind::Never
            | TypeKind::Unit
            | TypeKind::Bool
            | TypeKind::Slice(_)
            | TypeKind::Str
            | TypeKind::CStr
            | TypeKind::Array { .. }
            | TypeKind::Tuple(_)
            | TypeKind::Struct { .. }
            | TypeKind::Enum { .. }
            | TypeKind::FunctionPointer { .. }
            | TypeKind::Error => false,
        }
    }

    pub fn is_integer_like(&self) -> bool {
        matches!(
            self,
            TypeKind::Integer(_)
                | TypeKind::UnsignedInteger(_)
                | TypeKind::Infer(TypeVariable::Int(_))
        )
    }

    pub fn is_float_like(&self) -> bool {
        matches!(
            self,
            TypeKind::Float(_) | TypeKind::Infer(TypeVariable::Float(_))
        )
    }

    pub fn is_pointer_like(&self) -> bool {
        matches!(self, TypeKind::Pointer(_) | TypeKind::Any)
    }

    pub fn is_never(&self) -> bool {
        matches!(self, TypeKind::Never)
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, TypeKind::Unit)
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, TypeKind::Bool)
    }

    pub fn is_error(&self) -> bool {
        matches!(self, TypeKind::Error)
    }

    pub fn is_struct(&self) -> bool {
        matches!(self, TypeKind::Struct { .. })
    }

    pub fn is_aggregate(&self) -> bool {
        matches!(
            self,
            TypeKind::Str { .. }
                | TypeKind::Slice { .. }
                | TypeKind::Tuple { .. }
                | TypeKind::Struct { .. }
                | TypeKind::Array { .. }
        )
    }

    /// Collects the list of free type variables in this type, traversing
    /// recursive inner types if necessary
    pub fn free_type_variables(&self) -> HashSet<TypeVariable> {
        match self {
            TypeKind::Never
            | TypeKind::Unit
            | TypeKind::Bool
            | TypeKind::Char
            | TypeKind::Integer(_)
            | TypeKind::UnsignedInteger(_)
            | TypeKind::Float(_)
            | TypeKind::Str
            | TypeKind::CStr
            | TypeKind::Enum { .. }
            | TypeKind::Any
            | TypeKind::Error => HashSet::new(),
            TypeKind::Pointer(inner)
            | TypeKind::Slice(inner)
            | TypeKind::Array { ty: inner, .. } => inner.free_type_variables(),
            TypeKind::Struct { fields, .. } => {
                let mut res = HashSet::new();

                for field in fields.iter() {
                    res.extend(field.ty.free_type_variables());
                }

                res
            }
            TypeKind::Tuple(types) => {
                let mut res = HashSet::new();

                for ty in types.iter() {
                    res.extend(ty.free_type_variables());
                }

                res
            }
            TypeKind::FunctionPointer {
                parameters,
                return_type,
                ..
            } => {
                let mut res = HashSet::new();

                for param in parameters.iter() {
                    res.extend(param.free_type_variables());
                }

                res.extend(return_type.free_type_variables());

                res
            }
            TypeKind::Infer(type_variable) => HashSet::from([*type_variable]),
        }
    }
}

impl core::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Never => write!(f, "!"),
            Self::Unit => write!(f, "()"),
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::Integer(int_kind) => write!(f, "{int_kind}"),
            Self::UnsignedInteger(uint_kind) => write!(f, "{uint_kind}"),
            Self::Float(float_kind) => write!(f, "{float_kind}"),
            Self::Str => write!(f, "str"),
            Self::CStr => write!(f, "cstr"),
            Self::Pointer(ty) => write!(f, "*{}", **ty),
            Self::Slice(ty) => write!(f, "[{}]", **ty),
            Self::Array { ty, length } => write!(f, "[{}; {length}]", **ty),
            Self::Tuple(types) => {
                write!(f, "(")?;
                for (i, ty) in types.iter().enumerate() {
                    write!(f, "{}", **ty)?;

                    if i != types.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Self::Struct { name, .. } | Self::Enum { name, .. } => {
                write!(f, "{name}")
            }
            Self::FunctionPointer {
                parameters,
                return_type,
                is_variadic,
            } => {
                // fn (i32, bool) -> ()

                write!(f, "fn (")?;

                for (i, ty) in parameters.iter().enumerate() {
                    write!(f, "{}", **ty)?;

                    if i != parameters.len() - 1 || *is_variadic {
                        write!(f, ", ")?;
                    }
                }
                if *is_variadic {
                    write!(f, "...")?;
                }
                write!(f, ") -> ")?;
                write!(f, "{}", *return_type)
            }
            Self::Any => write!(f, "*any"),
            Self::Infer(type_variable) => match type_variable {
                TypeVariable::Int(id) => write!(f, "{{integer@{}}}", id.index()),
                TypeVariable::Float(id) => write!(f, "{{float@{}}}", id.index()),
            },
            Self::Error => write!(f, "{{unknown}}"),
        }
    }
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.colored().yellow())
    }
}

impl From<Type> for colored::ColoredString {
    fn from(s: Type) -> Self {
        (*s).to_string().into()
    }
}

impl Type {
    pub fn colored(&self) -> colored::ColoredString {
        self.clone().into()
    }
}
