//! LIR (Low-level Intermediate Representation). In this form, many abstract
//! concepts like loops and conditionals are simplified to labels and jumps,
//! expression trees are flattened into ordered post fix operations, etc.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    frontend::{
        ast::{BinaryOperatorKind, UnaryOperatorKind},
        intern::InternedSymbol,
    },
    index::simple_index,
    middle::{
        hir,
        primitive::{FloatKind, IntKind, UIntKind},
    },
};

pub mod hir_lowering;
pub mod pretty_print;

#[derive(Debug)]
pub struct Module {
    pub function_definitions: BTreeMap<hir::LocalDefId, FunctionDefinition>,
    pub static_definitions: BTreeMap<hir::LocalDefId, StaticDefinition>,
    pub static_strings: BTreeMap<StaticLabelId, InternedSymbol>,
    pub static_c_strings: BTreeMap<StaticLabelId, InternedSymbol>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub symbol_name: InternedSymbol,
    /// Allocated virtual registers used to store temporary data
    pub registers: BTreeMap<RegisterId, Register>,
    /// The register argument used to return a struct from the function by value
    pub struct_return: Option<RegisterId>,
    /// The registers holding the arguments to the function (implicitly defined)
    pub arguments: Vec<RegisterId>,
    pub blocks: BTreeMap<BlockId, Block>,
}

impl FunctionDefinition {
    pub fn type_of_operand(&self, operand: Operand) -> Type {
        match operand {
            Operand::Immediate(immediate) => match immediate {
                Immediate::Int(_, integer_width) => Type::Integer(integer_width),
                Immediate::Float(_, float_width) => Type::Float(float_width),
                Immediate::Bool(_) => Type::Integer(IntegerWidth::I8),
                Immediate::AnonymousStaticLabel(_)
                | Immediate::NamedStaticLabel(_)
                | Immediate::FunctionLabel(_) => Type::Pointer,
            },
            Operand::Register(register_id) => self.registers[&register_id].ty.clone(),
        }
    }
}

#[derive(Debug)]
pub struct StaticDefinition {
    pub symbol_name: InternedSymbol,
    pub layout: Layout,
}

#[derive(Debug)]
pub struct Block {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub predecessors: BTreeSet<BlockId>,
}

impl Block {
    pub fn returns(&self) -> bool {
        self.instructions
            .last()
            .is_some_and(|i| matches!(i, Instruction::Return { .. }))
    }
}

simple_index! {
    /// Identifies an LIR block
    pub struct BlockId;
}

impl BlockId {
    pub const ZERO: Self = Self(0);
}

/// A temporary virtual register of some size and alignment
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Register {
    pub id: RegisterId,
    pub ty: Type,
}

simple_index! {
    /// Identifies a virtual LIR register which holds a temporary value
    pub struct RegisterId;
}

/// A representation of types within the LIR. This is significantly simplified
/// compared to the types coming from the HIR since we dont need as much rich
/// type information at this stage.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Integer(IntegerWidth),
    Float(FloatWidth),
    Pointer,
    Struct(Struct),
    Array(Rc<Type>, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntegerWidth {
    I8,
    I16,
    I32,
    I64,
}

impl From<IntKind> for IntegerWidth {
    fn from(value: IntKind) -> Self {
        match value {
            IntKind::I8 => Self::I8,
            IntKind::I16 => Self::I16,
            IntKind::I32 => Self::I32,
            IntKind::I64 | IntKind::ISize => Self::I64,
        }
    }
}

impl From<UIntKind> for IntegerWidth {
    fn from(value: UIntKind) -> Self {
        match value {
            UIntKind::U8 => Self::I8,
            UIntKind::U16 => Self::I16,
            UIntKind::U32 => Self::I32,
            UIntKind::U64 | UIntKind::USize => Self::I64,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatWidth {
    F32,
    F64,
}

impl From<FloatKind> for FloatWidth {
    fn from(value: FloatKind) -> Self {
        match value {
            FloatKind::F32 => Self::F32,
            FloatKind::F64 => Self::F64,
        }
    }
}

/// Represents an anonymous structure made up of some list of types. This is a
/// separate structure to more easily allow computing of struct field layouts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Struct(pub Rc<[Type]>);

impl Struct {
    pub fn slice() -> Struct {
        Struct(
            [
                // ptr
                Type::Pointer,
                // length
                Type::Integer(IntegerWidth::I64),
            ]
            .into(),
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    LoadMem {
        /// Register type size determines the number of bytes to copy. Must be 8
        /// bytes or less.
        destination: RegisterId,
        /// Must be a pointer type
        source: Operand,
    },
    StoreMem {
        /// Must be a pointer type
        destination: Operand,
        /// Type size must be less than or equal to 8 bytes. For larger stores,
        /// use memcpy.
        source: Operand,
    },
    /// Allocates room for a type on the stack. The destination register will
    /// store a pointer to the allocated space. Type size may be zero, but
    /// pointers are not guaranteed to be unique in this case.
    AllocStack {
        /// Must have pointer type
        destination: RegisterId,
        /// Determines the and size and alignment of the allocation
        ty: Type,
    },
    /// Stores a pointer in the destination register to a particular field of a
    /// structure. Effectively computes `destination = source + offset_of(ty, index)` and
    /// stores the result.
    GetStructElementPointer {
        /// Must be a pointer type
        destination: RegisterId,
        /// Must be a pointer type
        source: Operand,
        /// The structure layout to use for the computation
        ty: Struct,
        /// Must be a valid index into the structure (Will panic otherwise)
        index: usize,
    },
    /// Stores a pointer in the destination register to a particular element of
    /// an array. Effectively computes `destination = source + size_of(ty) *
    /// index`
    GetArrayElementPointer {
        /// Must be a pointer type
        destination: RegisterId,
        /// Must be a pointer type
        source: Operand,
        /// The inner type which composes the array
        ty: Type,
        /// Must be a valid index into the array (UB otherwise)
        index: usize,
    },
    Move {
        destination: RegisterId,
        source: Operand,
    },
    IntegerCast {
        kind: IntegerCastKind,
        destination: RegisterId,
        operand: Operand,
    },
    UnaryOperation {
        operator: UnaryOperatorKind,
        destination: RegisterId,
        operand: Operand,
    },
    // TODO: math ops (only some are sign sensitive)
    BinaryOperation {
        operator: BinaryOperatorKind,
        destination: RegisterId,
        lhs: Operand,
        rhs: Operand,
    },
    // TODO: load and store struct fields with indices
    Branch {
        condition: Operand,
        positive: BlockId,
        negative: BlockId,
    },
    Jump {
        destination: BlockId,
    },
    Return {
        value: Option<Operand>,
    },
    FunctionCall {
        target: Operand,
        arguments: Vec<Operand>,
        destination: Option<RegisterId>,
    },
    Phi {
        destination: RegisterId,
        sources: BTreeMap<BlockId, RegisterId>,
    },
    Comment(String),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Immediate {
    Int(u64, IntegerWidth),
    Float(f64, FloatWidth),
    Bool(bool),
    AnonymousStaticLabel(StaticLabelId),
    NamedStaticLabel(InternedSymbol),
    FunctionLabel(InternedSymbol),
}

simple_index! {

    /// Represents a pointer to a piece of data to be later allocated in static
    /// memory during program assembly
    pub struct StaticLabelId;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operand {
    Immediate(Immediate),
    Register(RegisterId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegerCastKind {
    SignExtension,
    ZeroExtension,
    Truncate,
}

#[derive(Debug)]
pub struct Layout {
    pub size: usize,
    pub alignment: usize,
}

impl Type {
    /// Returns the size and alignment of the type in bytes
    pub fn layout(&self) -> Layout {
        let (size, alignment) = match self {
            Self::Integer(IntegerWidth::I8) => (1, 1),
            Self::Integer(IntegerWidth::I16) => (2, 2),
            Self::Integer(IntegerWidth::I32) => (4, 4),
            Self::Integer(IntegerWidth::I64) => (8, 8),
            Self::Float(FloatWidth::F32) => (4, 4),
            Self::Float(FloatWidth::F64) => (4, 8),
            Self::Pointer => (8, 8),
            Self::Array(ty, length) => (ty.layout().size * length, ty.layout().alignment),
            Self::Struct(s) => return s.layout(),
        };

        Layout { size, alignment }
    }
}

impl Struct {
    pub fn layout_of(&self, index: usize) -> Layout {
        self.0.get(index).expect("Invalid field index").layout()
    }

    pub fn offset_of(&self, index: usize) -> usize {
        assert!(self.0.len() > index);

        let mut offset = 0;

        for ty in self.0.iter().take(index) {
            let layout = ty.layout();
            offset = align_to(offset, layout.alignment);
            offset += layout.size;
        }

        offset
    }

    pub fn layout(&self) -> Layout {
        let mut offset = 0;
        let mut max_align = 1;

        for ty in self.0.iter() {
            let layout = ty.layout();
            offset = align_to(offset, layout.alignment);
            offset += layout.size;
            max_align = max_align.max(layout.alignment);
        }

        let total_size = align_to(offset, max_align);

        Layout {
            size: total_size,
            alignment: max_align,
        }
    }

    /// Returns the number of integer fields in this struct including those in
    /// all recursive sub-fields
    pub fn num_integer_fields(&self) -> usize {
        self.0.iter().fold(0, |acc, ty| match ty {
            Type::Integer(_) => acc + 1,
            Type::Float(_) => acc,
            Type::Pointer => acc + 1,
            Type::Struct(s) => acc + s.num_integer_fields(),
            Type::Array(_, _) => acc,
        })
    }

    pub fn num_non_integer_fields(&self) -> usize {
        self.0.iter().fold(0, |acc, ty| match ty {
            Type::Integer(_) => acc,
            Type::Float(_) => acc + 1,
            Type::Pointer => acc,
            Type::Struct(s) => acc + s.num_non_integer_fields(),
            Type::Array(_, _) => acc + 1,
        })
    }
}

pub fn align_to(offset: usize, align: usize) -> usize {
    (offset + align - 1) & !(align - 1)
}
