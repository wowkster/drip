//! A high level intermediate representation of the source code. Some
//! unnecessary information from the AST is removed like node IDs and spans for
//! individual pieces of syntax. Certain constructs from the AST are removed and
//! blocks are collected and separated from their owning nodes.

use core::fmt::Debug;
use std::{collections::BTreeMap, rc::Rc};

use super::primitive::{FloatKind, IntKind, PrimitiveKind, UIntKind};
use crate::{
    frontend::{
        ast::{AssignmentOperatorKind, BinaryOperatorKind, UnaryOperatorKind},
        intern::InternedSymbol,
        lexer::Span,
    },
    index::IndexVec,
};

pub mod ast_lowering;
pub mod id;
pub mod visit;

pub use id::*;
use itertools::Itertools;

#[derive(Debug)]
pub struct Module {
    /// All the item definitions within the module including those nested within
    /// other items
    pub owners: IndexVec<LocalDefId, Owner>,
}

impl Module {
    pub fn get_body(&self, id: BodyId) -> Rc<Body> {
        let owner = &self.owners[id.hir_id.owner];

        let Some(body) = &owner.body else {
            panic!("invalid body id");
        };

        assert_eq!(body.id(), id, "invalid body id");

        body.clone()
    }

    pub fn get_bodies(&self) -> impl Iterator<Item = BodyId> {
        self.owners
            .iter()
            .flat_map(|owner| owner.body.as_ref().map(|b| b.id()))
    }

    pub fn get_owner(&self, def_id: LocalDefId) -> &Owner {
        &self.owners[def_id]
    }

    pub fn get_owners(&self) -> impl Iterator<Item = LocalDefId> {
        self.owners.indices()
    }

    /// Finds the parent of the provided node in the tree. Returns None if the
    /// requested ID is an owner and this has no parent
    pub fn get_parent_of(&self, hir_id: HirId) -> Option<Node> {
        let owner = &self.owners[hir_id.owner];
        let node = &owner.nodes[hir_id.local_id];

        if node.parent == ItemLocalId::INVALID {
            None
        } else {
            Some(owner.nodes[node.parent].node.clone())
        }
    }

    /// Given a path, generate the mangled global symbol which can be used in
    /// the assembly. This symbol uses the module name and parent hierarchy to
    /// remove name conflicts from other translation units
    pub fn global_symbol_for(&self, path: &Path) -> InternedSymbol {
        path.as_local_symbol()
    }
}

/// Represents a top level owner within a module. HIR owners may be nested
#[derive(Debug)]
pub struct Owner {
    /// Contains all the HIR nodes for this owner. The first node is always the
    /// owner itself. This is how nodes are looked up by LocalId within an owner
    /// which is much faster than traversing the tree searching for it.
    /// Important to note is that this owner may contain nested owner nodes
    /// (i.e. functions defined within another function or functions defined
    /// within an impl block)
    pub nodes: IndexVec<ItemLocalId, ParentedNode>,
    /// Map from nested owners to their local ID within this owner
    pub parenting: BTreeMap<LocalDefId, ItemLocalId>,
    /// If present, the executable body within the owner. Will not be set for
    /// items like type definitions.
    pub body: Option<Rc<Body>>,
}

impl Owner {
    /// Returns the associated owner node kind
    pub fn node(&self) -> OwnerNode {
        // Indexing must ensure it is an OwnerNode.
        self.nodes[ItemLocalId::ZERO]
            .node
            .clone()
            .as_owner()
            .unwrap()
    }
}

/// An HIR node coupled with the ID of it's parent node. This makes the tree
/// structure of the HIR traversable easily in both directions.
///
/// When the node is a top level owner in the module, the parent id is always
/// INVALID. However, it will be set if the owner is a nested owner.
#[derive(Debug)]
pub struct ParentedNode {
    pub parent: ItemLocalId,
    pub node: Node,
}

#[derive(Debug, Clone)]
pub enum Node {
    Item(Rc<Item>),
    FunctionParameter(Rc<FunctionParameter>),
    StructField(Rc<StructField>),
    Expression(Rc<Expression>),
    Block(Rc<Block>),
    Statement(Rc<Statement>),
    /// Exists so that we can resolve local variable references to a node ID
    LetStatement(Rc<LetStatement>),
    Type(Rc<Type>),
    PathSegment(Rc<PathSegment>),
    StructInitializerField(Rc<StructInitializerField>),
}

impl Node {
    pub fn id(&self) -> HirId {
        match self {
            Node::Item(v) => v.hir_id(),
            Node::FunctionParameter(v) => v.hir_id,
            Node::StructField(v) => v.hir_id,
            Node::Expression(v) => v.hir_id,
            Node::Block(v) => v.hir_id,
            Node::Statement(v) => v.hir_id,
            Node::LetStatement(v) => v.hir_id,
            Node::Type(v) => v.hir_id,
            Node::PathSegment(v) => v.hir_id,
            Node::StructInitializerField(v) => v.hir_id,
        }
    }

    pub fn as_owner(self) -> Option<OwnerNode> {
        match self {
            Node::Item(item) => Some(OwnerNode::Item(item)),
            Node::Block(_)
            | Node::FunctionParameter(_)
            | Node::StructField(_)
            | Node::Statement(_)
            | Node::LetStatement(_)
            | Node::Type(_)
            | Node::Expression(_)
            | Node::PathSegment(_)
            | Node::StructInitializerField(_) => None,
        }
    }

    pub fn as_item(&self) -> Option<Rc<Item>> {
        match self {
            Node::Item(item) => Some(item.clone()),
            _ => None,
        }
    }

    pub fn as_let_statement(&self) -> Option<Rc<LetStatement>> {
        match self {
            Node::LetStatement(let_stmt) => Some(let_stmt.clone()),
            _ => None,
        }
    }
}

/// Represents an HIR node that can be a top level owner
#[derive(Debug)]
pub enum OwnerNode {
    ///
    Item(Rc<Item>),
    // TODO: submodules
    // TODO: foreign items
    // TODO: impl blocks?
}

impl OwnerNode {
    pub fn hir_id(&self) -> HirId {
        match self {
            OwnerNode::Item(item) => item.hir_id(),
        }
    }

    pub fn as_item(&self) -> Option<Rc<Item>> {
        match self {
            Self::Item(item) => Some(item.clone()),
        }
    }
}

impl From<OwnerNode> for Node {
    fn from(value: OwnerNode) -> Self {
        match value {
            OwnerNode::Item(item) => Node::Item(item),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub symbol: InternedSymbol,
    pub span: Span,
}

#[derive(Debug)]
pub struct Item {
    pub owner_id: LocalDefId,
    pub kind: ItemKind,
    pub span: Span,
}

impl Item {
    pub fn hir_id(&self) -> HirId {
        HirId::from_def_id(self.owner_id)
    }
}

#[derive(Debug)]
pub enum ItemKind {
    Function {
        name: Path,
        signature: FunctionSignature,
        body: BodyId,
    },
    Struct {
        name: Identifier,
        fields: Rc<[Rc<StructField>]>,
    },
    TypeAlias {
        name: Identifier,
        ty: Rc<Type>,
    },
    Static {
        is_mutable: bool,
        name: Identifier,
        ty: Rc<Type>,
        initializer: Rc<Expression>,
    },
    // TODO: enums, unions, const, submodule, impl
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub hir_id: HirId,
    pub name: Identifier,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub self_parameter: Option<SelfParameter>,
    /// List of inputs to the function
    pub parameters: Rc<[Rc<Type>]>,
    /// If present, is the expected variadic type (`any` for compat with c
    /// variadics)
    pub variadic_type: Option<Rc<Type>>,
    /// None if no return type is specified (defaults to `()` in this case)
    pub return_type: Option<Rc<Type>>,
    // Span of the function decl without body
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SelfParameter {
    Owned,
    Pointer { is_mutable: bool },
}

/// The body of a function or constant value
#[derive(Debug)]
pub struct Body {
    pub params: Rc<[Rc<FunctionParameter>]>,
    pub block: Rc<Block>,
}

impl Body {
    pub fn id(&self) -> BodyId {
        BodyId {
            hir_id: self.block.hir_id,
        }
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub hir_id: HirId,
    pub name: Identifier, // TODO: replace with pattern
    pub ty_span: Span,
    pub span: Span,
}

#[derive(Debug)]
pub struct Block {
    pub hir_id: HirId,
    pub statements: Rc<[Rc<Statement>]>,
    /// An expression at the end of the block without a semicolon, if any. (Used
    /// to infer the type of the block later)
    pub expression: Option<Rc<Expression>>,
    pub is_const: bool,
    pub span: Span,
}

#[derive(Debug)]
pub struct Statement {
    pub hir_id: HirId,
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Let(Rc<LetStatement>),
    /// An expression without a trailing semi-colon (must have unit type).
    BareExpression(Rc<Expression>),
    /// An expression with a trailing semi-colon (may have any type).
    SemiExpression(Rc<Expression>),
}

#[derive(Debug)]
pub struct LetStatement {
    pub hir_id: HirId,
    pub is_mutable: bool, // TODO: replace with pattern
    pub name: Identifier, // TODO: replace with pattern
    pub ty: Option<Rc<Type>>,
    pub initializer: Option<Rc<Expression>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ArrayInitializer {
    Repeated {
        value: Rc<Expression>,
        length: usize,
    },
    Specific(Rc<[Rc<Expression>]>),
}

#[derive(Debug, Clone)]
pub struct StructInitializerField {
    pub hir_id: HirId,
    pub name: Identifier,
    pub value: Rc<Expression>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Expression {
    pub hir_id: HirId,
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal(Literal),
    Path(Path),
    This,
    Array(ArrayInitializer),
    Tuple(Rc<[Rc<Expression>]>),
    Struct {
        name: Path,
        fields: Rc<[Rc<StructInitializerField>]>,
    },
    Block(Rc<Block>),
    FieldAccess {
        target: Rc<Expression>,
        name: Identifier,
        is_method_call: bool,
    },
    FunctionCall {
        target: Rc<Expression>,
        arguments: Rc<[Rc<Expression>]>,
    },
    Binary {
        lhs: Rc<Expression>,
        operator: BinaryOperatorKind,
        rhs: Rc<Expression>,
    },
    Unary {
        operator: UnaryOperatorKind,
        operand: Rc<Expression>,
    },
    Cast {
        expression: Rc<Expression>,
        ty: Rc<Type>,
    },
    If {
        condition: Rc<Expression>,
        positive: Rc<Block>,
        /// must be a block expression or an if expression
        negative: Option<Rc<Expression>>,
    },
    While {
        condition: Rc<Expression>,
        block: Rc<Block>,
    },
    Assignment {
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
    },
    OperatorAssignment {
        operator: AssignmentOperatorKind,
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
    },
    Break,
    Continue,
    // Least priority
    Return(Option<Rc<Expression>>),
}

macro_rules! expr_kind_as {
    ($suffix:ident, $variant:ident, $ty:ty) => {
        paste::paste! {
            #[allow(unused)]
            pub fn [<as_ $suffix>](&self) -> Option<&$ty> {
                if let Self::$variant(v) = self {
                    Some(v)
                } else {
                    None
                }
            }

            #[allow(unused)]
            #[track_caller]
            pub fn [<expect_ $suffix>](&self) -> &$ty {
                self.[<as_ $suffix>]().unwrap()
            }
        }
    };
}
impl ExpressionKind {
    expr_kind_as!(literal, Literal, Literal);
    expr_kind_as!(tuple, Tuple, Rc<[Rc<Expression>]>);
}

#[derive(Debug)]
pub enum Literal {
    Boolean(bool),
    Char(char),
    Integer(u64, LiteralIntegerKind),
    Float(InternedSymbol, LiteralFloatKind),
    String(InternedSymbol),
    ByteString(Rc<[u8]>),
    CString(Rc<[u8]>),
}

impl Literal {
    pub fn as_string(&self) -> Option<InternedSymbol> {
        if let Self::String(s) = self {
            Some(*s)
        } else {
            None
        }
    }

    #[track_caller]
    pub fn expect_string(&self) -> InternedSymbol {
        self.as_string().unwrap()
    }
}

#[derive(Debug)]
pub enum LiteralIntegerKind {
    /// e.g. `42_i32`
    Signed(IntKind),
    /// e.g. `42_u32`
    Unsigned(UIntKind),
    /// e.g. `42`
    Unsuffixed,
}

#[derive(Debug)]
pub enum LiteralFloatKind {
    Suffixed(FloatKind),
    Unsuffixed,
}

#[derive(Debug)]
pub struct Type {
    pub hir_id: HirId,
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TypeKind {
    Unit,
    /// core::string::String | u32 | some_local
    Path(Path),
    /// *T
    Pointer(Rc<Type>),
    /// [T]
    Slice(Rc<Type>),
    /// [T; 1024]
    Array {
        ty: Rc<Type>,
        length: usize,
    },
    /// (i32, u8, str)
    Tuple(Rc<[Rc<Type>]>),
    /// fn(T1, T2, ... *any) -> T3
    FunctionPointer {
        parameters: Rc<[Rc<Type>]>,
        return_type: Option<Rc<Type>>,
        is_variadic: bool, // FIXME: type?
    },
    /// any
    Any,
}

/// A path made up of multiple segments separated by `::`.
#[derive(Debug)]
pub struct Path {
    pub segments: Rc<[Rc<PathSegment>]>,
    pub span: Span,
}

impl Path {
    /// Returns the final resolution in the path (last segment)
    pub fn resolution(&self) -> &Resolution {
        &self.segments.last().as_ref().unwrap().resolution
    }

    /// Returns a string representation of the path which can be used for
    pub fn as_local_symbol(&self) -> InternedSymbol {
        InternedSymbol::new(
            &self
                .segments
                .iter()
                .map(|s| s.identifier.symbol.value())
                .join("::"),
        )
    }
}

#[derive(Debug)]
pub struct PathSegment {
    pub hir_id: HirId,
    pub identifier: Identifier,
    pub resolution: Resolution,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution<R = ItemLocalId> {
    // Any namespace
    // TODO: use global ID once we support modules
    Definition(DefinitionKind, LocalDefId),
    // Value namespace
    Local(R),
    IntrinsicFunction(InternedSymbol),
    // Type namespace
    Primitive(PrimitiveKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    // Value namespace
    Function,
    Constant,
    Static,

    // Type namespace
    Struct,
    Enum,
    Union,
    Alias,
}

impl<R> Resolution<R> {
    pub fn as_function_definition(self) -> Option<LocalDefId> {
        match self {
            Resolution::Definition(DefinitionKind::Function, local_def_id) => Some(local_def_id),
            _ => None,
        }
    }

    pub fn as_static_definition(self) -> Option<LocalDefId> {
        match self {
            Resolution::Definition(DefinitionKind::Static, local_def_id) => Some(local_def_id),
            _ => None,
        }
    }
}
