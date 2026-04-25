use crate::index::simple_index;

simple_index! {
    /// Represents one of the top level crates being compiled
    pub struct CrateNum;
}

/// Globally unique identifier for a particular item definition.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct DefId {
    krate: CrateNum,
    index: LocalDefId,
}

simple_index! {
    /// Represents a top level item that owns some amount of child nodes. This
    /// ID is tied to the crate in which the item is defined (not globally
    /// unique).
    pub struct LocalDefId;
}

simple_index! {
    /// Represents a child node within some top level owner
    pub struct ItemLocalId;
}

impl ItemLocalId {
    pub const ZERO: Self = Self(0);

    /// Used to denote that an ID does not actually identify a node in the tree
    /// and points to garbage. For example, the parent ID of the owner node uses
    /// this value to signal that it does not have a parent
    pub const INVALID: Self = Self(u32::MAX);
}

/// Identifies a node in the HIR for a crate. Composed of the ID of the
/// enclosing owner and the local ID of the node within the owner.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct HirId {
    pub owner: LocalDefId,
    pub local_id: ItemLocalId,
}

impl HirId {
    pub fn new(owner: LocalDefId, local_id: ItemLocalId) -> Self {
        Self { owner, local_id }
    }

    pub fn from_def_id(def_id: LocalDefId) -> Self {
        Self {
            owner: def_id,
            local_id: ItemLocalId::ZERO,
        }
    }
}

impl From<HirId> for ItemLocalId {
    fn from(value: HirId) -> Self {
        value.local_id
    }
}

/// An ID specifically identifying bodies within the HIR.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct BodyId {
    pub hir_id: HirId,
}
