use std::{collections::BTreeMap, rc::Rc};

use crate::{
    frontend::ast,
    index::{Index, simple_index},
};

#[derive(Debug)]
pub struct CrateModuleTree {
    /// The name of the crate (i.e. "core")
    name: Rc<str>,

    next_module_id: ModuleId,

    nodes: BTreeMap<ModuleId, ModuleData>,
}

simple_index! {
    pub struct ModuleId;
}

impl ModuleId {
    pub const ZERO: Self = Self(0);
}

#[derive(Debug)]
pub struct ModuleData {
    id: ModuleId,
    ast: ast::Module,
    children: BTreeMap<Rc<str>, ModuleId>,
}

impl CrateModuleTree {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.into(),
            next_module_id: ModuleId::ZERO,
            nodes: BTreeMap::new(),
        }
    }

    fn create_module_id(&mut self) -> ModuleId {
        let id = self.next_module_id;
        self.next_module_id = id.plus(1);
        id
    }


    pub fn get(&self, id: ModuleId) -> Option<&ModuleData> {
        todo!()
    }

    pub fn get_id(&self, qualified_name: &[Rc<str>]) -> Option<ModuleId> {
        todo!()
    }
}
