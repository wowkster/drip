use crate::{
    frontend::{SourceFile, SourceFileId},
    index::IndexVec,
};

/// Global compiler session state
#[derive(Debug)]
pub struct Session {
    /// Stores all of the source files discovered during parsing. Used for error
    /// reporting.
    source_map: IndexVec<SourceFileId, SourceFile>,
}

impl Session {
    pub fn new() -> Self {
        Self {
            source_map: IndexVec::new(),
        }
    }

    pub fn insert_source_file(&mut self, file: SourceFile) -> SourceFileId {
        self.source_map.push(file)
    }

    pub fn get_source_file(&self, id: SourceFileId) -> Option<&SourceFile> {
        self.source_map.get(id)
    }
}
