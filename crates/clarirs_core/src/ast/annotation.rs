use serde::Serialize;

use super::node::AstRef;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct Annotation<'c> {
    name: String,
    value: AstRef<'c>,
    eliminatable: bool,
    relocatable: bool,
}

impl<'c> Annotation<'c> {
    pub fn new(name: String, value: AstRef<'c>, eliminatable: bool, relocatable: bool) -> Self {
        Self {
            name,
            value,
            eliminatable,
            relocatable,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn value(&'c self) -> &AstRef<'c> {
        &self.value
    }

    pub fn eliminatable(&self) -> bool {
        self.eliminatable
    }

    pub fn relocatable(&self) -> bool {
        self.relocatable
    }
}
