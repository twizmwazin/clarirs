use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct Annotation {
    name: String,
    value: Vec<u8>,
    eliminatable: bool,
    relocatable: bool,
}

impl<'c> Annotation {
    pub fn new(name: String, value: Vec<u8>, eliminatable: bool, relocatable: bool) -> Self {
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

    pub fn value(&'c self) -> &Vec<u8> {
        &self.value
    }

    pub fn eliminatable(&self) -> bool {
        self.eliminatable
    }

    pub fn relocatable(&self) -> bool {
        self.relocatable
    }
}
