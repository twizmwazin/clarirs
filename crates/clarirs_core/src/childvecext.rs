use crate::prelude::*;

pub trait ChildVecExt<'c> {
    fn child(&self, index: usize) -> Result<AstRef<'c>, ClarirsError>;
}

impl<'c> ChildVecExt<'c> for &[AstRef<'c>] {
    fn child(&self, index: usize) -> Result<AstRef<'c>, ClarirsError> {
        self.get(index)
            .cloned()
            .ok_or(ClarirsError::InvalidArguments(format!(
                "ChildVecExt: Invalid index {index}"
            )))
    }
}
