use crate::prelude::*;

pub trait ChildVecExt<'c> {
    fn child_bool(&self, index: usize) -> Result<BoolAst<'c>, ClarirsError>;
    fn child_bitvec(&self, index: usize) -> Result<BitVecAst<'c>, ClarirsError>;
    fn child_float(&self, index: usize) -> Result<FloatAst<'c>, ClarirsError>;
    fn child_string(&self, index: usize) -> Result<StringAst<'c>, ClarirsError>;
    fn child_dyn(&self, index: usize) -> Result<DynAst<'c>, ClarirsError>;
}

impl<'c> ChildVecExt<'c> for &[DynAst<'c>] {
    fn child_bool(&self, index: usize) -> Result<BoolAst<'c>, ClarirsError> {
        self.get(index)
            .and_then(|child| child.clone().into_bool())
            .ok_or(ClarirsError::InvalidArgumentsWithMessage(format!(
                "ChildVecExt: Invalid index {index} for child bool"
            )))
    }

    fn child_bitvec(&self, index: usize) -> Result<BitVecAst<'c>, ClarirsError> {
        self.get(index)
            .and_then(|child| child.clone().into_bitvec())
            .ok_or(ClarirsError::InvalidArgumentsWithMessage(format!(
                "ChildVecExt: Invalid index {index} for child bitvec"
            )))
    }

    fn child_float(&self, index: usize) -> Result<FloatAst<'c>, ClarirsError> {
        self.get(index)
            .and_then(|child| child.clone().into_float())
            .ok_or(ClarirsError::InvalidArgumentsWithMessage(format!(
                "ChildVecExt: Invalid index {index} for child float"
            )))
    }

    fn child_string(&self, index: usize) -> Result<StringAst<'c>, ClarirsError> {
        self.get(index)
            .and_then(|child| child.clone().into_string())
            .ok_or(ClarirsError::InvalidArgumentsWithMessage(format!(
                "ChildVecExt: Invalid index {index} for child string"
            )))
    }

    fn child_dyn(&self, index: usize) -> Result<DynAst<'c>, ClarirsError> {
        self.get(index)
            .cloned()
            .ok_or(ClarirsError::InvalidArgumentsWithMessage(format!(
                "ChildVecExt: Invalid index {index} for child dyn"
            )))
    }
}
