use clarirs_core::prelude::*;

use super::AstExtZ3;
use crate::rc::RcAst;

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        todo!()
    }

    fn from_z3(_ctx: &'c Context<'c>, _ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        todo!()
    }
}
