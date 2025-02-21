use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

use super::AstExtZ3;

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        todo!()
    }

    fn from_z3(_ctx: &'c Context<'c>, _ast: z3::Ast) -> Result<Self, ClarirsError> {
        todo!()
    }
}
