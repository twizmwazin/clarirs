mod bool;
mod bv;
mod float;
mod string;

use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

use crate::{Z3_CONTEXT, rc::RcAst};

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Sized {
    fn to_z3(&self) -> Result<RcAst, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError>;

    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let ast = self.to_z3()?;
        Z3_CONTEXT.with(|ctx| unsafe {
            let simplified_ast = RcAst::from(z3::simplify(*ctx, ast.into()));
            let result = Self::from_z3(self.context(), simplified_ast);
            result
        })
    }
}
