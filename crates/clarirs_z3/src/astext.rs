mod bool;
mod bv;
mod float;
mod string;

use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

use crate::Z3_CONTEXT;

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Sized {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError>;

    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let ast = self.to_z3()?;
        Z3_CONTEXT.with(|ctx| {
            let simplified_ast = unsafe { z3::simplify(*ctx, ast) };
            unsafe { z3::inc_ref(*ctx, simplified_ast) };
            let result = Self::from_z3(self.context(), simplified_ast);
            unsafe { z3::dec_ref(*ctx, simplified_ast) };
            result
        })
    }
}
