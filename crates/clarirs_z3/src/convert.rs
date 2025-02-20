mod bool;
mod bv;
mod float;
mod string;

use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

pub(crate) trait Z3Convert<'c>: Sized {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError>;
}
