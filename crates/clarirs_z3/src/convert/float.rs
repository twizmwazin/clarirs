use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

pub unsafe fn convert_float_to_z3(
    _z3_ctx: z3::Context,
    _ast: &FloatAst,
) -> Result<z3::Ast, ClarirsError> {
    todo!()
}

pub unsafe fn convert_float_from_z3<'c>(
    _ctx: &'c Context<'c>,
    _ast: z3::Ast,
) -> Result<FloatAst<'c>, ClarirsError> {
    todo!()
}
