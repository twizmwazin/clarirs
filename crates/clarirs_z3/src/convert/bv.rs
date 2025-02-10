use clarirs_core::prelude::*;

pub fn convert_bv_to_z3<'z>(
    _z3_ctx: &'z z3::Context,
    _ast: &BitVecAst,
) -> Result<z3::ast::BV<'z>, ClarirsError> {
    todo!()
}

pub fn convert_bv_from_z3<'c>(
    _ctx: &'c Context,
    _ast: &z3::ast::BV,
) -> Result<BitVecAst<'c>, ClarirsError> {
    todo!()
}
