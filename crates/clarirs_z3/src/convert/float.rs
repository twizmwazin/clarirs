use clarirs_core::prelude::*;

pub fn convert_float_to_z3<'z>(
    _z3_ctx: &'z z3::Context,
    _ast: &FloatAst,
) -> Result<z3::ast::Float<'z>, ClarirsError> {
    todo!()
}

pub fn convert_float_from_z3<'c>(
    _ctx: &'c Context,
    _ast: &z3::ast::Float,
) -> Result<FloatAst<'c>, ClarirsError> {
    todo!()
}
