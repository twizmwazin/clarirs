use clarirs_core::prelude::*;

pub fn convert_bool_to_z3<'z>(
    _z3_ctx: &'z z3::Context,
    _ast: &BoolAst,
) -> Result<z3::ast::Bool<'z>, ClarirsError> {
    todo!()
}

pub fn convert_bool_from_z3<'c>(
    _ctx: &'c Context,
    _ast: &z3::ast::Bool,
) -> Result<BoolAst<'c>, ClarirsError> {
    todo!()
}
