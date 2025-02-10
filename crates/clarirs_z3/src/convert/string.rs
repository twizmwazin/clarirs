use clarirs_core::prelude::*;

pub fn convert_string_to_z3<'z>(
    _z3_ctx: &'z z3::Context,
    _ast: &StringAst,
) -> Result<z3::ast::String<'z>, ClarirsError> {
    todo!()
}

pub fn convert_string_from_z3<'c>(
    _ctx: &'c Context,
    _ast: &z3::ast::String,
) -> Result<StringAst<'c>, ClarirsError> {
    todo!()
}
