use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

pub fn convert_bv_to_z3(_ast: &BitVecAst) -> Result<z3::Ast, ClarirsError> {
    todo!()
}

pub fn convert_bv_from_z3<'c>(_ast: z3::Ast) -> Result<BitVecAst<'c>, ClarirsError> {
    todo!()
}
