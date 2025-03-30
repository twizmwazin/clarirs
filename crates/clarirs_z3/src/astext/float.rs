use clarirs_core::prelude::*;

use crate::rc::RcAst;

pub(crate) fn to_z3(_ast: &FloatAst, _children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    todo!()
}

pub(crate) fn from_z3<'c>(
    _ctx: &'c Context<'c>,
    _ast: impl Into<RcAst>,
) -> Result<FloatAst<'c>, ClarirsError> {
    todo!()
}
