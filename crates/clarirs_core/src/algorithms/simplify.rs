mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use crate::prelude::*;

pub(crate) fn extract_bool_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<BoolAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_bool())
        .ok_or(ClarirsError::InvalidArguments)
}

pub(crate) fn extract_bitvec_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<BitVecAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_bitvec())
        .ok_or(ClarirsError::InvalidArguments)
}

pub(crate) fn extract_float_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<FloatAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_float())
        .ok_or(ClarirsError::InvalidArguments)
}

pub(crate) fn extract_string_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<StringAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_string())
        .ok_or(ClarirsError::InvalidArguments)
}

use super::walk_post_order;

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError>;
}

impl<'c> Simplify<'c> for BoolAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .simplify()?
            .as_bool()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))
    }
}

impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .simplify()?
            .as_bitvec()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BvAst".to_string()))
    }
}

impl<'c> Simplify<'c> for FloatAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .simplify()?
            .as_float()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))
    }
}

impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .simplify()?
            .as_string()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))
    }
}

impl<'c> Simplify<'c> for DynAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::Boolean(ast) => bool::simplify_bool(&ast, children).map(DynAst::Boolean),
                DynAst::BitVec(ast) => bv::simplify_bv(&ast, children).map(DynAst::BitVec),
                DynAst::Float(ast) => float::simplify_float(&ast, children).map(DynAst::Float),
                DynAst::String(ast) => string::simplify_string(&ast, children).map(DynAst::String),
            },
            &self.context().simplification_cache,
        )
    }
}
