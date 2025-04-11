mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use crate::prelude::*;
macro_rules! extract_bool_child {
    ($children:ident, $index:expr) => {
        $children
            .get($index)
            .and_then(|child| child.clone().into_bool())
            .ok_or_else(|| ClarirsError::InvalidArguments)?
    };
}

macro_rules! extract_bitvec_child {
    ($children:ident, $index:expr) => {
        $children
            .get($index)
            .and_then(|child| child.clone().into_bitvec())
            .ok_or_else(|| ClarirsError::InvalidArguments)?
    };
}

macro_rules! extract_float_child {
    ($children:ident, $index:expr) => {
        $children
            .get($index)
            .and_then(|child| child.clone().into_float())
            .ok_or_else(|| ClarirsError::InvalidArguments)?
    };
}

macro_rules! extract_string_child {
    ($children:ident, $index:expr) => {
        $children
            .get($index)
            .and_then(|child| child.clone().into_string())
            .ok_or_else(|| ClarirsError::InvalidArguments)?
    };
}

pub(crate) use extract_bitvec_child;
pub(crate) use extract_bool_child;
pub(crate) use extract_float_child;
pub(crate) use extract_string_child;

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
