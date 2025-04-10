mod bool;
mod bv;

use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::algorithms::walk_post_order;
use clarirs_core::prelude::*;

// Define an enum to represent the result of reduction
#[derive(Debug, Clone)]
pub enum ReduceResult {
    BitVec(StridedInterval),
    Bool(ComparisonResult),
}

/// The Reduce trait transforms expressions into abstract domains:
/// - BitVec expressions are reduced to StridedIntervals
/// - Bool expressions are reduced to ComparisonResults
/// - Float and String expressions return errors
pub trait Reduce<'c>: Sized {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError>;
}

impl<'c> Reduce<'c> for DynAst<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::BitVec(bv) => bv::reduce_bv(&bv, &children).map(ReduceResult::BitVec),
                DynAst::Boolean(bool) => {
                    bool::reduce_bool(&bool, &children).map(ReduceResult::Bool)
                }
                _ => Err(ClarirsError::UnsupportedOperation(
                    "Unsupported operation for reduction".to_string(),
                )),
            },
            &(),
        )
    }
}

impl<'c> Reduce<'c> for BoolAst<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        DynAst::Boolean(self.clone()).reduce()
    }
}

impl<'c> Reduce<'c> for BitVecAst<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        DynAst::BitVec(self.clone()).reduce()
    }
}

impl<'c> Reduce<'c> for FloatAst<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Reduce is not supported for Float expressions".to_string(),
        ))
    }
}

impl<'c> Reduce<'c> for StringAst<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Reduce is not supported for String expressions".to_string(),
        ))
    }
}
