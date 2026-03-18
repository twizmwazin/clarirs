mod bool;
mod bv;

use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::algorithms::walk_pre_order;
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
    type Result;

    fn reduce(&self) -> Result<Self::Result, ClarirsError>;
}

impl<'c> Reduce<'c> for DynAst<'c> {
    type Result = ReduceResult;

    fn reduce(&self) -> Result<Self::Result, ClarirsError> {
        walk_pre_order(
            self.clone(),
            // pre_visit: no short-circuit; rely on walk_pre_order's internal
            // cache to deduplicate shared subtrees
            |_node| Ok(None),
            // post_visit: reduce the node using already-reduced children
            |node, children| match node {
                DynAst::BitVec(bv) => bv::reduce_bv(&bv, children).map(ReduceResult::BitVec),
                DynAst::Boolean(bool) => {
                    bool::reduce_bool(&bool, children).map(ReduceResult::Bool)
                }
                _ => Err(ClarirsError::UnsupportedOperation(
                    "Unsupported operation for reduction".to_string(),
                )),
            },
        )
    }
}

impl<'c> Reduce<'c> for BoolAst<'c> {
    type Result = ComparisonResult;

    fn reduce(&self) -> Result<Self::Result, ClarirsError> {
        if let ReduceResult::Bool(result) = DynAst::Boolean(self.clone()).reduce()? {
            Ok(result)
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected Bool result".to_string(),
            ))
        }
    }
}

impl<'c> Reduce<'c> for BitVecAst<'c> {
    type Result = StridedInterval;

    fn reduce(&self) -> Result<StridedInterval, ClarirsError> {
        if let ReduceResult::BitVec(result) = DynAst::BitVec(self.clone()).reduce()? {
            Ok(result)
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected BitVec result".to_string(),
            ))
        }
    }
}
