mod bool;
mod bv;

use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::algorithms::walk_post_order;
use clarirs_core::prelude::*;

fn child(children: &[ReduceResult], index: usize) -> Result<ComparisonResult, ClarirsError> {
    if let Some(ReduceResult::Bool(result)) = children.get(index) {
        Ok(result.clone())
    } else {
        Err(ClarirsError::InvalidArguments(format!(
            "Expected Bool at index {}, found {:?}",
            index,
            children.get(index)
        )))
    }
}

fn child_si(children: &[ReduceResult], index: usize) -> Result<StridedInterval, ClarirsError> {
    if let Some(ReduceResult::BitVec(result)) = children.get(index) {
        Ok(result.clone())
    } else {
        Err(ClarirsError::InvalidArguments(format!(
            "Expected BitVec at index {}, found {:?}",
            index,
            children.get(index)
        )))
    }
}

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
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::BitVec(bv) => bv::reduce_bv(&bv, children).map(ReduceResult::BitVec),
                DynAst::Boolean(bool) => bool::reduce_bool(&bool, children).map(ReduceResult::Bool),
                _ => Err(ClarirsError::UnsupportedOperation(
                    "Unsupported operation for reduction".to_string(),
                )),
            },
            &(),
        )
    }
}

impl<'c> Reduce<'c> for BoolAst<'c> {
    type Result = ComparisonResult;

    fn reduce(&self) -> Result<Self::Result, ClarirsError> {
        if let ReduceResult::Bool(result) = DynAst::Boolean(self.clone()).reduce()? {
            Ok(result)
        } else {
            Err(ClarirsError::InvalidArguments(
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
            Err(ClarirsError::InvalidArguments(
                "Expected BitVec result".to_string(),
            ))
        }
    }
}
