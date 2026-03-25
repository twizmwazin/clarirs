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
pub trait Reduce<T>: Sized {
    fn reduce(&self) -> Result<T, ClarirsError>;
}

fn reduce_ast<'c>(ast: &AstRef<'c>) -> Result<ReduceResult, ClarirsError> {
    walk_post_order(
        ast.clone(),
        |node, children| match node.return_type() {
            AstType::BitVec(_) => bv::reduce_bv(&node, children).map(ReduceResult::BitVec),
            AstType::Bool => bool::reduce_bool(&node, children).map(ReduceResult::Bool),
            _ => Err(ClarirsError::UnsupportedOperation(
                "Unsupported operation for reduction".to_string(),
            )),
        },
        &(),
    )
}

impl<'c> Reduce<ReduceResult> for AstRef<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        reduce_ast(self)
    }
}

impl<'c> Reduce<ComparisonResult> for AstRef<'c> {
    fn reduce(&self) -> Result<ComparisonResult, ClarirsError> {
        if let ReduceResult::Bool(result) = reduce_ast(self)? {
            Ok(result)
        } else {
            Err(ClarirsError::InvalidArguments(
                "Expected Bool result".to_string(),
            ))
        }
    }
}

impl<'c> Reduce<StridedInterval> for AstRef<'c> {
    fn reduce(&self) -> Result<StridedInterval, ClarirsError> {
        if let ReduceResult::BitVec(result) = reduce_ast(self)? {
            Ok(result)
        } else {
            Err(ClarirsError::InvalidArguments(
                "Expected BitVec result".to_string(),
            ))
        }
    }
}
