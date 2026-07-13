mod bool;
mod bv;

use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::algorithms::walk_post_order;
use clarirs_core::cache::GenericCache;
use clarirs_core::prelude::*;

// Define an enum to represent the result of reduction
#[derive(Debug, Clone)]
pub enum ReduceResult {
    BitVec(StridedInterval),
    Bool(ComparisonResult),
}

impl ReduceResult {
    /// Extract the strided interval, erroring if this is not a bitvector result.
    pub fn into_bv(self) -> Result<StridedInterval, ClarirsError> {
        match self {
            ReduceResult::BitVec(si) => Ok(si),
            _ => Err(ClarirsError::InvalidArguments(
                "Expected BitVec result".to_string(),
            )),
        }
    }

    /// Extract the comparison result, erroring if this is not a bool result.
    pub fn into_bool(self) -> Result<ComparisonResult, ClarirsError> {
        match self {
            ReduceResult::Bool(result) => Ok(result),
            _ => Err(ClarirsError::InvalidArguments(
                "Expected Bool result".to_string(),
            )),
        }
    }
}

/// Reduces expressions into abstract domains:
/// - BitVec expressions are reduced to StridedIntervals
/// - Bool expressions are reduced to ComparisonResults
/// - Float and String expressions return errors
///
/// The result is wrapped in a [`ReduceResult`]; callers extract the relevant
/// variant via [`ReduceResult::into_bv`]/[`ReduceResult::into_bool`].
pub trait Reduce<'c>: Sized {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError>;
}

impl<'c> Reduce<'c> for AstRef<'c> {
    fn reduce(&self) -> Result<ReduceResult, ClarirsError> {
        let cache = GenericCache::default();
        walk_post_order(
            self.clone(),
            |node, children| match node.ast_type() {
                AstType::BitVec(_) => bv::reduce_bv(&node, children).map(ReduceResult::BitVec),
                AstType::Bool => bool::reduce_bool(&node, children).map(ReduceResult::Bool),
                _ => Err(ClarirsError::UnsupportedOperation(
                    "Unsupported operation for reduction".to_string(),
                )),
            },
            &cache,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reduce_result_into_bv() {
        let si = StridedInterval::constant(8, 42u32);
        assert_eq!(ReduceResult::BitVec(si.clone()).into_bv().unwrap(), si);

        // A Bool result cannot be extracted as a bitvector
        assert!(
            ReduceResult::Bool(ComparisonResult::True)
                .into_bv()
                .is_err()
        );
    }

    #[test]
    fn test_reduce_result_into_bool() {
        assert_eq!(
            ReduceResult::Bool(ComparisonResult::Maybe)
                .into_bool()
                .unwrap(),
            ComparisonResult::Maybe
        );

        // A BitVec result cannot be extracted as a bool
        assert!(
            ReduceResult::BitVec(StridedInterval::top(8))
                .into_bool()
                .is_err()
        );
    }

    #[test]
    fn test_reduce_float_unsupported() {
        let ctx = Context::new();
        let f = ctx.fpv_from_f64(1.0).unwrap();
        assert!(f.reduce().is_err());
    }

    #[test]
    fn test_reduce_string_unsupported() {
        let ctx = Context::new();
        let s = ctx.stringv("hello").unwrap();
        assert!(s.reduce().is_err());
    }

    #[test]
    fn test_reduce_bool_op_with_float_children_errors() {
        // The children (floats) are unsupported, so the whole reduction errors
        let ctx = Context::new();
        let a = ctx.fpv_from_f64(1.0).unwrap();
        let b = ctx.fpv_from_f64(2.0).unwrap();
        let cmp = ctx.fp_lt(a, b).unwrap();
        assert!(cmp.reduce().is_err());
    }
}
