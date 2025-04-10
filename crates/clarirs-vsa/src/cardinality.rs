use clarirs_core::prelude::*;
use num_bigint::BigUint;
use num_traits::One;

use crate::{
    reduce::{Reduce, ReduceResult},
    strided_interval::ComparisonResult,
};

pub trait Cardinality {
    fn cardinality(&self) -> Result<BigUint, ClarirsError>;
}

impl Cardinality for BoolAst<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self.reduce()? {
            ReduceResult::BitVec(..) => unreachable!(),
            ReduceResult::Bool(comparison_result) => match comparison_result {
                ComparisonResult::True => Ok(BigUint::one()),
                ComparisonResult::False => Ok(BigUint::one()),
                ComparisonResult::Maybe => Ok(BigUint::from(2u32)),
            },
        }
    }
}

impl Cardinality for BitVecAst<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self.reduce()? {
            ReduceResult::BitVec(strided_interval) => Ok(strided_interval.cardinality()),
            ReduceResult::Bool(..) => unreachable!(),
        }
    }
}

impl Cardinality for DynAst<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self {
            DynAst::BitVec(bv) => bv.cardinality(),
            DynAst::Boolean(bool) => bool.cardinality(),
            _ => Err(ClarirsError::UnsupportedOperation(
                "Cardinality is not supported for this type".to_string(),
            )),
        }
    }
}
