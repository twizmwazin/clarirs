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

impl Cardinality for AstRef<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self.reduce()? {
            ReduceResult::Bool(comp) => match comp {
                ComparisonResult::True => Ok(BigUint::one()),
                ComparisonResult::False => Ok(BigUint::one()),
                ComparisonResult::Maybe => Ok(BigUint::from(2u32)),
            },
            ReduceResult::BitVec(si) => Ok(si.cardinality()),
        }
    }
}
