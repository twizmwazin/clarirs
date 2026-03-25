use clarirs_core::prelude::*;
use num_bigint::BigUint;
use num_traits::One;

use crate::reduce::Reduce;
use crate::strided_interval::{ComparisonResult, StridedInterval};

pub trait Cardinality {
    fn cardinality(&self) -> Result<BigUint, ClarirsError>;
}

impl Cardinality for AstRef<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self.return_type() {
            AstType::Bool => {
                let result: ComparisonResult = self.reduce()?;
                match result {
                    ComparisonResult::True => Ok(BigUint::one()),
                    ComparisonResult::False => Ok(BigUint::one()),
                    ComparisonResult::Maybe => Ok(BigUint::from(2u32)),
                }
            }
            AstType::BitVec(_) => {
                let si: StridedInterval = self.reduce()?;
                Ok(si.cardinality())
            }
            _ => Err(ClarirsError::UnsupportedOperation(
                "Cardinality is not supported for this type".to_string(),
            )),
        }
    }
}
