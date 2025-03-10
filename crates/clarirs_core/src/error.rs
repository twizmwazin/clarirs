use std::sync::PoisonError;

use clarirs_num::BitVecError;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ClarirsError {
    #[error("Cache lock poisoned")]
    CacheLockPoisoned,
    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),
    #[error("Invalid arguments")]
    InvalidArguments,
    #[error("BitVector too short: {value:?} is too short for length {length}")]
    BitVectorTooShort {
        value: num_bigint::BigUint,
        length: u32,
    },
    #[error("Division by zero error: attempted {dividend}/0")]
    DivisionByZero { dividend: num_bigint::BigUint },
    #[error("Invalid extract bounds: upper: {upper}, lower: {lower}, length: {length}")]
    InvalidExtractBounds { upper: u32, lower: u32, length: u32 },
    #[error(" BitVector length {size} must be a multiple of {bits}.")]
    InvalidChopSize { size: u32, bits: u32 },
    #[error("Type error: {:?}", .0)]
    TypeError(String),
    #[error("BitVector not bite-sized: {length:?} is not a multiple of 8")]
    BitVectorNotByteSized { length: u32 },
    #[error("Conversion error: {:?}", .0)]
    ConversionError(String),
    #[error("UNSAT")]
    Unsat,
}

impl<T> From<PoisonError<T>> for ClarirsError {
    fn from(_: PoisonError<T>) -> Self {
        ClarirsError::CacheLockPoisoned
    }
}

impl From<BitVecError> for ClarirsError {
    fn from(e: BitVecError) -> Self {
        match e {
            BitVecError::BitVectorTooShort { value, length } => {
                ClarirsError::BitVectorTooShort { value, length }
            }
            BitVecError::BitVectorNotByteSized { length } => {
                ClarirsError::BitVectorNotByteSized { length }
            }
            BitVecError::InvalidExtractBounds {
                upper,
                lower,
                length,
            } => ClarirsError::InvalidExtractBounds {
                upper,
                lower,
                length,
            },
            BitVecError::InvalidChopSize { size, bits } => {
                ClarirsError::InvalidChopSize { size, bits }
            }
            BitVecError::DivisionByZero { dividend } => ClarirsError::DivisionByZero { dividend },
        }
    }
}
