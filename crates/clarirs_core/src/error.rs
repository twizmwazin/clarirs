use std::sync::PoisonError;

use clarirs_num::BitVecError;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ClarirsError {
    #[error("Cache lock poisoned")]
    CacheLockPoisoned,
    #[error("Unsupported operation")]
    UnsupportedOperation,
    #[error("Invalid arguments")]
    InvalidArguments,
    #[error("Invalid AST Type: {:?}", .0)]
    InvalidAst(String),
    #[error("IO Error: {:?}", .0)]
    IoError(#[from] std::io::Error),
    #[error("BitVector too short: {value:?} is too short for length {length}")]
    BitVectorTooShort {
        value: num_bigint::BigUint,
        length: usize,
    },
    #[error("Usatisfiable constraints")]
    UnsatisfiableConstraints,
    #[error("Type error: {:?}", .0)]
    TypeError(String),
    #[error("BitVector not bite-sized: {length:?} is not a multiple of 8")]
    BitVectorNotByteSized { length: usize },
    #[error("AST not represented in model")]
    AstNotInModel,
    #[error("Conversion error: {:?}", .0)]
    ConversionError(String),
    #[error("UNSAT")]
    Unsat,
    #[error("Unknown error: {:?}", .0)]
    UnknownError(String),
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
        }
    }
}
