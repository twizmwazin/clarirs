use std::sync::PoisonError;

use clarirs_num::BitVecError;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ClarirsError {
    #[error("Cache lock poisoned")]
    CacheLockPoisoned,
    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),
    #[error("Invalid arguments: {0}")]
    InvalidArguments(String),
    #[error("Division by zero error")]
    DivisionByZero,
    #[error("Invalid extract bounds: upper: {upper}, lower: {lower}, length: {length}")]
    InvalidExtractBounds { upper: u32, lower: u32, length: u32 },
    #[error("BitVector length {size} must be a multiple of {bits}.")]
    InvalidChopSize { size: u32, bits: u32 },
    #[error("Type error: {:?}", .0)]
    TypeError(String),
    #[error("BitVector not byte-sized: {length:?} is not a multiple of 8")]
    BitVectorNotByteSized { length: u32 },
    #[error("BitVector lengths must match: {left} != {right}")]
    MismatchedLengths { left: u32, right: u32 },
    #[error("Conversion error: {:?}", .0)]
    ConversionError(String),
    #[error("UNSAT")]
    Unsat,
    #[error("Solver returned unknown: {0}")]
    SolverUnknown(String),
    #[error("Empty traversal result")]
    EmptyTraversal,
    #[error("Backend error ({0}): {1}")]
    BackendError(&'static str, String),
    #[error("Missing child at index {0}")]
    MissingChild(usize),
}

impl<T> From<PoisonError<T>> for ClarirsError {
    fn from(_: PoisonError<T>) -> Self {
        ClarirsError::CacheLockPoisoned
    }
}

impl From<BitVecError> for ClarirsError {
    fn from(e: BitVecError) -> Self {
        match e {
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
            BitVecError::DivisionByZero => ClarirsError::DivisionByZero,
            BitVecError::ConversionError => {
                ClarirsError::ConversionError("BitVec conversion error".to_string())
            }
            BitVecError::MismatchedLengths { left, right } => {
                ClarirsError::MismatchedLengths { left, right }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_simple_variants() {
        assert_eq!(
            ClarirsError::CacheLockPoisoned.to_string(),
            "Cache lock poisoned"
        );
        assert_eq!(ClarirsError::DivisionByZero.to_string(), "Division by zero error");
        assert_eq!(ClarirsError::Unsat.to_string(), "UNSAT");
        assert_eq!(
            ClarirsError::EmptyTraversal.to_string(),
            "Empty traversal result"
        );
    }

    #[test]
    fn test_display_variants_with_string_payloads() {
        assert_eq!(
            ClarirsError::UnsupportedOperation("frobnicate".to_string()).to_string(),
            "Unsupported operation: frobnicate"
        );
        assert_eq!(
            ClarirsError::InvalidArguments("bad arg".to_string()).to_string(),
            "Invalid arguments: bad arg"
        );
        // TypeError and ConversionError debug-format their payload, so the
        // message includes quotes around the inner string.
        assert_eq!(
            ClarirsError::TypeError("mismatch".to_string()).to_string(),
            "Type error: \"mismatch\""
        );
        assert_eq!(
            ClarirsError::ConversionError("oops".to_string()).to_string(),
            "Conversion error: \"oops\""
        );
        assert_eq!(
            ClarirsError::SolverUnknown("timeout".to_string()).to_string(),
            "Solver returned unknown: timeout"
        );
        assert_eq!(
            ClarirsError::BackendError("z3", "boom".to_string()).to_string(),
            "Backend error (z3): boom"
        );
        assert_eq!(
            ClarirsError::MissingChild(2).to_string(),
            "Missing child at index 2"
        );
    }

    #[test]
    fn test_display_structured_variants() {
        assert_eq!(
            ClarirsError::InvalidExtractBounds {
                upper: 7,
                lower: 4,
                length: 4
            }
            .to_string(),
            "Invalid extract bounds: upper: 7, lower: 4, length: 4"
        );
        assert_eq!(
            ClarirsError::InvalidChopSize { size: 12, bits: 8 }.to_string(),
            "BitVector length 12 must be a multiple of 8."
        );
        assert_eq!(
            ClarirsError::BitVectorNotByteSized { length: 12 }.to_string(),
            "BitVector not byte-sized: 12 is not a multiple of 8"
        );
        assert_eq!(
            ClarirsError::MismatchedLengths { left: 8, right: 16 }.to_string(),
            "BitVector lengths must match: 8 != 16"
        );
    }

    #[test]
    fn test_from_poison_error() {
        let err: ClarirsError = PoisonError::new(42u32).into();
        assert!(matches!(err, ClarirsError::CacheLockPoisoned));

        // Also via a genuinely poisoned lock
        let mutex = std::sync::Mutex::new(0u32);
        let _ = std::panic::catch_unwind(|| {
            let _guard = mutex.lock().unwrap();
            panic!("poison it");
        });
        let err: ClarirsError = mutex.lock().unwrap_err().into();
        assert!(matches!(err, ClarirsError::CacheLockPoisoned));
    }

    #[test]
    fn test_from_bitvec_error() {
        let err: ClarirsError = BitVecError::BitVectorNotByteSized { length: 9 }.into();
        assert!(matches!(
            err,
            ClarirsError::BitVectorNotByteSized { length: 9 }
        ));

        let err: ClarirsError = BitVecError::InvalidExtractBounds {
            upper: 10,
            lower: 2,
            length: 8,
        }
        .into();
        assert!(matches!(
            err,
            ClarirsError::InvalidExtractBounds {
                upper: 10,
                lower: 2,
                length: 8
            }
        ));

        let err: ClarirsError = BitVecError::InvalidChopSize { size: 10, bits: 4 }.into();
        assert!(matches!(
            err,
            ClarirsError::InvalidChopSize { size: 10, bits: 4 }
        ));

        let err: ClarirsError = BitVecError::DivisionByZero.into();
        assert!(matches!(err, ClarirsError::DivisionByZero));

        let err: ClarirsError = BitVecError::ConversionError.into();
        match err {
            ClarirsError::ConversionError(msg) => {
                assert_eq!(msg, "BitVec conversion error");
            }
            other => panic!("expected ConversionError, got {other:?}"),
        }

        let err: ClarirsError = BitVecError::MismatchedLengths { left: 4, right: 8 }.into();
        assert!(matches!(
            err,
            ClarirsError::MismatchedLengths { left: 4, right: 8 }
        ));
    }
}
