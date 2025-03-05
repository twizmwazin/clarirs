use crate::prelude::*;
use crate::py_err::InvalidExtractBoundsError;
use clarirs_num::bitvec::BitVecError;
use pyo3::{
    DowncastError, DowncastIntoError, PyErr, PyObject,
    exceptions::{PyRuntimeError, PyZeroDivisionError},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ClaripyError {
    #[error("Clarirs error: {0}")]
    ClarirsError(String),
    #[error("Type error: {0}")]
    TypeError(String),
    #[error("Invalid operation: {0}")]
    InvalidOperation(String),
    #[error("Missing argument index: {0}")]
    MissingArgIndex(usize),
    #[error("Failed to extract argument")]
    FailedToExtractArg(PyObject),
    #[error("Python error: {0}")]
    PythonError(String),
    #[error("Casting error: {0}")]
    CastingError(String),
    #[error("Invalid argument type: {0}")]
    InvalidArgumentType(String),
    #[error("Division by zero error: attempted {dividend}/0")]
    DivisionByZero { dividend: num_bigint::BigUint },
    #[error("Invalid extract bounds: upper: {upper}, lower: {lower}, length: {length}")]
    InvalidExtractBounds { upper: u32, lower: u32, length: u32 },
    #[error("BitVec error: {0}")]
    BitVecError(#[from] BitVecError),
    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),
}

impl From<ClarirsError> for ClaripyError {
    fn from(e: ClarirsError) -> Self {
        match e {
            ClarirsError::DivisionByZero { dividend } => ClaripyError::DivisionByZero { dividend },
            ClarirsError::InvalidExtractBounds {
                upper,
                lower,
                length,
            } => ClaripyError::InvalidExtractBounds {
                upper,
                lower,
                length,
            },
            _ => ClaripyError::ClarirsError(format!("{}", e)),
        }
    }
}

impl From<PyErr> for ClaripyError {
    fn from(e: PyErr) -> Self {
        ClaripyError::PythonError(format!("{}", e))
    }
}

impl From<ClaripyError> for PyErr {
    fn from(e: ClaripyError) -> Self {
        match e {
            ClaripyError::DivisionByZero { dividend } => PyZeroDivisionError::new_err(format!(
                "Division by zero error: attempted {}/0",
                dividend
            )),
            ClaripyError::InvalidExtractBounds {
                upper,
                lower,
                length,
            } => InvalidExtractBoundsError::new_err(format!(
                "Invalid extract bounds: upper: {}, lower: {}, length: {}",
                upper, lower, length
            )),
            _ => PyRuntimeError::new_err(format!("{}", e)),
        }
    }
}

impl From<DowncastError<'_, '_>> for ClaripyError {
    fn from(e: DowncastError) -> Self {
        ClaripyError::CastingError(format!("{}", e))
    }
}

impl From<DowncastIntoError<'_>> for ClaripyError {
    fn from(e: DowncastIntoError) -> Self {
        ClaripyError::CastingError(format!("{}", e))
    }
}
