use crate::{prelude::*, py_err};
use clarirs_num::bitvec::BitVecError;
use pyo3::{
    DowncastError, DowncastIntoError, Py, PyAny, PyErr,
    exceptions::{PyValueError, PyZeroDivisionError},
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
    FailedToExtractArg(Py<PyAny>),
    #[error("Python error: {0}")]
    PythonError(Py<PyAny>),
    #[error("Casting error: {0}")]
    CastingError(String),
    #[error("Invalid argument type: {0}")]
    InvalidArgumentType(String),
    #[error("Division by zero error: attempted {dividend}/0")]
    DivisionByZero { dividend: num_bigint::BigUint },
    #[error("Invalid extract bounds: upper: {upper}, lower: {lower}, length: {length}")]
    InvalidExtractBounds { upper: u32, lower: u32, length: u32 },
    #[error("BitVector length {size} must be a multiple of {bits}.")]
    InvalidChopSize { size: u32, bits: u32 },
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
            ClarirsError::InvalidChopSize { size, bits } => {
                ClaripyError::InvalidChopSize { size, bits }
            }
            ClarirsError::TypeError(e) => ClaripyError::TypeError(e),
            ClarirsError::UnsupportedOperation(e) => ClaripyError::UnsupportedOperation(e),
            _ => ClaripyError::ClarirsError(format!("{e}")),
        }
    }
}

impl From<&ClarirsError> for ClaripyError {
    fn from(e: &ClarirsError) -> Self {
        ClaripyError::ClarirsError(format!("{e}"))
    }
}

impl From<PyErr> for ClaripyError {
    fn from(e: PyErr) -> Self {
        Python::attach(|py| ClaripyError::PythonError(e.value(py).as_any().clone().unbind()))
    }
}

impl From<ClaripyError> for PyErr {
    fn from(e: ClaripyError) -> Self {
        match e {
            ClaripyError::DivisionByZero { dividend } => PyZeroDivisionError::new_err(format!(
                "Division by zero error: attempted {dividend}/0"
            )),
            ClaripyError::InvalidExtractBounds {
                upper,
                lower,
                length,
            } => py_err::InvalidExtractBoundsError::new_err(format!(
                "Invalid extract bounds: upper: {upper}, lower: {lower}, length: {length}"
            )),
            ClaripyError::InvalidChopSize { size, bits } => PyValueError::new_err(format!(
                "BitVector length {size} must be a multiple of {bits}."
            )),
            ClaripyError::InvalidOperation(e) => py_err::ClaripyOperationError::new_err(e),
            ClaripyError::TypeError(e) => py_err::ClaripyTypeError::new_err(e),
            ClaripyError::PythonError(o) => {
                Python::attach(|py| PyErr::from_value(o.bind(py).clone()))
            }
            _ => py_err::ClaripyError::new_err(format!("{e}")),
        }
    }
}

impl From<DowncastError<'_, '_>> for ClaripyError {
    fn from(e: DowncastError) -> Self {
        ClaripyError::CastingError(format!("{e}"))
    }
}

impl From<DowncastIntoError<'_>> for ClaripyError {
    fn from(e: DowncastIntoError) -> Self {
        ClaripyError::CastingError(format!("{e}"))
    }
}
