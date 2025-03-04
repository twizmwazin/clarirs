use crate::prelude::*;
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
    #[error("BitVec error: {0}")]
    BitVecError(#[from] BitVecError),
    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),
}

impl From<ClarirsError> for ClaripyError {
    fn from(e: ClarirsError) -> Self {
        match e {
            ClarirsError::TypeError(e) => ClaripyError::TypeError(e),
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
        if let ClaripyError::InvalidOperation(ref msg) = e {
            println!("{}", msg);
            if msg.contains("Division by zero") {
                return PyZeroDivisionError::new_err(msg.clone());
            }
        }
        PyRuntimeError::new_err(format!("{}", e))
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
