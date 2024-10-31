use crate::prelude::*;
use pyo3::{exceptions::PyRuntimeError, DowncastError, DowncastIntoError, PyErr, PyObject};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ClaripyError {
    #[error("Clarirs error: {0}")]
    ClarirsError(String),
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
}

impl From<ClarirsError> for ClaripyError {
    fn from(e: ClarirsError) -> Self {
        ClaripyError::ClarirsError(format!("{}", e))
    }
}

impl From<&ClarirsError> for ClaripyError {
    fn from(e: &ClarirsError) -> Self {
        ClaripyError::ClarirsError(format!("{}", e))
    }
}

impl From<PyErr> for ClaripyError {
    fn from(e: PyErr) -> Self {
        ClaripyError::PythonError(format!("{}", e))
    }
}

impl From<ClaripyError> for PyErr {
    fn from(e: ClaripyError) -> Self {
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
