use pyo3::exceptions::PyException;

use crate::prelude::*;

#[pyclass(name = "ClaripyError", extends = PyException, module = "clarirs.error", subclass)]
pub struct PyClaripyError;

#[pyclass(extends = PyClaripyError, module = "clarirs.error", subclass)]
pub struct UnsatError;
#[pyclass(extends = PyClaripyError, module = "clarirs.error", subclass)]
pub struct ClaripyFrontendError;
#[pyclass(extends = PyClaripyError, module = "clarirs.error", subclass)]
pub struct ClaripySolverInterruptError;
#[pyclass(extends = PyClaripyError, module = "clarirs.error", subclass)]
pub struct ClaripyOperationError;
#[pyclass(extends = PyClaripyError, module = "clarirs.error", subclass)]
pub struct ClaripyZeroDivisionError;
