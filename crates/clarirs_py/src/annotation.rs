use pyo3::types::PyTuple;

use crate::prelude::*;

#[pyclass(name = "Annotation", module = "clarirs.annotation", subclass)]
pub struct PyAnnotation {
    eliminatable: bool,
    relocatable: bool,
}

#[pymethods]
impl PyAnnotation {
    #[new]
    fn new(eliminatable: bool, relocatable: bool) -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation {
            eliminatable,
            relocatable,
        })
    }

    fn __getnewargs__(&self) -> PyResult<(bool, bool)> {
        Ok((self.eliminatable, self.relocatable))
    }

    #[getter]
    fn eliminatable(&self) -> bool {
        self.eliminatable
    }

    #[getter]
    fn relocatable(&self) -> bool {
        self.relocatable
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct SimplificationAvoidanceAnnotation {}

#[pymethods]
impl SimplificationAvoidanceAnnotation {
    #[new]
    fn new() -> PyClassInitializer<Self> {
        PyAnnotation::new(false, false).add_subclass(SimplificationAvoidanceAnnotation {})
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::empty(py)
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct RegionAnnotation {}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct UninitializedAnnotation {}

#[pymethods]
impl UninitializedAnnotation {
    #[new]
    fn new() -> PyClassInitializer<Self> {
        PyAnnotation::new(false, true).add_subclass(UninitializedAnnotation {})
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::empty(py)
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyAnnotation>()?;
    m.add_class::<SimplificationAvoidanceAnnotation>()?;
    m.add_class::<RegionAnnotation>()?;
    m.add_class::<UninitializedAnnotation>()?;

    Ok(())
}
