use std::{
    any::Any,
    hash::{DefaultHasher, Hash, Hasher},
};

use pyo3::types::PyTuple;

use crate::prelude::*;

#[pyclass(name = "Annotation", module = "clarirs.annotation", subclass, frozen)]
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

    fn __hash__(self_: Bound<PyAnnotation>) -> Result<isize, ClaripyError> {
        let mut hasher = DefaultHasher::new();

        self_
            .get_type()
            .name()?
            .extract::<String>()?
            .hash(&mut hasher);
        self_.get().eliminatable.hash(&mut hasher);
        self_.get().relocatable.hash(&mut hasher);

        Ok(hasher.finish() as isize)
    }

    fn __eq__(self_: Bound<PyAnnotation>, other: Bound<PyAny>) -> PyResult<bool> {
        if let Ok(other) = other.downcast::<PyAnnotation>() {
            Ok(self_.get_type().name()?.extract::<String>()?
                == other.get_type().name()?.extract::<String>()?
                && self_.get().eliminatable == other.get().eliminatable
                && self_.get().relocatable == other.get().relocatable)
        } else {
            Ok(false)
        }
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
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

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
pub struct RegionAnnotation {}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
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
