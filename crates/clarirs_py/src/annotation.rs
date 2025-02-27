use crate::prelude::*;

#[pyclass(name = "Annotation", module = "clarirs.annotation", subclass)]
pub struct PyAnnotation {}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct SimplificationAvoidanceAnnotation {}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct RegionAnnotation {}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass)]
pub struct UninitializedAnnotation {}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyAnnotation>()?;
    m.add_class::<SimplificationAvoidanceAnnotation>()?;
    m.add_class::<RegionAnnotation>()?;
    m.add_class::<UninitializedAnnotation>()?;

    Ok(())
}
