use crate::prelude::*;

#[pyclass(name = "Annotation", module = "claripy.annotation", subclass)]
pub struct PyAnnotation {}

#[pyclass(extends = PyAnnotation, module = "claripy.annotation", subclass)]
pub struct SimplificationAvoidanceAnnotation {}

#[pyclass(extends = PyAnnotation, module = "claripy.annotation", subclass)]
pub struct RegionAnnotation {}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyAnnotation>()?;
    m.add_class::<SimplificationAvoidanceAnnotation>()?;
    m.add_class::<RegionAnnotation>()?;

    Ok(())
}
