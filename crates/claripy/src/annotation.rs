use crate::prelude::*;

#[pyclass(name = "Annotation", module = "claripy.annotation", subclass)]
pub struct PyAnnotation { }

#[pyclass(extends = PyAnnotation, module = "claripy.annotation", subclass)]
pub struct SimplificationAvoidanceAnnotation { }

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<PyAnnotation>()?;
    m.add_class::<SimplificationAvoidanceAnnotation>()?;

    Ok(())
}
