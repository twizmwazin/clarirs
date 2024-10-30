use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "clarirs.ast.base")]
#[derive(Clone, Default)]
pub struct Base {}

#[pymethods]
impl Base {}

impl Base {
    pub fn new() -> Self {
        Base {}
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}
