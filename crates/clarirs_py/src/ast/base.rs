use pyo3::types::PyList;

use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "clarirs.ast.base")]
#[derive(Clone)]
pub struct Base {
    errored: Py<PyList>,
}

impl Base {
    pub fn new(py: Python) -> Self {
        Base {
            errored: PyList::empty_bound(py).unbind(),
        }
    }
}

#[pymethods]
impl Base {
    #[getter]
    fn _errored(&self) -> Py<PyList> {
        self.errored.clone()
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}
