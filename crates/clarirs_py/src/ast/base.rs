use pyo3::types::PySet;

use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "clarirs.ast.base")]
#[derive(Clone)]
pub struct Base {
    errored: Py<PySet>,
}

impl Base {
    pub fn new(py: Python) -> Self {
        Base {
            errored: PySet::empty_bound(py)
                .expect("Failed to create PySet")
                .unbind(),
        }
    }
}

#[pymethods]
impl Base {
    #[getter]
    fn _errored(&self) -> Py<PySet> {
        self.errored.clone()
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}
