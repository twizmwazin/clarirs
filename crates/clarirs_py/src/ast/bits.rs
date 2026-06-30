use pyo3_stub_gen::derive::gen_stub_pyclass;

use crate::prelude::*;

#[gen_stub_pyclass]
#[pyclass(extends=Base, subclass, frozen, weakref, module="claripy.ast.bits")]
#[derive(Default)]
pub struct Bits;

impl Bits {
    pub fn new() -> Self {
        Bits {}
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Bits>()?;
    Ok(())
}
