use crate::ast::bits::Bits;
use crate::prelude::*;

#[pyclass(extends=Bits, subclass, frozen, module="claripy.ast.string")]
pub struct String {}

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<String>()?;
    Ok(())
}
