use crate::prelude::*;

#[pyclass(extends=Base, subclass, frozen, weakref, module="claripy.ast.bits")]
pub struct Bits;

impl Bits {
    pub fn new() -> Self {
        Bits {}
    }
}

impl PyAst for Bits {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Base::new_from_astref(ast_ref).add_subclass(Bits::new())
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super()
    }
}

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<Bits>()?;
    Ok(())
}
