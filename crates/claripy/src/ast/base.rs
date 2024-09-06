use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "claripy.ast.base")]
#[derive(Clone)]
pub struct Base {
    pub ast: AstRef<'static>,
}

#[pymethods]
impl Base {}

impl Base {
    pub fn new(ast: &AstRef<'static>) -> Self {
        Base { ast: ast.clone() }
    }
}

impl From<Base> for AstRef<'static> {
    fn from(base: Base) -> Self {
        base.ast
    }
}

impl PyAst for Base {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        PyClassInitializer::from(Base::new(ast_ref))
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<self::Base> {
        self_
    }
}

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}
