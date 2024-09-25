#![allow(non_snake_case)]

use pyo3::prelude::*;

use crate::prelude::*;
use crate::{ast::py_factory::GLOBAL_CONTEXT, error::ClaripyError};

use super::shared_ops;
use super::{base::Base, py_factory::py_ast_from_astref, PyAst};

#[pyclass(extends=Base, subclass, frozen, weakref, module="claripy.ast.bool")]
pub struct Bool;

#[pymethods]
impl Bool {
    fn is_true(self_: PyRef<Self>) -> bool {
        self_.as_super().ast.is_true()
    }

    fn is_false(self_: PyRef<Self>) -> bool {
        self_.as_super().ast.is_false()
    }
}

impl PyAst for Bool {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Base::new_from_astref(ast_ref).add_subclass(Bool {})
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super()
    }
}

pyop!(BoolS, bools, Bool, name: String);
pyop!(BoolV, boolv, Bool, value: bool);

#[pyfunction(name = "true")]
pub fn true_op(py: Python) -> Result<Py<Bool>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.true_()?)
}
#[pyfunction(name = "false")]
pub fn false_op(py: Python) -> Result<Py<Bool>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.false_()?)
}

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<Bool>()?;

    add_pyfunctions!(
        m,
        BoolS,
        BoolV,
        shared_ops::Not,
        shared_ops::And,
        shared_ops::Or,
        shared_ops::Xor,
        shared_ops::Eq_,
        shared_ops::If,
        true_op,
        false_op,
    );

    Ok(())
}
