#![allow(non_snake_case)]

use crate::ast::{base::Base, bool::Bool};
use crate::prelude::*;

#[pyfunction]
pub fn Not(py: Python, b: PyRef<Base>) -> Result<Py<Base>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.not(&get_astref(b))?)
}

#[pyfunction]
pub fn And(py: Python, lhs: PyRef<Base>, rhs: PyRef<Base>) -> Result<Py<Base>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.and(&get_astref(lhs), &get_astref(rhs))?)
}

#[pyfunction]
pub fn Or(py: Python, lhs: PyRef<Base>, rhs: PyRef<Base>) -> Result<Py<Base>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.or(&get_astref(lhs), &get_astref(rhs))?)
}

#[pyfunction]
pub fn Xor(py: Python, lhs: PyRef<Base>, rhs: PyRef<Base>) -> Result<Py<Base>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.xor(&get_astref(lhs), &get_astref(rhs))?)
}

#[allow(non_snake_case)]
#[pyfunction(name = "Eq")]
pub fn Eq_(py: Python, lhs: PyRef<Base>, rhs: PyRef<Base>) -> Result<Py<Bool>, ClaripyError> {
    py_ast_from_astref(
        py,
        crate::ast::py_factory::GLOBAL_CONTEXT
            .eq_(&crate::ast::get_astref(lhs), &crate::ast::get_astref(rhs))?,
    )
}

#[pyfunction]
pub fn If(
    py: Python,
    cond: PyRef<Bool>,
    then_: PyRef<Bool>,
    else_: PyRef<Bool>,
) -> Result<Py<Bool>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.if_(&get_astref(cond), &get_astref(then_), &get_astref(else_))?,
    )
}
