#![allow(non_snake_case)]

use std::sync::LazyLock;

use ast::args::ExtractPyArgs;
use dashmap::DashMap;
use pyo3::types::PyFrozenSet;
use pyo3::types::PyWeakrefMethods;
use pyo3::types::PyWeakrefReference;

use crate::ast::{And, Not, Or, Xor};
use crate::prelude::*;

static PY_BOOL_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Base, subclass, frozen, weakref, module="clarirs.ast.bool")]
pub struct Bool {
    pub(crate) inner: BoolAst<'static>,
}

impl Bool {
    pub fn new(py: Python, inner: &BoolAst<'static>) -> Result<Py<Bool>, ClaripyError> {
        if let Some(cache_hit) = PY_BOOL_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<Bool>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit.unbind())
        } else {
            let this = Py::new(
                py,
                PyClassInitializer::from(Base::new(py)).add_subclass(Bool {
                    inner: inner.clone(),
                }),
            )?;
            let weakref = PyWeakrefReference::new_bound(this.bind(py))?;
            PY_BOOL_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl Bool {
    #[getter]
    fn op(&self) -> String {
        self.inner.op().to_opstring()
    }

    #[getter]
    fn args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        self.inner.op().extract_py_args(py)
    }

    #[getter]
    fn variables(&self, py: Python) -> Result<Py<PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new_bound(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.to_object(py))
                .collect::<Vec<_>>()
                .iter(),
        )?
        .unbind())
    }

    #[getter]
    fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    fn hash(&self) -> u64 {
        self.inner.hash()
    }

    #[getter]
    fn depth(&self) -> u32 {
        self.inner.depth()
    }

    fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    fn is_true(self_: PyRef<Self>) -> bool {
        self_.inner.is_true()
    }

    fn is_false(self_: PyRef<Self>) -> bool {
        self_.inner.is_false()
    }
}

#[pyfunction]
pub fn BoolS(py: Python, name: &str) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.bools(name)?)
}
#[pyfunction]
pub fn BoolV(py: Python, value: bool) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.boolv(value)?)
}

#[pyfunction]
pub fn Eq_(py: Python, a: Bound<Bool>, b: Bound<Bool>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.eq_(&a.get().inner, &b.get().inner)?)
}

#[pyfunction]
pub fn Neq(py: Python, a: Bound<Bool>, b: Bound<Bool>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.neq(&a.get().inner, &b.get().inner)?)
}

#[pyfunction]
pub fn If(
    py: Python,
    cond: Bound<Bool>,
    then_: Bound<Bool>,
    else_: Bound<Bool>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.if_(&cond.get().inner, &then_.get().inner, &else_.get().inner)?,
    )
}

#[pyfunction(name = "true")]
pub fn true_op(py: Python) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.true_()?)
}
#[pyfunction(name = "false")]
pub fn false_op(py: Python) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.false_()?)
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Bool>()?;

    add_pyfunctions!(m, BoolS, BoolV, Not, And, Or, Xor, Eq_, If, true_op, false_op,);

    Ok(())
}
