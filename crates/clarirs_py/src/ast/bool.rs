#![allow(non_snake_case)]

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::LazyLock;

use ast::args::ExtractPyArgs;
use dashmap::DashMap;
use pyo3::types::PyFrozenSet;
use pyo3::types::PyWeakrefMethods;
use pyo3::types::PyWeakrefReference;

use crate::ast::{And, Not, Or, Xor};
use crate::prelude::*;

static BOOLS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BOOL_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Base, subclass, frozen, weakref, module="clarirs.ast.bool")]
pub struct Bool {
    pub(crate) inner: BoolAst<'static>,
}

impl Bool {
    pub fn new(py: Python, inner: &BoolAst<'static>) -> Result<Py<Bool>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name(
        py: Python,
        inner: &BoolAst<'static>,
        name: Option<String>,
    ) -> Result<Py<Bool>, ClaripyError> {
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
                PyClassInitializer::from(Base::new_with_name(py, name)).add_subclass(Bool {
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

    fn is_true(&self) -> bool {
        self.inner.is_true()
    }

    fn is_false(&self) -> bool {
        self.inner.is_false()
    }

    fn __invert__(&self, py: Python) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    fn __and__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    fn __or__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    fn __xor__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }
}

#[pyfunction(signature = (name, explicit_name = false))]
pub fn BoolS(py: Python, name: &str, explicit_name: bool) -> Result<Py<Bool>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = BOOLS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("Bool_{}_{}", name, counter)
    };
    Bool::new_with_name(py, &GLOBAL_CONTEXT.bools(&name)?, Some(name.clone()))
}

#[pyfunction]
pub fn BoolV(py: Python, value: bool) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.boolv(value)?)
}

#[pyfunction(name = "Eq")]
pub fn Eq_(py: Python, a: Bound<Bool>, b: Bound<Bool>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.eq_(&a.get().inner, &b.get().inner)?)
}

#[pyfunction]
pub fn Neq(py: Python, a: Bound<Bool>, b: Bound<Bool>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.neq(&a.get().inner, &b.get().inner)?)
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

    add_pyfunctions!(
        m,
        BoolS,
        BoolV,
        Not,
        And,
        Or,
        Xor,
        Eq_,
        super::If,
        true_op,
        false_op,
    );

    Ok(())
}
