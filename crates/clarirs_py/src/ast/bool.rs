#![allow(non_snake_case)]

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::LazyLock;

use ast::args::ExtractPyArgs;
use dashmap::DashMap;
use pyo3::types::PyBytes;
use pyo3::types::PyFrozenSet;
use pyo3::types::PyWeakrefMethods;
use pyo3::types::PyWeakrefReference;

use crate::ast::{and, not, or, xor};
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
            let weakref = PyWeakrefReference::new(this.bind(py))?;
            PY_BOOL_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl Bool {
    #[new]
    pub fn py_new(py: Python, op: &str, args: Vec<PyObject>) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &match op {
                "BoolS" => GLOBAL_CONTEXT.bools(&args[0].extract::<String>(py)?)?,
                "BoolV" => GLOBAL_CONTEXT.boolv(args[0].extract::<bool>(py)?)?,
                "Not" => GLOBAL_CONTEXT.not(&args[0].downcast_bound::<Bool>(py)?.get().inner)?,
                "And" => GLOBAL_CONTEXT.and(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<Bool>(py)?.get().inner,
                )?,
                "Or" => GLOBAL_CONTEXT.or(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<Bool>(py)?.get().inner,
                )?,
                "Xor" => GLOBAL_CONTEXT.xor(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<Bool>(py)?.get().inner,
                )?,
                "__eq__" => {
                    if args[0].downcast_bound::<Bool>(py).is_ok() {
                        GLOBAL_CONTEXT.eq_(
                            &args[0].downcast_bound::<Bool>(py)?.get().inner,
                            &args[1].downcast_bound::<Bool>(py)?.get().inner,
                        )?
                    } else if args[0].downcast_bound::<BV>(py).is_ok() {
                        GLOBAL_CONTEXT.eq_(
                            &args[0].downcast_bound::<BV>(py)?.get().inner,
                            &args[1].downcast_bound::<BV>(py)?.get().inner,
                        )?
                    } else {
                        GLOBAL_CONTEXT.eq_(
                            &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                            &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                        )?
                    }
                }
                "__ne__" => {
                    if args[0].downcast_bound::<Bool>(py).is_ok() {
                        GLOBAL_CONTEXT.neq(
                            &args[0].downcast_bound::<Bool>(py)?.get().inner,
                            &args[1].downcast_bound::<Bool>(py)?.get().inner,
                        )?
                    } else if args[0].downcast_bound::<BV>(py).is_ok() {
                        GLOBAL_CONTEXT.neq(
                            &args[0].downcast_bound::<BV>(py)?.get().inner,
                            &args[1].downcast_bound::<BV>(py)?.get().inner,
                        )?
                    } else {
                        GLOBAL_CONTEXT.neq(
                            &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                            &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                        )?
                    }
                }
                "ULE" | "__le__" => GLOBAL_CONTEXT.ule(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "ULT" | "__lt__" => GLOBAL_CONTEXT.ult(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "UGE" | "__ge__" => GLOBAL_CONTEXT.uge(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "UGT" | "__gt__" => GLOBAL_CONTEXT.ugt(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SLT" => GLOBAL_CONTEXT.slt(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SLE" => GLOBAL_CONTEXT.sle(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SGT" => GLOBAL_CONTEXT.sgt(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SGE" => GLOBAL_CONTEXT.sge(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "fpEQ" => GLOBAL_CONTEXT.fp_eq(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpNEQ" => GLOBAL_CONTEXT.fp_neq(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpLT" => GLOBAL_CONTEXT.fp_lt(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpLEQ" => GLOBAL_CONTEXT.fp_leq(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpGT" => GLOBAL_CONTEXT.fp_gt(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpGEQ" => GLOBAL_CONTEXT.fp_geq(
                    &args[0].downcast_bound::<FP>(py)?.get().inner,
                    &args[1].downcast_bound::<FP>(py)?.get().inner,
                )?,
                "fpIsNan" => {
                    GLOBAL_CONTEXT.fp_is_nan(&args[0].downcast_bound::<FP>(py)?.get().inner)?
                }
                "fpIsInf" => {
                    GLOBAL_CONTEXT.fp_is_inf(&args[0].downcast_bound::<FP>(py)?.get().inner)?
                }
                "StrContains" => GLOBAL_CONTEXT.strcontains(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                )?,
                "StrPrefixOf" => GLOBAL_CONTEXT.strprefixof(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                )?,
                "StrSuffixOf" => GLOBAL_CONTEXT.strsuffixof(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                )?,
                "StrIsDigit" => GLOBAL_CONTEXT
                    .strisdigit(&args[0].downcast_bound::<PyAstString>(py)?.get().inner)?,
                "If" => GLOBAL_CONTEXT.if_(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<Bool>(py)?.get().inner,
                    &args[2].downcast_bound::<Bool>(py)?.get().inner,
                )?,
                _ => return Err(ClaripyError::InvalidOp(op.to_string())),
            },
        )
    }

    #[getter]
    pub fn op(&self) -> String {
        self.inner.op().to_opstring()
    }

    #[getter]
    pub fn args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        self.inner.op().extract_py_args(py)
    }

    #[getter]
    pub fn variables(&self, py: Python) -> Result<Py<PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.into_py_any(py))
                .collect::<Result<Vec<_>, _>>()?
                .iter(),
        )?
        .unbind())
    }

    #[getter]
    pub fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    #[getter]
    pub fn annotations(&self, py: Python) -> PyResult<Vec<PyObject>> {
        let pickle_loads = py.import("pickle")?.getattr("loads")?;
        self.inner
            .get_annotations()
            .iter()
            .map(|a| pickle_loads.call1((PyBytes::new(py, a.value()),)))
            .map(|a| a.map(|a| a.unbind()))
            .collect()
    }

    pub fn hash(&self) -> u64 {
        self.inner.hash()
    }

    pub fn __hash__(&self) -> usize {
        self.hash() as usize
    }

    #[getter]
    pub fn depth(&self) -> u32 {
        self.inner.depth()
    }

    pub fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    pub fn simplify(&self, py: Python) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(py, &self.inner.simplify()?)
    }

    pub fn is_true(&self) -> Result<bool, ClaripyError> {
        Ok(self.inner.simplify()?.is_true())
    }

    pub fn is_false(&self) -> Result<bool, ClaripyError> {
        Ok(self.inner.simplify()?.is_false())
    }

    #[getter]
    pub fn concrete_value(&self) -> Result<Option<bool>, ClaripyError> {
        Ok(match self.inner.simplify()?.op() {
            BooleanOp::BoolV(value) => Some(*value),
            _ => None,
        })
    }

    pub fn annotate(&self, py: Python, annotation: Bound<PyAny>) -> Result<Py<Bool>, ClaripyError> {
        let pickle_dumps = py.import("pickle")?.getattr("dumps")?;
        let annotation_bytes = pickle_dumps
            .call1((&annotation,))?
            .downcast::<PyBytes>()?
            .extract::<Vec<u8>>()?;
        let eliminatable = annotation.getattr("eliminatable")?.extract::<bool>()?;
        let relocatable = annotation.getattr("relocatable")?.extract::<bool>()?;
        Bool::new(
            py,
            &GLOBAL_CONTEXT.annotated(
                &self.inner,
                Annotation::new("".to_string(), annotation_bytes, eliminatable, relocatable),
            )?,
        )
    }

    pub fn __invert__(&self, py: Python) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __and__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __or__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __xor__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __eq__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.eq_(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __ne__(&self, py: Python, other: CoerceBool) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
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
        not,
        and,
        or,
        xor,
        Eq_,
        super::r#if,
        true_op,
        false_op,
    );

    Ok(())
}
