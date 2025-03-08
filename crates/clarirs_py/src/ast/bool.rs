#![allow(non_snake_case)]

use std::sync::LazyLock;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use ast::args::ExtractPyArgs;
use dashmap::DashMap;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyList;
use pyo3::types::PyTuple;
use pyo3::types::{PyBytes, PyDict, PyFrozenSet, PyWeakrefMethods, PyWeakrefReference};

use crate::ast::{and, not, or, xor};
use crate::prelude::*;
use clarirs_core::smtlib::ToSmtLib;

use super::r#if;

static BOOLS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BOOL_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Base, subclass, frozen, weakref, module="clarirs.ast.bool")]
pub struct Bool {
    pub(crate) inner: BoolAst<'static>,
}

impl Bool {
    pub fn new<'py>(
        py: Python<'py>,
        inner: &BoolAst<'static>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name<'py>(
        py: Python<'py>,
        inner: &BoolAst<'static>,
        name: Option<String>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        if let Some(cache_hit) = PY_BOOL_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<Bool>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit)
        } else {
            let this = Bound::new(
                py,
                PyClassInitializer::from(Base::new_with_name(py, name)).add_subclass(Bool {
                    inner: inner.clone(),
                }),
            )?;
            let weakref = PyWeakrefReference::new(&this)?;
            PY_BOOL_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl Bool {
    #[new]
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<PyObject>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
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
                _ => return Err(ClaripyError::InvalidOperation(op.to_string())),
            },
        )
    }

    #[getter]
    pub fn op(&self) -> String {
        self.inner.to_opstring()
    }

    #[getter]
    pub fn args<'py>(&self, py: Python<'py>) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        self.inner.extract_py_args(py)
    }

    #[getter]
    pub fn variables<'py>(&self, py: Python<'py>) -> Result<Bound<'py, PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.into_py_any(py))
                .collect::<Result<Vec<_>, _>>()?
                .iter(),
        )?)
    }

    #[getter]
    pub fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    #[getter]
    pub fn annotations<'py>(&self, py: Python<'py>) -> PyResult<Vec<Bound<'py, PyAny>>> {
        let pickle_loads = py.import("pickle")?.getattr("loads")?;
        self.inner
            .get_annotations()
            .iter()
            .map(|a| pickle_loads.call1((PyBytes::new(py, a.value()),)))
            .collect()
    }

    pub fn hash(&self) -> u64 {
        self.inner.hash()
    }

    pub fn __hash__(&self) -> usize {
        self.hash() as usize
    }

    pub fn __repr__(&self) -> String {
        self.inner.to_smtlib()
    }

    #[getter]
    pub fn depth(&self) -> u32 {
        self.inner.depth()
    }

    pub fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    pub fn simplify<'py>(&self, py: Python<'py>) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &self.inner.simplify()?)
    }

    pub fn size(&self) -> usize {
        1
    }

    pub fn __len__(&self) -> usize {
        self.size()
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

    pub fn annotate<'py>(
        &self,
        py: Python<'py>,
        annotation: Bound<'py, PyAny>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
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
                Annotation::new(
                    format!(
                        "{}.{}",
                        annotation.get_type().module()?.extract::<String>()?,
                        annotation.get_type().qualname()?.extract::<String>()?
                    ),
                    annotation_bytes,
                    eliminatable,
                    relocatable,
                ),
            )?,
        )
    }

    pub fn has_annotation_type<'py>(
        &self,
        py: Python<'py>,
        annotation_type: Bound<'py, PyAny>,
    ) -> Result<bool, ClaripyError> {
        Ok(self
            .annotations(py)?
            .iter()
            .any(|annotation| annotation.is_instance(&annotation_type).unwrap_or(false)))
    }

    pub fn get_annotations_by_type<'py>(
        &self,
        py: Python<'py>,
        annotation_type: Bound<'py, PyAny>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(self
            .annotations(py)?
            .iter()
            .filter(|annotation| annotation.is_instance(&annotation_type).unwrap_or(false))
            .cloned()
            .collect())
    }

    pub fn clear_annotations(self_: Bound<'_, Bool>) -> Result<Bound<'_, Bool>, ClaripyError> {
        let mut inner = self_.get().inner.clone();
        while let BooleanOp::Annotated(inner_, _) = inner.op() {
            inner = inner_.clone();
        }
        Bool::new(self_.py(), &inner)
    }

    pub fn __invert__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __and__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __or__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __xor__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __eq__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.eq_(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __ne__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, &<CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }
}

#[pyfunction(signature = (name, explicit_name = false))]
pub fn BoolS<'py>(
    py: Python<'py>,
    name: &str,
    explicit_name: bool,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = BOOLS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("Bool_{}_{}", name, counter)
    };
    Bool::new_with_name(py, &GLOBAL_CONTEXT.bools(&name)?, Some(name.clone()))
}

#[pyfunction]
pub fn BoolV(py: Python<'_>, value: bool) -> Result<Bound<'_, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.boolv(value)?)
}

#[pyfunction(name = "Eq")]
pub fn Eq_<'py>(
    py: Python<'py>,
    a: Bound<Bool>,
    b: Bound<Bool>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.eq_(&a.get().inner, &b.get().inner)?)
}

#[pyfunction]
pub fn Neq<'py>(
    py: Python<'py>,
    a: Bound<Bool>,
    b: Bound<Bool>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.neq(&a.get().inner, &b.get().inner)?)
}

#[pyfunction(name = "true")]
pub fn true_op(py: Python<'_>) -> Result<Bound<'_, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.true_()?)
}
#[pyfunction(name = "false")]
pub fn false_op(py: Python<'_>) -> Result<Bound<'_, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.false_()?)
}

/// Create an if-then-else tree from a list of condition-value pairs with a default value
///
/// # Arguments
///
/// * `cases` - A list of (condition, value) tuples
/// * `default` - The default value if none of the conditions are satisfied
///
/// # Returns
///
/// An expression encoding the result
#[pyfunction]
pub fn ite_cases<'py>(
    py: Python<'py>,
    cases: Bound<'py, PyList>,
    default: Bound<'py, PyAny>,
) -> PyResult<Bound<'py, PyAny>> {
    let mut sofar = default;

    // Process cases in reverse order
    let cases_len = cases.len();
    for i in (0..cases_len).rev() {
        let case = cases.get_item(i)?;
        let tuple = case.downcast::<PyTuple>()?;
        if tuple.len() != 2 {
            return Err(PyValueError::new_err(
                "Each case must be a (condition, value) tuple",
            ));
        }

        let cond = tuple.get_item(0)?;
        let cond_bool = cond.downcast::<Bool>()?.clone();
        let value = tuple.get_item(1)?;

        // Create If expression: If(cond, value, sofar)
        sofar = r#if(py, cond_bool, value, sofar)?.as_any().clone();
    }

    Ok(sofar)
}

/// Create a binary search tree for large tables
///
/// # Arguments
///
/// * `i` - The variable which may take on multiple values
/// * `d` - A dictionary mapping possible values for i to values which the result could be
/// * `default` - A default value if i matches none of the keys of d
///
/// # Returns
///
/// An expression encoding the result
#[pyfunction]
pub fn ite_dict<'py>(
    py: Python<'py>,
    i: Bound<'py, Base>,
    d: Bound<'py, PyDict>,
    default: Bound<'py, PyAny>,
) -> PyResult<Bound<'py, PyAny>> {
    // For small dictionaries, just use ite_cases
    if d.len() <= 4 {
        let cases = PyList::empty(py);
        for (k, v) in d.iter() {
            let cond = i.call_method1("__eq__", (k.clone(),))?;
            let tuple = PyTuple::new(py, &[cond, v])?;
            cases.append(tuple)?;
        }

        return ite_cases(py, Py::from(cases).bind(py).clone(), default);
    }

    // Binary search
    // Find the median
    let keys = d.keys();

    // Sort the keys
    keys.getattr("sort")?.call0()?;

    let split_idx = (keys.len() - 1) / 2;
    let split_val = keys.get_item(split_idx)?;

    // Split the dictionary
    let dict_low = PyDict::new(py);
    let dict_high = PyDict::new(py);

    for (k, v) in d.iter() {
        let le = k.call_method1("__le__", (split_val.clone(),))?;
        let is_le = le.downcast::<Bool>()?;

        if is_le.get().inner.is_true() {
            dict_low.set_item(k, v)?;
        } else {
            dict_high.set_item(k, v)?;
        }
    }

    // Recursively build trees for each part
    let val_low = if dict_low.is_empty() {
        default.clone()
    } else {
        ite_dict(py, i.clone(), dict_low, default.clone())?
    };

    let val_high = if dict_high.is_empty() {
        default.clone()
    } else {
        ite_dict(py, i.clone(), dict_high, default.clone())?
    };

    // Combine with an if-then-else
    let cond = i
        .call_method1("__le__", (split_val,))?
        .downcast::<Bool>()?
        .clone();

    // Create If expression: If(cond, val_low, val_high)
    let result = r#if(py, cond, val_low.clone(), val_high.clone())?;
    let coerced = result.clone().into_any();
    Ok(coerced)
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
        ite_cases,
        ite_dict,
    );

    Ok(())
}
