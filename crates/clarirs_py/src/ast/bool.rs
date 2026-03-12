#![allow(non_snake_case)]

use std::sync::LazyLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use clarirs_vsa::reduce::Reduce;
use clarirs_vsa::strided_interval::ComparisonResult;
use dashmap::DashMap;
use pyo3::exceptions::PyValueError;
use pyo3::types::{PyDict, PyTuple, PyWeakrefReference};

use crate::ast::{and, not, or, xor};
use crate::prelude::*;

use super::r#if;

static BOOLS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BOOL_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Base, subclass, frozen, weakref, module="claripy.ast.bool")]
pub struct Bool {
    pub(crate) inner: BoolAst<'static>,
}

impl_py_ast_common! {
    type: Bool,
    inner_type: BoolAst<'static>,
    cache: PY_BOOL_CACHE,
    simplify: |inner| inner.simplify()?,
    make_annotated: make_bool_annotated,
    make_clear: make_bool,
    dynast_variant: Boolean,
    dynast_into: into_bool,
    canon_name: "Bool",
    init_chain: Base => Bool,
}

#[pymethods]
impl Bool {
    #[new]
    #[pyo3(signature = (op, args, annotations=None))]
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<Py<PyAny>>,
        annotations: Option<Vec<PyAnnotation>>,
    ) -> Result<Py<Bool>, ClaripyError> {
        let inner = match op {
            "BoolS" => GLOBAL_CONTEXT.bools(&args[0].extract::<String>(py)?)?,
            "BoolV" => GLOBAL_CONTEXT.boolv(args[0].extract::<bool>(py)?)?,
            "Not" => GLOBAL_CONTEXT.not(&args[0].cast_bound::<Bool>(py)?.get().inner)?,
            "And" => GLOBAL_CONTEXT.and2(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
            )?,
            "Or" => GLOBAL_CONTEXT.or2(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
            )?,
            "Xor" => GLOBAL_CONTEXT.xor(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
            )?,
            "__eq__" => {
                if args[0].cast_bound::<Bool>(py).is_ok() {
                    GLOBAL_CONTEXT.eq_(
                        &args[0].cast_bound::<Bool>(py)?.get().inner,
                        &args[1].cast_bound::<Bool>(py)?.get().inner,
                    )?
                } else if args[0].cast_bound::<BV>(py).is_ok() {
                    GLOBAL_CONTEXT.eq_(
                        &args[0].cast_bound::<BV>(py)?.get().inner,
                        &args[1].cast_bound::<BV>(py)?.get().inner,
                    )?
                } else {
                    GLOBAL_CONTEXT.eq_(
                        &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                        &args[1].cast_bound::<PyAstString>(py)?.get().inner,
                    )?
                }
            }
            "__ne__" => {
                if args[0].cast_bound::<Bool>(py).is_ok() {
                    GLOBAL_CONTEXT.neq(
                        &args[0].cast_bound::<Bool>(py)?.get().inner,
                        &args[1].cast_bound::<Bool>(py)?.get().inner,
                    )?
                } else if args[0].cast_bound::<BV>(py).is_ok() {
                    GLOBAL_CONTEXT.neq(
                        &args[0].cast_bound::<BV>(py)?.get().inner,
                        &args[1].cast_bound::<BV>(py)?.get().inner,
                    )?
                } else {
                    GLOBAL_CONTEXT.neq(
                        &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                        &args[1].cast_bound::<PyAstString>(py)?.get().inner,
                    )?
                }
            }
            "ULE" | "__le__" => GLOBAL_CONTEXT.ule(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "ULT" | "__lt__" => GLOBAL_CONTEXT.ult(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "UGE" | "__ge__" => GLOBAL_CONTEXT.uge(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "UGT" | "__gt__" => GLOBAL_CONTEXT.ugt(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "SLT" => GLOBAL_CONTEXT.slt(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "SLE" => GLOBAL_CONTEXT.sle(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "SGT" => GLOBAL_CONTEXT.sgt(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "SGE" => GLOBAL_CONTEXT.sge(
                &args[0].cast_bound::<BV>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
            )?,
            "fpEQ" => GLOBAL_CONTEXT.fp_eq(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpNEQ" => GLOBAL_CONTEXT.fp_neq(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpLT" => GLOBAL_CONTEXT.fp_lt(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpLEQ" => GLOBAL_CONTEXT.fp_leq(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpGT" => GLOBAL_CONTEXT.fp_gt(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpGEQ" => GLOBAL_CONTEXT.fp_geq(
                &args[0].cast_bound::<FP>(py)?.get().inner,
                &args[1].cast_bound::<FP>(py)?.get().inner,
            )?,
            "fpIsNan" => GLOBAL_CONTEXT.fp_is_nan(&args[0].cast_bound::<FP>(py)?.get().inner)?,
            "fpIsInf" => GLOBAL_CONTEXT.fp_is_inf(&args[0].cast_bound::<FP>(py)?.get().inner)?,
            "StrContains" => GLOBAL_CONTEXT.str_contains(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrPrefixOf" => GLOBAL_CONTEXT.str_prefix_of(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrSuffixOf" => GLOBAL_CONTEXT.str_suffix_of(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrIsDigit" => {
                GLOBAL_CONTEXT.str_is_digit(&args[0].cast_bound::<PyAstString>(py)?.get().inner)?
            }
            "If" => GLOBAL_CONTEXT.ite(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
                &args[2].cast_bound::<Bool>(py)?.get().inner,
            )?,
            _ => return Err(ClaripyError::InvalidOperation(op.to_string())),
        };

        let inner_with_annotations = if let Some(annots) = annotations {
            GLOBAL_CONTEXT.annotate(&inner, annots.into_iter().map(|a| a.0))?
        } else {
            inner
        };

        Ok(Bool::new(py, &inner_with_annotations)?.unbind())
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
        Ok(match self.inner.simplify_ext(false, false)?.op() {
            BooleanOp::BoolV(value) => Some(*value),
            _ => None,
        })
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
            &GLOBAL_CONTEXT.and2(&self.inner, <CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __or__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.or2(&self.inner, <CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __xor__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, <CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __eq__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.eq_(&self.inner, <CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    pub fn __ne__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBool,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, <CoerceBool as Into<BoolAst>>::into(other))?,
        )
    }

    #[getter]
    pub fn cardinality(&self) -> Result<usize, ClaripyError> {
        match self.inner.reduce()? {
            ComparisonResult::True => Ok(1),
            ComparisonResult::False => Ok(1),
            ComparisonResult::Maybe => Ok(2),
        }
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
        format!("Bool_{name}_{counter}")
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
#[pyfunction]
pub fn ite_cases<'py>(
    py: Python<'py>,
    cases: Bound<'py, PyAny>,
    default: Bound<'py, PyAny>,
) -> PyResult<Bound<'py, PyAny>> {
    let mut sofar = default;

    let cases_vec = cases.try_iter()?.collect::<Result<Vec<_>, _>>()?;

    for i in cases_vec.iter().rev() {
        let mut iter = i.try_iter()?;

        let cond = iter.next().ok_or_else(|| {
            PyValueError::new_err("Each case must be a (condition, value) tuple")
        })??;
        let cond_bool = cond.extract::<CoerceBool>()?;
        let value = iter.next().ok_or_else(|| {
            PyValueError::new_err("Each case must be a (condition, value) tuple")
        })??;

        sofar = r#if(py, cond_bool, value, sofar)?.as_any().clone();
    }

    Ok(sofar)
}

/// Given an expression created by `ite_cases`, produce the cases that generated it
#[pyfunction]
pub fn reverse_ite_cases<'py>(
    py: Python<'py>,
    ast: Bound<'py, PyAny>,
) -> PyResult<Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)>> {
    let mut queue: Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)> =
        vec![(true_op(py)?.into_any(), ast)];
    let mut results = Vec::new();

    while let Some((condition, current_ast)) = queue.pop() {
        if let Ok(base) = current_ast.cast::<Base>() {
            let op = base.getattr("op")?;
            let op_str: String = op.extract()?;

            if op_str == "If" {
                let args = base.getattr("args")?;
                let args_vec: Vec<Bound<'py, PyAny>> = args.extract()?;

                if args_vec.len() == 3 {
                    let if_cond = args_vec[0].clone();
                    let true_branch = args_vec[1].clone();
                    let false_branch = args_vec[2].clone();

                    let new_cond_true =
                        and(py, vec![condition.clone(), if_cond.clone()])?.into_any();
                    queue.push((new_cond_true, true_branch));

                    let not_if_cond = not(py, if_cond.cast::<Base>()?.clone())?;
                    let new_cond_false =
                        and(py, vec![condition.clone(), not_if_cond.into_any()])?.into_any();
                    queue.push((new_cond_false, false_branch));

                    continue;
                }
            }
        }

        results.push((condition, current_ast));
    }

    Ok(results)
}

/// Create a binary search tree for large tables
#[pyfunction]
pub fn ite_dict<'py>(
    py: Python<'py>,
    i: Bound<'py, Base>,
    d: Bound<'py, PyDict>,
    default: Bound<'py, PyAny>,
) -> PyResult<Bound<'py, PyAny>> {
    if d.len() <= 4 {
        let mut cases = Vec::new();
        for (k, v) in d.iter() {
            let cond = i.call_method1("__eq__", (k.clone(),))?;
            let tuple = PyTuple::new(py, &[cond, v])?;
            cases.push(tuple.into_any());
        }

        return ite_cases(py, cases.into_bound_py_any(py)?, default);
    }

    let keys = d.keys();

    keys.getattr("sort")?.call0()?;

    let split_idx = (keys.len() - 1) / 2;
    let split_val = keys.get_item(split_idx)?;

    let dict_low = PyDict::new(py);
    let dict_high = PyDict::new(py);

    for (k, v) in d.iter() {
        let le = k.call_method1("__le__", (split_val.clone(),))?;
        let is_le: Bound<'py, Bool> = le.extract::<CoerceBool>()?.into();

        if is_le.get().inner.is_true() {
            dict_low.set_item(k, v)?;
        } else {
            dict_high.set_item(k, v)?;
        }
    }

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

    let cond = i
        .call_method1("__le__", (split_val,))?
        .cast::<Bool>()?
        .clone();

    let result = r#if(py, CoerceBool(cond), val_low.clone(), val_high.clone())?;
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
        reverse_ite_cases,
        ite_dict,
    );

    Ok(())
}
