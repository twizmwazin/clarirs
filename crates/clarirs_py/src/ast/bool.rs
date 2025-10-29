#![allow(non_snake_case)]

use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use ast::args::ExtractPyArgs;
use clarirs_core::algorithms::canonicalize;
use clarirs_core::algorithms::structurally_match;
use dashmap::DashMap;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyTuple;
use pyo3::types::{PyDict, PyFrozenSet, PyWeakrefMethods, PyWeakrefReference};

use crate::ast::{and, not, or, xor};
use crate::prelude::*;
use clarirs_core::smtlib::ToSmtLib;

use super::r#if;

static BOOLS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BOOL_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Base, subclass, frozen, weakref, module="claripy.ast.bool")]
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
    #[pyo3(signature = (op, args, annotations=None))]
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<Py<PyAny>>,
        annotations: Option<Vec<PyAnnotation>>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        let inner = match op {
            "BoolS" => GLOBAL_CONTEXT.bools(&args[0].extract::<String>(py)?)?,
            "BoolV" => GLOBAL_CONTEXT.boolv(args[0].extract::<bool>(py)?)?,
            "Not" => GLOBAL_CONTEXT.not(&args[0].cast_bound::<Bool>(py)?.get().inner)?,
            "And" => GLOBAL_CONTEXT.and(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
            )?,
            "Or" => GLOBAL_CONTEXT.or(
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
            "StrContains" => GLOBAL_CONTEXT.strcontains(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrPrefixOf" => GLOBAL_CONTEXT.strprefixof(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrSuffixOf" => GLOBAL_CONTEXT.strsuffixof(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrIsDigit" => {
                GLOBAL_CONTEXT.strisdigit(&args[0].cast_bound::<PyAstString>(py)?.get().inner)?
            }
            "If" => GLOBAL_CONTEXT.if_(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<Bool>(py)?.get().inner,
                &args[2].cast_bound::<Bool>(py)?.get().inner,
            )?,
            _ => return Err(ClaripyError::InvalidOperation(op.to_string())),
        };

        let inner_with_annotations = if let Some(annots) = annotations {
            let mut result = inner;
            for annot in annots {
                result = GLOBAL_CONTEXT.annotate(&result, annot.0)?;
            }
            result
        } else {
            inner
        };

        Bool::new(py, &inner_with_annotations)
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
    pub fn concrete(&self) -> bool {
        !self.inner.symbolic()
    }

    #[getter]
    pub fn annotations(&self) -> PyResult<Vec<PyAnnotation>> {
        Ok(self
            .inner
            .annotations()
            .iter()
            .cloned()
            .map(PyAnnotation::from)
            .collect())
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

    #[allow(clippy::type_complexity)]
    pub fn canonicalize<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<(HashMap<u64, Bound<'py, PyAny>>, usize, Bound<'py, Bool>), ClaripyError> {
        let (replacement_map, counter, canonical) = canonicalize(&self.inner.clone().into())?;
        let canonical_bool = Bool::new(
            py,
            &canonical.into_bool().ok_or(ClaripyError::InvalidOperation(
                "Canonicalization did not produce a Bool".to_string(),
            ))?,
        )?;

        let mut py_map = HashMap::new();
        for (hash, dynast) in replacement_map {
            let py_ast = Base::from_dynast(py, dynast)?;
            py_map.insert(hash, py_ast.into_any());
        }

        Ok((py_map, counter, canonical_bool))
    }

    pub fn identical(&self, other: Bound<'_, Base>) -> Result<bool, ClaripyError> {
        let other_dyn = Base::to_dynast(other)?;
        Ok(structurally_match(
            &DynAst::Boolean(self.inner.clone()),
            &other_dyn,
        )?)
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

    pub fn has_annotation_type(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<bool, ClaripyError> {
        Ok(self
            .annotations()?
            .iter()
            .any(|annotation| annotation_type.matches(annotation.0.type_())))
    }

    pub fn get_annotations_by_type(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<Vec<PyAnnotation>, ClaripyError> {
        Ok(self
            .annotations()?
            .into_iter()
            .filter(|annotation| annotation_type.matches(annotation.0.type_()))
            .collect())
    }

    pub fn get_annotation(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<Option<PyAnnotation>, ClaripyError> {
        Ok(self
            .annotations()?
            .into_iter()
            .find(|annotation| annotation_type.matches(annotation.0.type_())))
    }

    pub fn append_annotation<'py>(
        &self,
        py: Python<'py>,
        annotation: PyAnnotation,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        Self::new(
            py,
            &GLOBAL_CONTEXT.annotate(&self.inner, annotation.0.clone())?,
        )
    }

    pub fn append_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let mut inner = self.inner.clone();
        for annotation in annotations {
            inner = GLOBAL_CONTEXT.annotate(&inner, annotation.0)?;
        }
        Self::new(py, &inner)
    }

    #[pyo3(signature = (*annotations, remove_annotations = None))]
    pub fn annotate<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
        remove_annotations: Option<Vec<PyAnnotation>>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let new_annotations = self
            .annotations()?
            .iter()
            .filter(|a| {
                if let Some(remove_annotations) = &remove_annotations {
                    !remove_annotations.iter().any(|ra| ra.0 == a.0)
                } else {
                    true
                }
            })
            .map(|a| a.0.clone())
            .chain(annotations.into_iter().map(|a| a.0))
            .collect();
        let inner = self
            .inner
            .context()
            .make_bool_annotated(self.inner.op().clone(), new_annotations)?;
        Self::new(py, &inner)
    }

    pub fn insert_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let mut inner = self.inner.clone();
        for annotation in annotations {
            inner = GLOBAL_CONTEXT.annotate(&inner, annotation.0)?;
        }
        Self::new(py, &inner)
    }

    /// This actually just removes all annotations and adds the new ones.
    pub fn replace_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_bool_annotated(
            self.inner.op().clone(),
            annotations.into_iter().map(|a| a.0).collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn remove_annotation<'py>(
        &self,
        py: Python<'py>,
        annotation: PyAnnotation,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_bool_annotated(
            self.inner.op().clone(),
            self.inner
                .annotations()
                .iter()
                .filter(|a| **a != annotation.0)
                .cloned()
                .collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn remove_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let annotations_set: HashSet<_> = annotations.into_iter().map(|a| a.0).collect();
        let inner = self.inner.context().make_bool_annotated(
            self.inner.op().clone(),
            self.inner
                .annotations()
                .iter()
                .filter(|a| !annotations_set.contains(a))
                .cloned()
                .collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn clear_annotations<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self
            .inner
            .context()
            .make_bool_annotated(self.inner.op().clone(), Default::default())?;
        Self::new(py, &inner)
    }

    pub fn clear_annotation_type<'py>(
        &self,
        py: Python<'py>,
        annotation_type: PyAnnotationType,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_bool_annotated(
            self.inner.op().clone(),
            self.inner
                .annotations()
                .iter()
                .filter(|a| !annotation_type.matches(a.type_()))
                .cloned()
                .collect(),
        )?;
        Self::new(py, &inner)
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

    #[allow(clippy::type_complexity)]
    pub fn __reduce__<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<
        (
            Bound<'py, PyAny>,
            (String, Vec<Bound<'py, PyAny>>, Vec<PyAnnotation>),
        ),
        ClaripyError,
    > {
        let class = py.get_type::<Bool>();
        let op = self.op();
        let args = self.args(py)?;
        let annotations = self.annotations()?;
        Ok((class.into_any(), (op, args, annotations)))
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
    cases: Bound<'py, PyAny>,
    default: Bound<'py, PyAny>,
) -> PyResult<Bound<'py, PyAny>> {
    let mut sofar = default;

    let cases_vec = cases.try_iter()?.collect::<Result<Vec<_>, _>>()?;

    // Process cases in reverse order
    for i in cases_vec.iter().rev() {
        let mut iter = i.try_iter()?;

        let cond = iter.next().ok_or_else(|| {
            PyValueError::new_err("Each case must be a (condition, value) tuple")
        })??;
        let cond_bool = cond.extract::<CoerceBool>()?;
        let value = iter.next().ok_or_else(|| {
            PyValueError::new_err("Each case must be a (condition, value) tuple")
        })??;

        // Create If expression: If(cond, value, sofar)
        sofar = r#if(py, cond_bool, value, sofar)?.as_any().clone();
    }

    Ok(sofar)
}

/// Given an expression created by `ite_cases`, produce the cases that generated it
///
/// # Arguments
///
/// * `ast` - The AST expression to reverse
///
/// # Returns
///
/// A list of (condition, value) tuples
#[pyfunction]
pub fn reverse_ite_cases<'py>(
    py: Python<'py>,
    ast: Bound<'py, PyAny>,
) -> PyResult<Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)>> {
    let mut queue: Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)> =
        vec![(true_op(py)?.into_any(), ast)];
    let mut results = Vec::new();

    while let Some((condition, current_ast)) = queue.pop() {
        // Check if this is an If node
        if let Ok(base) = current_ast.cast::<Base>() {
            let op = base.getattr("op")?;
            let op_str: String = op.extract()?;

            if op_str == "If" {
                // Get the three arguments: condition, true_branch, false_branch
                let args = base.getattr("args")?;
                let args_vec: Vec<Bound<'py, PyAny>> = args.extract()?;

                if args_vec.len() == 3 {
                    let if_cond = args_vec[0].clone();
                    let true_branch = args_vec[1].clone();
                    let false_branch = args_vec[2].clone();

                    // Queue: And(condition, if_cond)
                    let new_cond_true =
                        and(py, vec![condition.clone(), if_cond.clone()])?.into_any();
                    queue.push((new_cond_true, true_branch));

                    // Queue: And(condition, Not(if_cond))
                    let not_if_cond = not(py, if_cond.cast::<Base>()?.clone())?;
                    let new_cond_false =
                        and(py, vec![condition.clone(), not_if_cond.into_any()])?.into_any();
                    queue.push((new_cond_false, false_branch));

                    continue;
                }
            }
        }

        // If not an If node, yield the condition and ast
        results.push((condition, current_ast));
    }

    Ok(results)
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
        let mut cases = Vec::new();
        for (k, v) in d.iter() {
            let cond = i.call_method1("__eq__", (k.clone(),))?;
            let tuple = PyTuple::new(py, &[cond, v])?;
            cases.push(tuple.into_any());
        }

        return ite_cases(py, cases.into_bound_py_any(py)?, default);
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
        let is_le: Bound<'py, Bool> = le.extract::<CoerceBool>()?.into();

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
        .cast::<Bool>()?
        .clone();

    // Create If expression: If(cond, val_low, val_high)
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
