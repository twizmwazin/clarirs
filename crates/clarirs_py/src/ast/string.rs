#![allow(non_snake_case)]

use std::{
    collections::{HashMap, HashSet},
    sync::{
        LazyLock,
        atomic::{AtomicUsize, Ordering},
    },
};

use dashmap::DashMap;
use pyo3::types::{PyFrozenSet, PyWeakrefReference};

use crate::prelude::*;
use clarirs_core::{
    algorithms::{canonicalize, structurally_match},
    smtlib::ToSmtLib,
};

static STRINGS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_STRING_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> =
    LazyLock::new(DashMap::new);

#[pyclass(name="String", extends=Base, subclass, frozen, module="claripy.ast.strings")]
pub struct PyAstString {
    pub(crate) inner: StringAst<'static>,
}

impl PyAstString {
    pub fn new<'py>(
        py: Python<'py>,
        inner: &StringAst<'static>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name<'py>(
        py: Python<'py>,
        inner: &StringAst<'static>,
        name: Option<String>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        if let Some(cache_hit) = PY_STRING_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<PyAstString>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit)
        } else {
            let this = Py::new(
                py,
                PyClassInitializer::from(Base::new_with_name(py, name)).add_subclass(PyAstString {
                    inner: inner.clone(),
                }),
            )?;
            let weakref = PyWeakrefReference::new(this.bind(py))?;
            PY_STRING_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this.into_bound(py))
        }
    }
}

#[pymethods]
impl PyAstString {
    #[new]
    #[pyo3(signature = (op, args, annotations=None))]
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<Py<PyAny>>,
        annotations: Option<Vec<PyAnnotation>>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        let inner = match op {
            "StringS" => GLOBAL_CONTEXT.strings(&args[0].extract::<String>(py)?)?,
            "StringV" => GLOBAL_CONTEXT.stringv(&args[0].extract::<String>(py)?)?,
            "StrConcat" => GLOBAL_CONTEXT.strconcat(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "StrSubstr" => GLOBAL_CONTEXT.strsubstr(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<BV>(py)?.get().inner,
                &args[2].cast_bound::<BV>(py)?.get().inner,
            )?,
            "StrReplace" => GLOBAL_CONTEXT.strreplace(
                &args[0].cast_bound::<PyAstString>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
                &args[2].cast_bound::<PyAstString>(py)?.get().inner,
            )?,
            "IntToStr" => GLOBAL_CONTEXT.bvtostr(&args[0].cast_bound::<BV>(py)?.get().inner)?,
            "If" => GLOBAL_CONTEXT.if_(
                &args[0].cast_bound::<Bool>(py)?.get().inner,
                &args[1].cast_bound::<PyAstString>(py)?.get().inner,
                &args[2].cast_bound::<PyAstString>(py)?.get().inner,
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

        PyAstString::new(py, &inner_with_annotations)
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

    pub fn canonicalize<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<
        (
            HashMap<u64, Bound<'py, PyAny>>,
            usize,
            Bound<'py, PyAstString>,
        ),
        ClaripyError,
    > {
        let (replacement_map, counter, canonical) = canonicalize(&self.inner.clone().into())?;
        let canonical_string = PyAstString::new(
            py,
            &canonical
                .into_string()
                .ok_or(ClaripyError::InvalidOperation(
                    "Canonicalization did not produce a String".to_string(),
                ))?,
        )?;

        let mut py_map = HashMap::new();
        for (hash, dynast) in replacement_map {
            let py_ast = Base::from_dynast(py, dynast)?;
            py_map.insert(hash, py_ast.into_any());
        }

        Ok((py_map, counter, canonical_string))
    }

    pub fn identical(&self, other: Bound<'_, Base>) -> Result<bool, ClaripyError> {
        let other_dyn = Base::to_dynast(other)?;
        Ok(structurally_match(
            &DynAst::String(self.inner.clone()),
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

    pub fn simplify<'py>(&self, py: Python<'py>) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        PyAstString::new(py, &self.inner.simplify()?)
    }

    #[getter]
    pub fn concrete_value(&self) -> Result<Option<String>, ClaripyError> {
        Ok(match self.inner.simplify()?.op() {
            StringOp::StringV(value) => Some(value.clone()),
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
            .make_string_annotated(self.inner.op().clone(), new_annotations)?;
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
        let inner = self.inner.context().make_string_annotated(
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
        let inner = self.inner.context().make_string_annotated(
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
        let inner = self.inner.context().make_string_annotated(
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
        let inner = self.inner.context().make_string(self.inner.op().clone())?;
        Self::new(py, &inner)
    }

    pub fn clear_annotation_type<'py>(
        &self,
        py: Python<'py>,
        annotation_type: PyAnnotationType,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_string_annotated(
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

    pub fn __add__<'py>(
        &self,
        py: Python<'py>,
        other: Bound<'py, PyAstString>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        PyAstString::new(
            py,
            &GLOBAL_CONTEXT.strconcat(&self.inner, &other.get().inner)?,
        )
    }

    pub fn __eq__<'py>(
        &self,
        py: Python<'py>,
        other: Bound<'py, PyAstString>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.streq(&self.inner, &other.get().inner)?)
    }

    pub fn __ne__<'py>(
        &self,
        py: Python<'py>,
        other: Bound<'py, PyAstString>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.strneq(&self.inner, &other.get().inner)?)
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
        let class = py.get_type::<PyAstString>();
        let op = self.op();
        let args = self.args(py)?;
        let annotations = self.annotations()?;
        Ok((class.into_any(), (op, args, annotations)))
    }
}

#[pyfunction(signature = (name, explicit_name = false))]
pub fn StringS<'py>(
    py: Python<'py>,
    name: &str,
    explicit_name: bool,
) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = STRINGS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("String_{name}_{counter}")
    };
    PyAstString::new_with_name(py, &GLOBAL_CONTEXT.strings(&name)?, Some(name))
}

#[pyfunction]
pub fn StringV<'py>(py: Python<'py>, value: &str) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    PyAstString::new(py, &GLOBAL_CONTEXT.stringv(value)?)
}

#[pyfunction]
pub fn StrLen<'py>(
    py: Python<'py>,
    s: Bound<'py, PyAstString>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.strlen(&s.get().inner)?)
}

#[pyfunction]
pub fn StrConcat<'py>(
    py: Python<'py>,
    s1: Bound<'py, PyAstString>,
    s2: Bound<'py, PyAstString>,
) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        &GLOBAL_CONTEXT.strconcat(&s1.get().inner, &s2.get().inner)?,
    )
}

#[pyfunction]
pub fn StrSubstr<'py>(
    py: Python<'py>,
    start: CoerceBV<'py>,
    size: CoerceBV<'py>,
    base: Bound<'py, PyAstString>,
) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        &GLOBAL_CONTEXT.strsubstr(
            &base.get().inner,
            &start.unpack(py, 64, false)?.get().inner,
            &size.unpack(py, 64, false)?.get().inner,
        )?,
    )
}

#[pyfunction]
pub fn StrContains<'py>(
    py: Python<'py>,
    haystack: Bound<'py, PyAstString>,
    needle: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.strcontains(&haystack.get().inner, &needle.get().inner)?,
    )
}

#[pyfunction]
pub fn StrIndexOf<'py>(
    py: Python<'py>,
    haystack: Bound<'py, PyAstString>,
    needle: Bound<'py, PyAstString>,
    start: CoerceBV<'py>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.strindexof(
            &haystack.get().inner,
            &needle.get().inner,
            &start.unpack(py, 64, false)?.get().inner,
        )?,
    )
}

#[pyfunction]
pub fn StrReplace<'py>(
    py: Python<'py>,
    haystack: Bound<'py, PyAstString>,
    needle: Bound<'py, PyAstString>,
    replacement: Bound<'py, PyAstString>,
) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        &GLOBAL_CONTEXT.strreplace(
            &haystack.get().inner,
            &needle.get().inner,
            &replacement.get().inner,
        )?,
    )
}

#[pyfunction]
pub fn StrPrefixOf<'py>(
    py: Python<'py>,
    needle: Bound<'py, PyAstString>,
    haystack: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.strprefixof(&needle.get().inner, &haystack.get().inner)?,
    )
}

#[pyfunction]
pub fn StrSuffixOf<'py>(
    py: Python<'py>,
    needle: Bound<'py, PyAstString>,
    haystack: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.strsuffixof(&needle.get().inner, &haystack.get().inner)?,
    )
}

#[pyfunction]
pub fn StrToInt<'py>(
    py: Python<'py>,
    s: Bound<'py, PyAstString>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.strtobv(&s.get().inner)?)
}

#[pyfunction]
pub fn IntToStr<'py>(
    py: Python<'py>,
    bv: Bound<'py, BV>,
) -> Result<Bound<'py, PyAstString>, ClaripyError> {
    PyAstString::new(py, &GLOBAL_CONTEXT.bvtostr(&bv.get().inner)?)
}

#[pyfunction]
pub fn StrIsDigit<'py>(
    py: Python<'py>,
    s: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.strisdigit(&s.get().inner)?)
}

#[pyfunction]
pub fn StrEq<'py>(
    py: Python<'py>,
    s1: Bound<'py, PyAstString>,
    s2: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.streq(&s1.get().inner, &s2.get().inner)?)
}

#[pyfunction]
pub fn StrNeq<'py>(
    py: Python<'py>,
    s1: Bound<'py, PyAstString>,
    s2: Bound<'py, PyAstString>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.strneq(&s1.get().inner, &s2.get().inner)?,
    )
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyAstString>()?;

    add_pyfunctions!(
        m,
        StringS,
        StringV,
        StrLen,
        StrConcat,
        StrSubstr,
        StrContains,
        StrIndexOf,
        StrReplace,
        StrPrefixOf,
        StrSuffixOf,
        StrToInt,
        IntToStr,
        StrIsDigit,
        StrEq,
        StrNeq,
    );

    Ok(())
}
