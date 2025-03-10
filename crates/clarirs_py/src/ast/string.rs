#![allow(non_snake_case)]

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    LazyLock,
};

use dashmap::DashMap;
use pyo3::types::{PyAnyMethods, PyFrozenSet, PyWeakrefReference};

use crate::{annotation::{create_pyannotation, extract_annotation}, prelude::*};
use clarirs_core::smtlib::ToSmtLib;

static STRINGS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_STRING_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> =
    LazyLock::new(DashMap::new);

#[pyclass(name="String", extends=Base, subclass, frozen, module="clarirs.ast.string")]
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
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<PyObject>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        PyAstString::new(
            py,
            &match op {
                "StringS" => GLOBAL_CONTEXT.strings(&args[0].extract::<String>(py)?)?,
                "StringV" => GLOBAL_CONTEXT.stringv(&args[0].extract::<String>(py)?)?,
                "StrConcat" => GLOBAL_CONTEXT.strconcat(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                )?,
                "StrSubstr" => GLOBAL_CONTEXT.strsubstr(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                    &args[2].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "StrReplace" => GLOBAL_CONTEXT.strreplace(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[2].downcast_bound::<PyAstString>(py)?.get().inner,
                )?,
                "IntToStr" => {
                    GLOBAL_CONTEXT.bvtostr(&args[0].downcast_bound::<BV>(py)?.get().inner)?
                }
                "If" => GLOBAL_CONTEXT.if_(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[2].downcast_bound::<PyAstString>(py)?.get().inner,
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
        Ok(self
            .inner
            .get_annotations()
            .iter()
            .map(|a| create_pyannotation(py, a))
            .collect::<Result<Vec<Bound<'py, PyAny>>, ClaripyError>>()?)
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

    pub fn annotate<'py>(
        &self,
        py: Python<'py>,
        annotation: Bound<'py, PyAny>,
    ) -> Result<Bound<'py, PyAstString>, ClaripyError> {
        PyAstString::new(
            py,
            &GLOBAL_CONTEXT.annotated(&self.inner, extract_annotation(annotation)?)?,
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

    pub fn clear_annotations(
        self_: Bound<'_, PyAstString>,
    ) -> Result<Bound<'_, PyAstString>, ClaripyError> {
        let mut inner = self_.get().inner.clone();
        while let StringOp::Annotated(inner_, _) = inner.op() {
            inner = inner_.clone();
        }
        PyAstString::new(self_.py(), &inner)
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
        format!("String_{}_{}", name, counter)
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
            &start.extract(py, 64)?.get().inner,
            &size.extract(py, 64)?.get().inner,
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
            &start.extract(py, 64)?.get().inner,
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
