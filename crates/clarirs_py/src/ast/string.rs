#![allow(non_snake_case)]

use std::sync::LazyLock;

use dashmap::DashMap;
use pyo3::types::PyWeakrefReference;

use crate::prelude::*;

static PY_STRING_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> =
    LazyLock::new(DashMap::new);

#[pyclass(name="String", extends=Base, subclass, frozen, module="clarirs.ast.string")]
pub struct PyAstString {
    pub(crate) inner: StringAst<'static>,
}

impl PyAstString {
    pub fn new(py: Python, inner: StringAst<'static>) -> Result<Py<PyAstString>, ClaripyError> {
        if let Some(cache_hit) = PY_STRING_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<PyAstString>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit.unbind())
        } else {
            let this = Py::new(
                py,
                PyClassInitializer::from(Base::new()).add_subclass(PyAstString {
                    inner: inner.clone(),
                }),
            )?;
            let weakref = PyWeakrefReference::new_bound(this.bind(py))?;
            PY_STRING_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pyfunction]
pub fn StringS(py: Python, name: &str, size: u32) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(py, GLOBAL_CONTEXT.strings(name, size)?)
}

#[pyfunction]
pub fn StringV(py: Python, value: &str) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(py, GLOBAL_CONTEXT.stringv(value)?)
}

#[pyfunction]
pub fn StrLen(py: Python, s: Bound<PyAstString>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, GLOBAL_CONTEXT.strlen(&s.get().inner)?)
}

#[pyfunction]
pub fn StrConcat(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        GLOBAL_CONTEXT.strconcat(&s1.get().inner, &s2.get().inner)?,
    )
}

#[pyfunction]
pub fn StrSubstr(
    py: Python,
    base: Bound<PyAstString>,
    start: Bound<BV>,
    end: Bound<BV>,
) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        GLOBAL_CONTEXT.strsubstr(&base.get().inner, &start.get().inner, &end.get().inner)?,
    )
}

#[pyfunction]
pub fn StrContains(
    py: Python,
    haystack: Bound<PyAstString>,
    needle: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.strcontains(&haystack.get().inner, &needle.get().inner)?,
    )
}

#[pyfunction]
pub fn StrIndexOf(
    py: Python,
    haystack: Bound<PyAstString>,
    needle: Bound<PyAstString>,
    start: Bound<BV>,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        GLOBAL_CONTEXT.strindexof(
            &haystack.get().inner,
            &needle.get().inner,
            &start.get().inner,
        )?,
    )
}

#[pyfunction]
pub fn StrReplace(
    py: Python,
    haystack: Bound<PyAstString>,
    needle: Bound<PyAstString>,
    replacement: Bound<PyAstString>,
) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        GLOBAL_CONTEXT.strreplace(
            &haystack.get().inner,
            &needle.get().inner,
            &replacement.get().inner,
        )?,
    )
}

#[pyfunction]
pub fn StrPrefixOf(
    py: Python,
    needle: Bound<PyAstString>,
    haystack: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.strprefixof(&needle.get().inner, &haystack.get().inner)?,
    )
}
#[pyfunction]
pub fn StrSuffixOf(
    py: Python,
    needle: Bound<PyAstString>,
    haystack: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.strsuffixof(&needle.get().inner, &haystack.get().inner)?,
    )
}

#[pyfunction]
pub fn StrToBV(py: Python, s: Bound<PyAstString>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, GLOBAL_CONTEXT.strtobv(&s.get().inner)?)
}

#[pyfunction]
pub fn BVToStr(py: Python, bv: Bound<BV>) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(py, GLOBAL_CONTEXT.bvtostr(&bv.get().inner)?)
}

#[pyfunction]
pub fn StrIsDigit(py: Python, s: Bound<PyAstString>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, GLOBAL_CONTEXT.strisdigit(&s.get().inner)?)
}
#[pyfunction]
pub fn StrEq(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, GLOBAL_CONTEXT.streq(&s1.get().inner, &s2.get().inner)?)
}
#[pyfunction]
pub fn StrNeq(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, GLOBAL_CONTEXT.strneq(&s1.get().inner, &s2.get().inner)?)
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
        StrToBV,
        BVToStr,
        StrIsDigit,
        StrEq,
        StrNeq,
    );

    Ok(())
}
