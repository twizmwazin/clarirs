#![allow(non_snake_case)]

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    LazyLock,
};

use dashmap::DashMap;
use pyo3::types::{PyBytes, PyFrozenSet, PyWeakrefReference};

use crate::prelude::*;

static STRINGS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_STRING_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> =
    LazyLock::new(DashMap::new);

#[pyclass(name="String", extends=Base, subclass, frozen, module="clarirs.ast.string")]
pub struct PyAstString {
    pub(crate) inner: StringAst<'static>,
}

impl PyAstString {
    pub fn new(py: Python, inner: &StringAst<'static>) -> Result<Py<PyAstString>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name(
        py: Python,
        inner: &StringAst<'static>,
        name: Option<String>,
    ) -> Result<Py<PyAstString>, ClaripyError> {
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
                PyClassInitializer::from(Base::new_with_name(py, name)).add_subclass(PyAstString {
                    inner: inner.clone(),
                }),
            )?;
            let weakref = PyWeakrefReference::new_bound(this.bind(py))?;
            PY_STRING_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl PyAstString {
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
    pub fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    #[getter]
    pub fn annotations(&self, py: Python) -> PyResult<Vec<PyObject>> {
        let pickle_loads = py.import_bound("pickle")?.getattr("loads")?;
        self.inner
            .get_annotations()
            .iter()
            .map(|a| pickle_loads.call1((PyBytes::new_bound(py, a.value()),)))
            .map(|a| a.map(|a| a.unbind()))
            .collect()
    }

    pub fn hash(&self) -> u64 {
        self.inner.hash()
    }

    #[getter]
    pub fn depth(&self) -> u32 {
        self.inner.depth()
    }

    pub fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    pub fn annotate(
        &self,
        py: Python,
        annotation: Bound<PyAny>,
    ) -> Result<Py<PyAstString>, ClaripyError> {
        let pickle_dumps = py.import_bound("pickle")?.getattr("dumps")?;
        let annotation_bytes = pickle_dumps
            .call1((&annotation,))?
            .downcast::<PyBytes>()?
            .extract::<Vec<u8>>()?;
        let eliminatable = annotation.getattr("eliminatable")?.extract::<bool>()?;
        let relocatable = annotation.getattr("relocatable")?.extract::<bool>()?;
        PyAstString::new(
            py,
            &GLOBAL_CONTEXT.annotated(
                &self.inner,
                Annotation::new("".to_string(), annotation_bytes, eliminatable, relocatable),
            )?,
        )
    }
}

#[pyfunction(signature = (name, explicit_name = false))]
pub fn StringS(
    py: Python,
    name: &str,
    explicit_name: bool,
) -> Result<Py<PyAstString>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = STRINGS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("String_{}_{}", name, counter)
    };
    PyAstString::new_with_name(py, &GLOBAL_CONTEXT.strings(&name)?, Some(name))
}

#[pyfunction]
pub fn StringV(py: Python, value: &str) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(py, &GLOBAL_CONTEXT.stringv(value)?)
}

#[pyfunction]
pub fn StrLen(py: Python, s: Bound<PyAstString>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.strlen(&s.get().inner)?)
}

#[pyfunction]
pub fn StrConcat(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        &GLOBAL_CONTEXT.strconcat(&s1.get().inner, &s2.get().inner)?,
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
        &GLOBAL_CONTEXT.strsubstr(&base.get().inner, &start.get().inner, &end.get().inner)?,
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
        &GLOBAL_CONTEXT.strcontains(&haystack.get().inner, &needle.get().inner)?,
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
        &GLOBAL_CONTEXT.strindexof(
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
        &GLOBAL_CONTEXT.strreplace(
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
        &GLOBAL_CONTEXT.strprefixof(&needle.get().inner, &haystack.get().inner)?,
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
        &GLOBAL_CONTEXT.strsuffixof(&needle.get().inner, &haystack.get().inner)?,
    )
}

#[pyfunction]
pub fn StrToInt(py: Python, s: Bound<PyAstString>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.strtobv(&s.get().inner)?)
}

#[pyfunction]
pub fn IntToStr(py: Python, bv: Bound<BV>) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(py, &GLOBAL_CONTEXT.bvtostr(&bv.get().inner)?)
}

#[pyfunction]
pub fn StrIsDigit(py: Python, s: Bound<PyAstString>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.strisdigit(&s.get().inner)?)
}
#[pyfunction]
pub fn StrEq(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.streq(&s1.get().inner, &s2.get().inner)?)
}
#[pyfunction]
pub fn StrNeq(
    py: Python,
    s1: Bound<PyAstString>,
    s2: Bound<PyAstString>,
) -> Result<Py<Bool>, ClaripyError> {
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
