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
            let weakref = PyWeakrefReference::new(this.bind(py))?;
            PY_STRING_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl PyAstString {
    #[new]
    pub fn py_new(
        py: Python,
        op: &str,
        args: Vec<PyObject>,
    ) -> Result<Py<PyAstString>, ClaripyError> {
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

    pub fn simplify(&self, py: Python) -> Result<Py<PyAstString>, ClaripyError> {
        PyAstString::new(py, &self.inner.simplify()?)
    }

    #[getter]
    pub fn concrete_value(&self) -> Result<Option<String>, ClaripyError> {
        Ok(match self.inner.simplify()?.op() {
            StringOp::StringV(value) => Some(value.clone()),
            _ => None,
        })
    }

    pub fn annotate(
        &self,
        py: Python,
        annotation: Bound<PyAny>,
    ) -> Result<Py<PyAstString>, ClaripyError> {
        let pickle_dumps = py.import("pickle")?.getattr("dumps")?;
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

    pub fn __add__(
        &self,
        py: Python,
        other: Bound<PyAstString>,
    ) -> Result<Py<PyAstString>, ClaripyError> {
        PyAstString::new(
            py,
            &GLOBAL_CONTEXT.strconcat(&self.inner, &other.get().inner)?,
        )
    }

    pub fn __eq__(&self, py: Python, other: Bound<PyAstString>) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.streq(&self.inner, &other.get().inner)?)
    }

    pub fn __ne__(&self, py: Python, other: Bound<PyAstString>) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.strneq(&self.inner, &other.get().inner)?)
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
    start: CoerceBV,
    size: CoerceBV,
    base: Bound<PyAstString>,
) -> Result<Py<PyAstString>, ClaripyError> {
    PyAstString::new(
        py,
        &GLOBAL_CONTEXT.strsubstr(&base.get().inner, &start.into(), &size.into())?,
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
    start: CoerceBV,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.strindexof(&haystack.get().inner, &needle.get().inner, &start.into())?,
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
