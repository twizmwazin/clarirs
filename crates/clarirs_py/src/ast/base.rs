use pyo3::types::PySet;

use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "claripy.ast.base", from_py_object)]
#[derive(Clone)]
pub struct Base {
    errored: Py<PySet>,
    name: Option<String>,
    encoded_name: Option<Vec<u8>>,
}

impl Base {
    pub fn new(py: Python) -> Self {
        Self::new_with_name(py, None)
    }

    pub fn new_with_name(py: Python, name: Option<String>) -> Self {
        let encoded_name = name.as_ref().map(|name| name.as_bytes().to_vec());
        Self {
            errored: PySet::empty(py).expect("Failed to create PySet").unbind(),
            name,
            encoded_name,
        }
    }

    pub fn to_astref(self_: Bound<'_, Base>) -> Result<AstRef<'static>, ClaripyError> {
        if let Ok(bool) = self_.clone().into_any().cast::<Bool>() {
            Ok(bool.get().inner.clone())
        } else if let Ok(bv) = self_.clone().into_any().cast::<BV>() {
            Ok(bv.get().inner.clone())
        } else if let Ok(fp) = self_.clone().into_any().cast::<FP>() {
            Ok(fp.get().inner.clone())
        } else if let Ok(string) = self_.clone().into_any().cast::<PyAstString>() {
            Ok(string.get().inner.clone())
        } else {
            Err(ClaripyError::TypeError(
                "Cannot convert to AstRef: unsupported type".to_string(),
            ))
        }
    }

    pub fn from_astref<'py>(
        py: Python<'py>,
        ast: &AstRef<'static>,
    ) -> Result<Bound<'py, Base>, ClaripyError> {
        match ast.op().base_theories() {
            Theories::BOOLEAN => {
                Bool::new(py, ast).map(|b| b.into_any().cast_into::<Base>().unwrap())
            }
            Theories::BITVEC => {
                BV::new(py, ast).map(|b| b.into_any().cast_into::<Base>().unwrap())
            }
            Theories::FLOAT => {
                FP::new(py, ast).map(|b| b.into_any().cast_into::<Base>().unwrap())
            }
            Theories::STRING => {
                PyAstString::new(py, ast).map(|b| b.into_any().cast_into::<Base>().unwrap())
            }
            _ => Err(ClaripyError::TypeError(
                "Cannot convert AstRef to Python type: unknown theory".to_string(),
            )),
        }
    }
}

#[pymethods]
impl Base {
    #[getter]
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    #[getter]
    pub fn _encoded_name(&self) -> Option<&[u8]> {
        self.encoded_name.as_deref()
    }

    #[getter]
    pub fn _errored(&self) -> Py<PySet> {
        self.errored.clone()
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<Base>()?;
    Ok(())
}
