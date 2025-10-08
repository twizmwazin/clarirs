use pyo3::types::PySet;

use crate::prelude::*;

#[pyclass(subclass, frozen, weakref, module = "claripy.ast.base")]
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

    pub fn to_dynast(self_: Bound<'_, Base>) -> Result<DynAst<'static>, ClaripyError> {
        if let Ok(bool) = self_.clone().into_any().downcast::<Bool>() {
            Ok(DynAst::Boolean(bool.get().inner.clone()))
        } else if let Ok(bv) = self_.clone().into_any().downcast::<BV>() {
            Ok(DynAst::BitVec(bv.get().inner.clone()))
        } else if let Ok(fp) = self_.clone().into_any().downcast::<FP>() {
            Ok(DynAst::Float(fp.get().inner.clone()))
        } else if let Ok(string) = self_.clone().into_any().downcast::<PyAstString>() {
            Ok(DynAst::String(string.get().inner.clone()))
        } else {
            Err(ClaripyError::TypeError(
                "Cannot convert to DynAst: unsupported type".to_string(),
            ))
        }
    }

    pub fn from_dynast<'py>(
        py: Python<'py>,
        dynast: DynAst<'static>,
    ) -> Result<Bound<'py, Base>, ClaripyError> {
        match dynast {
            DynAst::Boolean(ast) => {
                Bool::new(py, &ast).map(|b| b.into_any().downcast_into::<Base>().unwrap())
            }
            DynAst::BitVec(ast) => {
                BV::new(py, &ast).map(|b| b.into_any().downcast_into::<Base>().unwrap())
            }
            DynAst::Float(ast) => {
                FP::new(py, &ast).map(|b| b.into_any().downcast_into::<Base>().unwrap())
            }
            DynAst::String(ast) => {
                PyAstString::new(py, &ast).map(|b| b.into_any().downcast_into::<Base>().unwrap())
            }
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
