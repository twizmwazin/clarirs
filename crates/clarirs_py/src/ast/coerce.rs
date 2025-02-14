use std::str;

use clarirs_core::ast::bitvec::BitVecExt;

use crate::prelude::*;

pub struct CoerceBool(pub Py<Bool>);

use clarirs_num::bitvec::BitVecError;
use pyo3::exceptions::PyValueError;
use pyo3::PyErr;

pub struct PyBitVecError(pub BitVecError);

impl From<BitVecError> for PyBitVecError {
    fn from(err: BitVecError) -> Self {
        PyBitVecError(err)
    }
}

impl From<PyBitVecError> for PyErr {
    fn from(err: PyBitVecError) -> Self {
        PyValueError::new_err(format!("{}", err.0))
    }
}

impl FromPyObject<'_> for CoerceBool {
    fn extract_bound(val: &Bound<PyAny>) -> PyResult<Self> {
        if let Ok(bool_val) = val.downcast::<Bool>() {
            Ok(CoerceBool(bool_val.clone().unbind()))
        } else if let Ok(bool_val) = val.extract::<bool>() {
            Ok(CoerceBool(
                Bool::new(val.py(), &GLOBAL_CONTEXT.boolv(bool_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected Bool".to_string()).into())
        }
    }
}

impl From<CoerceBool> for Py<Bool> {
    fn from(val: CoerceBool) -> Self {
        val.0
    }
}

impl From<CoerceBool> for BoolAst<'static> {
    fn from(val: CoerceBool) -> Self {
        val.0.get().inner.clone()
    }
}

pub struct CoerceBV {
    inner: Py<BV>,
    coerced: bool,
}

impl CoerceBV {
    pub fn new(bv: Py<BV>) -> Self {
        CoerceBV {
            inner: bv,
            coerced: false,
        }
    }

    pub fn new_coerced(bv: Py<BV>) -> Self {
        CoerceBV {
            inner: bv,
            coerced: true,
        }
    }

    pub fn extract_like(&self, py: Python, like: &BV) -> Result<Py<BV>, ClaripyError> {
        let our_size = self.inner.get().inner.size();
        let like_size = like.inner.size();

        if self.coerced && like_size != our_size {
            match self.inner.get().inner.op() {
                BitVecOp::BVV(val) => BV::new(
                    py,
                    &GLOBAL_CONTEXT.bvv_from_biguint_with_size(&val.as_biguint(), like_size)?,
                ),
                _ => {
                    if like_size > our_size {
                        self.inner.get().zero_extend(py, like_size)
                    } else {
                        self.inner.get().Extract(py, like_size - 1, 0)
                    }
                }
            }
        } else {
            Ok(self.inner.clone())
        }
    }

    pub fn extract_pair(
        py: Python,
        lhs: &CoerceBV,
        rhs: &CoerceBV,
    ) -> Result<(Py<BV>, Py<BV>), ClaripyError> {
        Ok(match (lhs.coerced, rhs.coerced) {
            (true, true) | (false, false) => (lhs.inner.clone(), rhs.inner.clone()),
            (true, false) => (lhs.extract_like(py, rhs.inner.get())?, rhs.inner.clone()),
            (false, true) => (lhs.inner.clone(), rhs.extract_like(py, lhs.inner.get())?),
        })
    }
}

impl FromPyObject<'_> for CoerceBV {
    fn extract_bound(val: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(bv_val) = val.downcast::<BV>() {
            Ok(CoerceBV::new(bv_val.clone().unbind()))
        } else if let Ok(bv_val) = val.extract::<u64>() {
            Ok(CoerceBV::new_coerced(
                BV::new(val.py(), &GLOBAL_CONTEXT.bvv_prim(bv_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected BV".to_string()).into())
        }
    }
}

impl From<CoerceBV> for Py<BV> {
    fn from(val: CoerceBV) -> Self {
        val.inner
    }
}

impl From<Py<BV>> for CoerceBV {
    fn from(val: Py<BV>) -> Self {
        CoerceBV::new(val)
    }
}

impl From<Bound<'_, BV>> for CoerceBV {
    fn from(val: Bound<BV>) -> Self {
        CoerceBV::new(val.unbind())
    }
}

impl From<CoerceBV> for BitVecAst<'static> {
    fn from(val: CoerceBV) -> Self {
        val.inner.get().inner.clone()
    }
}

pub struct CoerceFP(pub Py<FP>);

impl FromPyObject<'_> for CoerceFP {
    fn extract_bound(val: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(fp_val) = val.downcast::<FP>() {
            Ok(CoerceFP(fp_val.clone().unbind()))
        } else if let Ok(fp_val) = val.extract::<f64>() {
            Ok(CoerceFP(
                FP::new(
                    val.py(),
                    &GLOBAL_CONTEXT
                        .fpv(Float::try_from(fp_val).map_err(PyBitVecError::from)?)
                        .unwrap(),
                )
                .unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected FP".to_string()).into())
        }
    }
}

impl From<CoerceFP> for Py<FP> {
    fn from(val: CoerceFP) -> Self {
        val.0
    }
}

impl From<CoerceFP> for FloatAst<'static> {
    fn from(val: CoerceFP) -> Self {
        val.0.get().inner.clone()
    }
}

pub struct CoerceString(pub Py<PyAstString>);

impl FromPyObject<'_> for CoerceString {
    fn extract_bound(val: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(string_val) = val.downcast::<PyAstString>() {
            Ok(CoerceString(string_val.clone().unbind()))
        } else if let Ok(string_val) = val.extract::<&str>() {
            Ok(CoerceString(
                PyAstString::new(val.py(), &GLOBAL_CONTEXT.stringv(string_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected String".to_string()).into())
        }
    }
}

impl From<CoerceString> for Py<PyAstString> {
    fn from(val: CoerceString) -> Self {
        val.0
    }
}

impl From<CoerceString> for StringAst<'static> {
    fn from(val: CoerceString) -> Self {
        val.0.get().inner.clone()
    }
}
