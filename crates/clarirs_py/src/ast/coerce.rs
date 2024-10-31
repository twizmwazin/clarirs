use std::str;

use crate::prelude::*;

pub struct CoerceBool(pub Py<Bool>);

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

pub struct CoerceBV(pub Py<BV>);

impl FromPyObject<'_> for CoerceBV {
    fn extract_bound(val: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(bv_val) = val.downcast::<BV>() {
            Ok(CoerceBV(bv_val.clone().unbind()))
        } else if let Ok(bv_val) = val.extract::<u64>() {
            Ok(CoerceBV(
                BV::new(val.py(), &GLOBAL_CONTEXT.bvv_prim(bv_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected BV".to_string()).into())
        }
    }
}

impl From<CoerceBV> for Py<BV> {
    fn from(val: CoerceBV) -> Self {
        val.0
    }
}

impl From<CoerceBV> for BitVecAst<'static> {
    fn from(val: CoerceBV) -> Self {
        val.0.get().inner.clone()
    }
}

pub struct CoerceFP(pub Py<FP>);

impl FromPyObject<'_> for CoerceFP {
    fn extract_bound(val: &Bound<'_, PyAny>) -> PyResult<Self> {
        if let Ok(fp_val) = val.downcast::<FP>() {
            Ok(CoerceFP(fp_val.clone().unbind()))
        } else if let Ok(fp_val) = val.extract::<f64>() {
            Ok(CoerceFP(
                FP::new(val.py(), &GLOBAL_CONTEXT.fpv(fp_val).unwrap()).unwrap(),
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
