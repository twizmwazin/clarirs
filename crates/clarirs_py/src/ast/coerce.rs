use std::str;

use clarirs_core::ast::bitvec::BitVecExt;

use crate::prelude::*;

pub struct CoerceBool<'py>(pub Bound<'py, Bool>);

impl<'py> FromPyObject<'py> for CoerceBool<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(bool_val) = val.downcast::<Bool>() {
            Ok(CoerceBool(bool_val.clone()))
        } else if let Ok(bool_val) = val.extract::<bool>() {
            Ok(CoerceBool(
                Bool::new(val.py(), &GLOBAL_CONTEXT.boolv(bool_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected Bool".to_string()).into())
        }
    }
}

impl<'py> From<CoerceBool<'py>> for Bound<'py, Bool> {
    fn from(val: CoerceBool<'py>) -> Self {
        val.0
    }
}

impl<'py> From<CoerceBool<'py>> for BoolAst<'static> {
    fn from(val: CoerceBool<'py>) -> Self {
        val.0.get().inner.clone()
    }
}

pub struct CoerceBV<'py> {
    inner: Bound<'py, BV>,
    coerced: bool,
}

impl<'py> CoerceBV<'py> {
    pub fn new(bv: Bound<'py, BV>) -> Self {
        CoerceBV {
            inner: bv,
            coerced: false,
        }
    }

    pub fn new_coerced(bv: Bound<'py, BV>) -> Self {
        CoerceBV {
            inner: bv,
            coerced: true,
        }
    }

    pub fn extract_like(&self, py: Python<'py>, like: &BV) -> Result<Bound<'py, BV>, ClaripyError> {
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
        py: Python<'py>,
        lhs: &CoerceBV<'py>,
        rhs: &CoerceBV<'py>,
    ) -> Result<(Bound<'py, BV>, Bound<'py, BV>), ClaripyError> {
        Ok(match (lhs.coerced, rhs.coerced) {
            (true, true) | (false, false) => (lhs.inner.clone(), rhs.inner.clone()),
            (true, false) => (lhs.extract_like(py, rhs.inner.get())?, rhs.inner.clone()),
            (false, true) => (lhs.inner.clone(), rhs.extract_like(py, lhs.inner.get())?),
        })
    }
}

impl<'py> FromPyObject<'py> for CoerceBV<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(bv_val) = val.downcast::<BV>() {
            Ok(CoerceBV::new(bv_val.clone()))
        } else if let Ok(bv_val) = val.extract::<u64>() {
            Ok(CoerceBV::new_coerced(
                BV::new(val.py(), &GLOBAL_CONTEXT.bvv_prim(bv_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected BV".to_string()).into())
        }
    }
}

impl<'py> From<CoerceBV<'py>> for Bound<'py, BV> {
    fn from(val: CoerceBV<'py>) -> Self {
        val.inner
    }
}

impl<'py> From<Bound<'py, BV>> for CoerceBV<'py> {
    fn from(val: Bound<'py, BV>) -> Self {
        CoerceBV::new(val)
    }
}

impl<'py> From<CoerceBV<'py>> for BitVecAst<'static> {
    fn from(val: CoerceBV<'py>) -> Self {
        val.inner.get().inner.clone()
    }
}

pub struct CoerceFP<'py>(pub Bound<'py, FP>);

impl<'py> FromPyObject<'py> for CoerceFP<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(fp_val) = val.downcast::<FP>() {
            Ok(CoerceFP(fp_val.clone()))
        } else if let Ok(fp_val) = val.extract::<f64>() {
            Ok(CoerceFP(
                FP::new(val.py(), &GLOBAL_CONTEXT.fpv(Float::from(fp_val)).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected FP".to_string()).into())
        }
    }
}

impl<'py> From<CoerceFP<'py>> for Bound<'py, FP> {
    fn from(val: CoerceFP<'py>) -> Self {
        val.0
    }
}

impl<'py> From<CoerceFP<'py>> for FloatAst<'static> {
    fn from(val: CoerceFP<'py>) -> Self {
        val.0.get().inner.clone()
    }
}

pub struct CoerceString<'py>(pub Bound<'py, PyAstString>);

impl<'py> FromPyObject<'py> for CoerceString<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(string_val) = val.downcast::<PyAstString>() {
            Ok(CoerceString(string_val.clone()))
        } else if let Ok(string_val) = val.extract::<&str>() {
            Ok(CoerceString(
                PyAstString::new(val.py(), &GLOBAL_CONTEXT.stringv(string_val).unwrap()).unwrap(),
            ))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected String".to_string()).into())
        }
    }
}

impl<'py> From<CoerceString<'py>> for Bound<'py, PyAstString> {
    fn from(val: CoerceString<'py>) -> Self {
        val.0
    }
}

impl<'py> From<CoerceString<'py>> for StringAst<'static> {
    fn from(val: CoerceString<'py>) -> Self {
        val.0.get().inner.clone()
    }
}
