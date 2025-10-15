use std::{cmp::max, str};

use num_bigint::BigInt;
use pyo3::types::PyInt;

use crate::prelude::*;

#[derive(Clone)]
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

pub enum CoerceBV<'py> {
    BV(Bound<'py, BV>),
    Int(BigInt),
}

impl<'py> CoerceBV<'py> {
    pub fn extract(
        &self,
        py: Python<'py>,
        size: u32,
        allow_mismatch: bool,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        match self {
            CoerceBV::BV(bv) => {
                if bv.get().size() as u32 == size || allow_mismatch {
                    Ok(bv.clone())
                } else {
                    Err(ClaripyError::CastingError("BV size mismatch".to_string()))
                }
            }
            CoerceBV::Int(int) => {
                let bv = BitVec::from_bigint_trunc(int, size);
                BV::new(py, &GLOBAL_CONTEXT.bvv(bv)?)
            }
        }
    }

    pub fn extract_like(&self, py: Python<'py>, like: &BV) -> Result<Bound<'py, BV>, ClaripyError> {
        self.extract(py, like.size() as u32, false)
    }

    pub fn extract_pair(
        py: Python<'py>,
        lhs: &CoerceBV<'py>,
        rhs: &CoerceBV<'py>,
    ) -> Result<(Bound<'py, BV>, Bound<'py, BV>), ClaripyError> {
        Ok(match (lhs, rhs) {
            (CoerceBV::BV(lhs), CoerceBV::BV(rhs)) => (lhs.clone(), rhs.clone()),
            (CoerceBV::Int(_), CoerceBV::BV(rhs)) => {
                let lhs = lhs.extract_like(py, rhs.get())?;
                (lhs, rhs.clone())
            }
            (CoerceBV::BV(lhs), CoerceBV::Int(_)) => {
                let rhs = rhs.extract_like(py, lhs.get())?;
                (lhs.clone(), rhs)
            }
            (CoerceBV::Int(lhs_int), CoerceBV::Int(rhs_int)) => {
                // Both args are ints, so we kinda have to guess the size
                // Take the max size of the two ints, then round up to the nearest power of 2

                let mut size = max(lhs_int.bits() as u32, rhs_int.bits() as u32);
                if *lhs_int < BigInt::ZERO || *rhs_int < BigInt::ZERO {
                    // If either int is negative, we need to add an extra bit for the sign
                    size += 1;
                }
                let size = size.next_power_of_two();

                let lhs = lhs.extract(py, size, false)?;
                let rhs = rhs.extract(py, size, false)?;
                (lhs, rhs)
            }
        })
    }
}

impl<'py> FromPyObject<'py> for CoerceBV<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(bv_val) = val.downcast::<BV>() {
            Ok(CoerceBV::from(bv_val.clone()))
        } else if let Ok(int_val) = val.downcast::<PyInt>() {
            Ok(CoerceBV::from(int_val.clone()))
        } else {
            Err(ClaripyError::InvalidArgumentType("Expected BV".to_string()).into())
        }
    }
}

impl<'py> From<Bound<'py, BV>> for CoerceBV<'py> {
    fn from(val: Bound<'py, BV>) -> Self {
        CoerceBV::BV(val)
    }
}

impl<'py> From<Bound<'py, PyInt>> for CoerceBV<'py> {
    fn from(val: Bound<'py, PyInt>) -> Self {
        CoerceBV::Int(val.extract::<BigInt>().unwrap())
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

pub struct CoerceBase<'py>(pub Bound<'py, Base>);

impl<'py> FromPyObject<'py> for CoerceBase<'py> {
    fn extract_bound(val: &Bound<'py, PyAny>) -> PyResult<Self> {
        if let Ok(bool) = CoerceBool::extract_bound(val) {
            Ok(CoerceBase(bool.0.downcast()?.clone()))
        } else if let Ok(bv) = CoerceBV::extract_bound(val) {
            match bv {
                CoerceBV::BV(bv) => Ok(CoerceBase(bv.downcast()?.clone())),
                CoerceBV::Int(int) => {
                    // Just default to 64 bits for now
                    let bv = BitVec::from_bigint_trunc(&int, 64);
                    let bv = BV::new(
                        val.py(),
                        &GLOBAL_CONTEXT.bvv(bv).map_err(ClaripyError::from)?,
                    )?;
                    Ok(CoerceBase(bv.downcast()?.clone()))
                }
            }
        } else if let Ok(fp) = CoerceFP::extract_bound(val) {
            Ok(CoerceBase(fp.0.downcast()?.clone()))
        } else if let Ok(string) = CoerceString::extract_bound(val) {
            Ok(CoerceBase(string.0.downcast()?.clone()))
        } else {
            Err(
                ClaripyError::InvalidArgumentType("Expected Bool, BV, FP, or String".to_string())
                    .into(),
            )
        }
    }
}

impl<'py> From<CoerceBase<'py>> for Bound<'py, Base> {
    fn from(val: CoerceBase<'py>) -> Self {
        val.0
    }
}
