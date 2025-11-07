use std::{cmp::max, str};

use num_bigint::BigInt;
use pyo3::types::PyInt;

use crate::prelude::*;

#[derive(Clone)]
pub struct CoerceBool<'py>(pub Bound<'py, Bool>);

impl<'py> FromPyObject<'_, 'py> for CoerceBool<'py> {
    type Error = PyErr;

    fn extract(val: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bool_val) = val.cast::<Bool>() {
            Ok(CoerceBool(bool_val.to_owned()))
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
    pub fn unpack(
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

    pub fn unpack_like(&self, py: Python<'py>, like: &BV) -> Result<Bound<'py, BV>, ClaripyError> {
        self.unpack(py, like.size() as u32, false)
    }

    pub fn unpack_pair(
        py: Python<'py>,
        lhs: &CoerceBV<'py>,
        rhs: &CoerceBV<'py>,
    ) -> Result<(Bound<'py, BV>, Bound<'py, BV>), ClaripyError> {
        Ok(match (lhs, rhs) {
            (CoerceBV::BV(lhs), CoerceBV::BV(rhs)) => {
                // Check for size mismatch when both are BVs
                let lhs_size = lhs.get().size() as u32;
                let rhs_size = rhs.get().size() as u32;
                if lhs_size != rhs_size {
                    return Err(ClaripyError::CastingError(format!(
                        "BV size mismatch: left operand has {lhs_size} bits, right operand has {rhs_size} bits"
                    )));
                }
                (lhs.clone(), rhs.clone())
            }
            (CoerceBV::Int(_), CoerceBV::BV(rhs)) => {
                let lhs = lhs.unpack_like(py, rhs.get())?;
                (lhs, rhs.clone())
            }
            (CoerceBV::BV(lhs), CoerceBV::Int(_)) => {
                let rhs = rhs.unpack_like(py, lhs.get())?;
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

                let lhs = lhs.unpack(py, size, false)?;
                let rhs = rhs.unpack(py, size, false)?;
                (lhs, rhs)
            }
        })
    }

    pub fn unpack_vec(
        py: Python<'py>,
        vals: &[CoerceBV<'py>],
    ) -> Result<Vec<Bound<'py, BV>>, ClaripyError> {
        if vals.is_empty() {
            return Ok(vec![]);
        }

        // First, determine the size to use
        let size = vals
            .iter()
            .find(|val| matches!(val, CoerceBV::BV(_)))
            .map(|val| match val {
                CoerceBV::BV(bv) => bv.get().size() as u32,
                CoerceBV::Int(_) => 0,
            })
            .ok_or(ClaripyError::InvalidArgumentType(
                "Failed to extract size of BVs in list".to_string(),
            ))?;

        // Round up to the nearest power of 2
        let size = size.next_power_of_two();

        // Now unpack all values
        vals.iter().map(|val| val.unpack(py, size, true)).collect()
    }

    pub fn unpack_vec_mismatch(
        py: Python<'py>,
        vals: &[CoerceBV<'py>],
    ) -> Result<Vec<Bound<'py, BV>>, ClaripyError> {
        // If len is 1 and it is an Int, then we can't determine size, so just return error
        if vals.len() == 1 && matches!(vals[0], CoerceBV::Int(_)) {
            return Err(ClaripyError::InvalidArgumentType(
                "Cannot determine size from single Int".to_string(),
            ));
        }

        let default_size = vals
            .iter()
            .find(|val| matches!(val, CoerceBV::BV(_)))
            .map(|val| match val {
                CoerceBV::BV(bv) => bv.get().size() as u32,
                CoerceBV::Int(_) => 0,
            })
            .ok_or(ClaripyError::InvalidArgumentType(
                "Failed to extract size of BVs in list".to_string(),
            ))?;

        let mut results = Vec::with_capacity(vals.len());

        for val in vals {
            let unpacked = match val {
                CoerceBV::BV(bv) => Ok(bv.clone()),
                CoerceBV::Int(int) => {
                    // Match the size of the first BV in the list, otherwise default to 64 bits
                    let bv = BitVec::from_bigint_trunc(int, default_size);
                    BV::new(py, &GLOBAL_CONTEXT.bvv(bv).map_err(ClaripyError::from)?)
                }
            };
            results.push(unpacked?);
        }

        Ok(results)
    }
}

impl<'py> FromPyObject<'_, 'py> for CoerceBV<'py> {
    type Error = PyErr;

    fn extract(val: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bv_val) = val.cast::<BV>() {
            Ok(CoerceBV::from(bv_val.to_owned()))
        } else if let Ok(int_val) = val.cast::<PyInt>() {
            Ok(CoerceBV::from(int_val.to_owned()))
        } else if let Ok(bytes_val) = val.extract::<Vec<u8>>() {
            Ok(CoerceBV::BV(BV::new(
                val.py(),
                &GLOBAL_CONTEXT
                    .bvv(BitVec::from_bytes_be(&bytes_val))
                    .map_err(ClaripyError::from)?,
            )?))
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

impl<'py> FromPyObject<'_, 'py> for CoerceFP<'py> {
    type Error = PyErr;

    fn extract(val: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(fp_val) = val.cast::<FP>() {
            Ok(CoerceFP(fp_val.to_owned()))
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

impl<'py> FromPyObject<'_, 'py> for CoerceString<'py> {
    type Error = PyErr;
    fn extract(val: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(string_val) = val.cast::<PyAstString>() {
            Ok(CoerceString(string_val.to_owned()))
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

impl<'a, 'py> FromPyObject<'a, 'py> for CoerceBase<'py> {
    type Error = PyErr;

    fn extract(val: Borrowed<'a, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bool) = CoerceBool::extract(val) {
            Ok(CoerceBase(bool.0.cast()?.clone()))
        } else if let Ok(bv) = CoerceBV::extract(val) {
            match bv {
                CoerceBV::BV(bv) => Ok(CoerceBase(bv.cast()?.clone())),
                CoerceBV::Int(int) => {
                    // Just default to 64 bits for now
                    let bv = BitVec::from_bigint_trunc(&int, 64);
                    let bv = BV::new(
                        val.py(),
                        &GLOBAL_CONTEXT.bvv(bv).map_err(ClaripyError::from)?,
                    )?;
                    Ok(CoerceBase(bv.cast()?.clone()))
                }
            }
        } else if let Ok(fp) = CoerceFP::extract(val) {
            Ok(CoerceBase(fp.0.cast()?.clone()))
        } else if let Ok(string) = CoerceString::extract(val) {
            Ok(CoerceBase(string.0.cast()?.clone()))
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
