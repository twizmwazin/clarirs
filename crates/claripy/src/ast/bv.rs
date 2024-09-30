#![allow(non_snake_case)]

use num_bigint::BigUint;
use pyo3::exceptions::{PyTypeError, PyValueError};

use super::shared_ops;
use super::{bits::Bits, bool::Bool};
use crate::prelude::*;

#[pyclass(extends=Bits, subclass, frozen, weakref, module="claripy.ast.bv")]
pub struct BV;

impl PyAst for BV {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Bits::new_from_astref(ast_ref).add_subclass(BV {})
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super().into_super()
    }
}

#[pymethods]
impl BV {}

pyop!(BVS, bvs, BV, name: String, size: u32);

#[allow(non_snake_case)]
#[pyfunction(signature = (value, size = None))]
pub fn BVV(py: Python, value: Bound<PyAny>, size: Option<u32>) -> Result<Py<BV>, PyErr> {
    if let Ok(int_val) = value.extract::<BigUint>() {
        if let Some(size) = size {
            return Ok(py_ast_from_astref(
                py,
                GLOBAL_CONTEXT
                    .bvv_from_biguint_with_size(&int_val, size)
                    .map_err(ClaripyError::from)?,
            )?);
        } else {
            return Err(PyErr::new::<PyValueError, _>("size must be specified"));
        }
    }
    // TODO: deduplicate bytes/str
    if let Ok(bytes_val) = value.extract::<Vec<u8>>() {
        let int_val = BigUint::from_bytes_le(&bytes_val);
        log::warn!("bytes value passed to BVV, assuming little-endian");
        if size.is_some() {
            log::warn!("BVV size specified with bytes, value will be ignored");
        }
        return Ok(py_ast_from_astref(
            py,
            GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, bytes_val.len() as u32 * 8)
                .map_err(ClaripyError::from)?,
        )?);
    }
    if let Ok(str_val) = value.extract::<String>() {
        log::warn!("string value passed to BVV, assuming utf-8");
        let bytes_val = str_val.as_bytes();
        let int_val = BigUint::from_bytes_le(bytes_val);
        log::warn!("bytes value passed to BVV, assuming little-endian");
        if size.is_some() {
            log::warn!("BVV size specified with bytes, value will be ignored");
        }
        return Ok(py_ast_from_astref(
            py,
            GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, bytes_val.len() as u32 * 8)
                .map_err(ClaripyError::from)?,
        )?);
    }
    Err(PyErr::new::<PyTypeError, _>(
        "BVV value must be a int, bytes, or str",
    ))
}

pyop!(Add, add, BV, BV, BV);
pyop!(Sub, sub, BV, BV, BV);
pyop!(Mul, mul, BV, BV, BV);
pyop!(UDiv, udiv, BV, BV, BV);
pyop!(SDiv, sdiv, BV, BV, BV);
pyop!(UMod, urem, BV, BV, BV);
pyop!(SMod, srem, BV, BV, BV);
pyop!(Pow, pow, BV, BV, BV);
pyop!(LShL, lshl, BV, BV, BV);
pyop!(LShR, lshr, BV, BV, BV);
pyop!(AShR, ashr, BV, BV, BV);
pyop!(AShL, ashl, BV, BV, BV);
pyop!(Concat, concat, BV, BV, BV);
pyop!(Extract, extract, BV, BV, start: u32, end: u32);

pyop!(ULT, ult, Bool, BV, BV);
pyop!(ULE, ule, Bool, BV, BV);
pyop!(UGT, ugt, Bool, BV, BV);
pyop!(UGE, uge, Bool, BV, BV);
pyop!(SLT, slt, Bool, BV, BV);
pyop!(SLE, sle, Bool, BV, BV);
pyop!(SGT, sgt, Bool, BV, BV);
pyop!(SGE, sge, Bool, BV, BV);

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<BV>()?;

    add_pyfunctions!(
        m,
        BVS,
        BVV,
        shared_ops::Not,
        shared_ops::And,
        Add,
        Sub,
        Mul,
        UDiv,
        SDiv,
        UMod,
        SMod,
        Pow,
        LShL,
        LShR,
        AShR,
        AShL,
        Concat,
        Extract,
        ULT,
        ULE,
        UGT,
        UGE,
        SLT,
        SLE,
        SGT,
        SGE,
        shared_ops::Eq_,
        shared_ops::If,
    );

    Ok(())
}
