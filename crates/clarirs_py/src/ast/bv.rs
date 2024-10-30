#![allow(non_snake_case)]

use std::sync::LazyLock;

use dashmap::DashMap;
use num_bigint::BigUint;
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::types::PyWeakrefReference;

use crate::ast::{And, Not, Or, Xor};
use crate::prelude::*;

static PY_BV_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Bits, subclass, frozen, weakref, module="clarirs.ast.bv")]
pub struct BV {
    pub(crate) inner: BitVecAst<'static>,
}

impl BV {
    pub fn new(py: Python, inner: BitVecAst<'static>) -> Result<Py<BV>, ClaripyError> {
        if let Some(cache_hit) = PY_BV_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<BV>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit.unbind())
        } else {
            let this = Py::new(
                py,
                PyClassInitializer::from(Base::new())
                    .add_subclass(Bits::new())
                    .add_subclass(BV {
                        inner: inner.clone(),
                    }),
            )?;
            let weakref = PyWeakrefReference::new_bound(this.bind(py))?;
            PY_BV_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl BV {}

#[pyfunction]
pub fn BVS(py: Python, name: String, size: u32) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, GLOBAL_CONTEXT.bvs(&name, size)?)
}

#[allow(non_snake_case)]
#[pyfunction(signature = (value, size = None))]
pub fn BVV(py: Python, value: Bound<PyAny>, size: Option<u32>) -> Result<Py<BV>, PyErr> {
    if let Ok(int_val) = value.extract::<BigUint>() {
        if let Some(size) = size {
            let a = GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, size)
                .map_err(ClaripyError::from)?;
            return Ok(BV::new(py, a)?);
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
        return Ok(BV::new(
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
        return Ok(BV::new(
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

macro_rules! binop {
    ($name:ident, $context_method:ident, $return_type:ty, $lhs:ty, $rhs:ty) => {
        #[pyfunction]
        pub fn $name(
            py: Python,
            lhs: Bound<$lhs>,
            rhs: Bound<$rhs>,
        ) -> Result<Py<$return_type>, ClaripyError> {
            <$return_type>::new(
                py,
                GLOBAL_CONTEXT.$context_method(&lhs.get().inner, &rhs.get().inner)?,
            )
        }
    };
}

binop!(Add, add, BV, BV, BV);
binop!(Sub, sub, BV, BV, BV);
binop!(Mul, mul, BV, BV, BV);
binop!(UDiv, udiv, BV, BV, BV);
binop!(SDiv, sdiv, BV, BV, BV);
binop!(UMod, urem, BV, BV, BV);
binop!(SMod, srem, BV, BV, BV);
binop!(Pow, pow, BV, BV, BV);
binop!(ShL, ashl, BV, BV, BV);
binop!(LShR, lshr, BV, BV, BV);
binop!(AShR, ashr, BV, BV, BV);
binop!(Concat, concat, BV, BV, BV);

binop!(ULT, ult, Bool, BV, BV);
binop!(ULE, ule, Bool, BV, BV);
binop!(UGT, ugt, Bool, BV, BV);
binop!(UGE, uge, Bool, BV, BV);
binop!(SLT, slt, Bool, BV, BV);
binop!(SLE, sle, Bool, BV, BV);
binop!(SGT, sgt, Bool, BV, BV);
binop!(SGE, sge, Bool, BV, BV);
binop!(Eq_, eq_, Bool, BV, BV);
binop!(Neq, neq, Bool, BV, BV);

#[pyfunction]
pub fn Extract(py: Python, base: Bound<BV>, start: u32, end: u32) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, GLOBAL_CONTEXT.extract(&base.get().inner, start, end)?)
}

#[pyfunction]
pub fn If(
    py: Python,
    cond: Bound<Bool>,
    then_: Bound<BV>,
    else_: Bound<BV>,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        GLOBAL_CONTEXT.if_(&cond.get().inner, &then_.get().inner, &else_.get().inner)?,
    )
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<BV>()?;

    add_pyfunctions!(
        m, BVS, BVV, Not, And, Or, Xor, Add, Sub, Mul, UDiv, SDiv, UMod, SMod, Pow, ShL, LShR,
        AShR, Concat, Extract, ULT, ULE, UGT, UGE, SLT, SLE, SGT, SGE, Eq_, If,
    );

    Ok(())
}
