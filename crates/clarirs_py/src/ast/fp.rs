#![allow(non_snake_case)]

use std::sync::LazyLock;

use dashmap::DashMap;
use pyo3::types::PyWeakrefReference;

use crate::prelude::*;

static PY_FP_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(name = "RM", module = "clarirs.ast.fp", eq)]
#[derive(Clone, PartialEq, Eq, Default)]
#[allow(non_camel_case_types)]
pub enum PyRM {
    #[default]
    RM_NearestTiesEven,
    RM_NearestTiesAwayFromZero,
    RM_TowardsZero,
    RM_TowardsPositiveInf,
    RM_TowardsNegativeInf,
}

impl From<PyRM> for FPRM {
    fn from(rm: PyRM) -> FPRM {
        match rm {
            PyRM::RM_NearestTiesEven => FPRM::NearestTiesToEven,
            PyRM::RM_NearestTiesAwayFromZero => FPRM::NearestTiesToAway,
            PyRM::RM_TowardsZero => FPRM::TowardZero,
            PyRM::RM_TowardsPositiveInf => FPRM::TowardPositive,
            PyRM::RM_TowardsNegativeInf => FPRM::TowardNegative,
        }
    }
}

#[pyclass(name = "FSort", module = "clarirs.ast.fp")]
#[derive(Clone)]
pub struct PyFSort(FSort);

impl PyFSort {
    pub fn new(fsort: FSort) -> Self {
        PyFSort(fsort)
    }
}

impl From<PyFSort> for FSort {
    fn from(val: PyFSort) -> Self {
        val.0
    }
}

pub fn fsort_float() -> PyFSort {
    PyFSort(FSort::f32())
}

pub fn fsort_double() -> PyFSort {
    PyFSort(FSort::f64())
}

#[pyclass(extends=Bits, subclass, frozen, weakref, module="clarirs.ast.bits")]
pub struct FP {
    pub(crate) inner: FloatAst<'static>,
}

impl FP {
    pub fn new(py: Python, inner: FloatAst<'static>) -> Result<Py<FP>, ClaripyError> {
        if let Some(cache_hit) = PY_FP_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<FP>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit.unbind())
        } else {
            let this = Py::new(
                py,
                PyClassInitializer::from(Base::new())
                    .add_subclass(Bits::new())
                    .add_subclass(FP {
                        inner: inner.clone(),
                    }),
            )?;
            let weakref = PyWeakrefReference::new_bound(this.bind(py))?;
            PY_FP_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pyfunction]
pub fn FPS(py: Python, name: &str, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    FP::new(py, GLOBAL_CONTEXT.fps(name, sort)?)
}

#[pyfunction]
pub fn FPV(py: Python, value: f64, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT
            .fpv(<f64 as Into<Float>>::into(value).to_fsort(sort.into(), FPRM::default()))?,
    )
}

#[pyfunction(name = "fpToFP", signature = (fp, sort, rm = None))]
pub fn FpToFP(
    py: Python,
    fp: PyRef<FP>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_to_fp(&fp.inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "bvToFpUnsigned", signature = (bv, sort, rm = None))]
pub fn BvToFpUnsigned(
    py: Python,
    bv: Bound<BV>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.bv_to_fp_unsigned(&bv.get().inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToIEEEBV", signature = (fp))]
pub fn fpToIEEEBV(py: Python, fp: Bound<FP>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, GLOBAL_CONTEXT.fp_to_ieeebv(&fp.get().inner)?)
}

#[pyfunction(name = "fpToUBV", signature = (fp, len, rm = None))]
pub fn FpToUbv(
    py: Python,
    fp: Bound<FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        GLOBAL_CONTEXT.fp_to_ubv(&fp.get().inner, len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToSBV", signature = (fp, len, rm = None))]
pub fn FpToBv(
    py: Python,
    fp: Bound<FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        GLOBAL_CONTEXT.fp_to_sbv(&fp.get().inner, len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpNeg", signature = (lhs, rm = None))]
pub fn FpNeg(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_neg(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpAbs", signature = (lhs, rm = None))]
pub fn FpAbs(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_abs(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpAdd", signature = (lhs, rhs, rm = None))]
pub fn FpAdd(
    py: Python,
    lhs: Bound<FP>,
    rhs: Bound<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_add(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSub", signature = (lhs, rhs, rm = None))]
pub fn FpSub(
    py: Python,
    lhs: Bound<FP>,
    rhs: Bound<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_sub(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpMul", signature = (lhs, rhs, rm = None))]
pub fn FpMul(
    py: Python,
    lhs: Bound<FP>,
    rhs: Bound<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_mul(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpDiv", signature = (lhs, rhs, rm = None))]
pub fn FpDiv(
    py: Python,
    lhs: Bound<FP>,
    rhs: Bound<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_div(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSqrt", signature = (lhs, rm = None))]
pub fn FpSqrt(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        GLOBAL_CONTEXT.fp_sqrt(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "FpEq", signature = (lhs, rhs))]
pub fn FpEq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_eq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpNeq", signature = (lhs, rhs))]
pub fn FpNeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_neq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLt", signature = (lhs, rhs))]
pub fn FpLt(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_lt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLeq", signature = (lhs, rhs))]
pub fn FpLeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_leq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGt", signature = (lhs, rhs))]
pub fn FpGt(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_gt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGeq", signature = (lhs, rhs))]
pub fn FpGeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        GLOBAL_CONTEXT.fp_geq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpIsNan", signature = (fp))]
pub fn FpIsNan(py: Python, fp: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, GLOBAL_CONTEXT.fp_is_nan(&fp.get().inner)?)
}

#[pyfunction(name = "fpIsInf", signature = (fp))]
pub fn FpIsInf(py: Python, fp: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, GLOBAL_CONTEXT.fp_is_inf(&fp.get().inner)?)
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyFSort>()?;
    m.add_class::<FP>()?;

    add_pyfunctions!(
        m,
        FPS,
        FPV,
        FpToFP,
        BvToFpUnsigned,
        fpToIEEEBV,
        FpToUbv,
        FpToBv,
        FpNeg,
        FpAbs,
        FpAdd,
        FpSub,
        FpMul,
        FpDiv,
        FpSqrt,
        FpEq,
        FpNeq,
        FpLt,
        FpLeq,
        FpGt,
        FpGeq,
        FpIsNan,
        FpIsInf,
    );

    m.add("FSORT_FLOAT", fsort_float())?;
    m.add("FSORT_DOUBLE", fsort_double())?;

    Ok(())
}
