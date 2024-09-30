#![allow(non_snake_case)]

use ast::bv::BV;

use crate::ast::bits::Bits;
use crate::prelude::*;

#[pyclass(name = "RM", module = "claripy.ast.fp", eq)]
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

#[pyclass(name = "FSort", module = "claripy.ast.fp")]
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

#[pyclass(extends=Bits, subclass, frozen, weakref, module="claripy.ast.bits")]
#[derive(Default)]
pub struct FP;

impl FP {
    pub fn new() -> Self {
        FP {}
    }
}

impl PyAst for FP {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Bits::new_from_astref(ast_ref).add_subclass(FP::new())
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super().into_super()
    }
}

pyop!(FPS, fps, FP, name: String, sort: PyFSort);

#[pyfunction]
pub fn FPV(py: Python, value: f64, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
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
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_to_fp(&get_astref(fp), sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "bvToFpUnsigned", signature = (bv, sort, rm = None))]
pub fn BvToFpUnsigned(
    py: Python,
    bv: PyRef<BV>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.bv_to_fp_unsigned(&get_astref(bv), sort, rm.unwrap_or_default())?,
    )
}

pyop!(fpToIEEEBV, fp_to_ieeebv, BV, FP);

#[pyfunction(name = "fpToUBV", signature = (fp, len, rm = None))]
pub fn FpToUbv(
    py: Python,
    fp: PyRef<FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Py<BV>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_to_ubv(&get_astref(fp), len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToSBV", signature = (fp, len, rm = None))]
pub fn FpToBv(
    py: Python,
    fp: PyRef<FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Py<BV>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_to_sbv(&get_astref(fp), len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpNeg", signature = (lhs, rm = None))]
pub fn FpNeg(py: Python, lhs: PyRef<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_neg(&get_astref(lhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpAbs", signature = (lhs, rm = None))]
pub fn FpAbs(py: Python, lhs: PyRef<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_abs(&get_astref(lhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpAdd", signature = (lhs, rhs, rm = None))]
pub fn FpAdd(
    py: Python,
    lhs: PyRef<FP>,
    rhs: PyRef<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_add(&get_astref(lhs), &get_astref(rhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSub", signature = (lhs, rhs, rm = None))]
pub fn FpSub(
    py: Python,
    lhs: PyRef<FP>,
    rhs: PyRef<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_sub(&get_astref(lhs), &get_astref(rhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpMul", signature = (lhs, rhs, rm = None))]
pub fn FpMul(
    py: Python,
    lhs: PyRef<FP>,
    rhs: PyRef<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_mul(&get_astref(lhs), &get_astref(rhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpDiv", signature = (lhs, rhs, rm = None))]
pub fn FpDiv(
    py: Python,
    lhs: PyRef<FP>,
    rhs: PyRef<FP>,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_div(&get_astref(lhs), &get_astref(rhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSqrt", signature = (lhs, rm = None))]
pub fn FpSqrt(py: Python, lhs: PyRef<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_sqrt(&get_astref(lhs), rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "FpEq", signature = (lhs, rhs))]
pub fn FpEq(py: Python, lhs: PyRef<FP>, rhs: PyRef<FP>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_eq(&get_astref(lhs), &get_astref(rhs))?,
    )
}

#[pyfunction(name = "fpNeq", signature = (lhs, rhs))]
pub fn FpNeq(py: Python, lhs: PyRef<FP>, rhs: PyRef<FP>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_neq(&get_astref(lhs), &get_astref(rhs))?,
    )
}

#[pyfunction(name = "fpLt", signature = (lhs, rhs))]
pub fn FpLt(py: Python, lhs: PyRef<FP>, rhs: PyRef<FP>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_lt(&get_astref(lhs), &get_astref(rhs))?,
    )
}

#[pyfunction(name = "fpLeq", signature = (lhs, rhs))]
pub fn FpLeq(py: Python, lhs: PyRef<FP>, rhs: PyRef<FP>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_leq(&get_astref(lhs), &get_astref(rhs))?,
    )
}

#[pyfunction(name = "fpGt", signature = (lhs, rhs))]
pub fn FpGt(py: Python, lhs: PyRef<FP>, rhs: PyRef<FP>) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.fp_gt(&get_astref(lhs), &get_astref(rhs))?,
    )
}

pyop!(fpIsNan, fp_is_nan, FP, FP);
pyop!(fpIsInf, fp_is_inf, FP, FP);

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
        fpIsNan,
        fpIsInf,
    );

    m.add("FSORT_FLOAT", fsort_float())?;
    m.add("FSORT_DOUBLE", fsort_double())?;

    Ok(())
}
