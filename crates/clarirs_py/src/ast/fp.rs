#![allow(non_snake_case)]

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    LazyLock,
};

use clarirs_core::ast::float::FloatExt;
use dashmap::DashMap;
use pyo3::types::{PyBytes, PyFrozenSet, PyWeakrefReference};

use crate::prelude::*;

static FPS_COUNTER: AtomicUsize = AtomicUsize::new(0);
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

#[pymethods]
impl PyRM {
    #[staticmethod]
    #[allow(clippy::should_implement_trait)]
    pub fn default() -> PyRM {
        <PyRM as Default>::default()
    }
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

impl From<FPRM> for PyRM {
    fn from(rm: FPRM) -> PyRM {
        match rm {
            FPRM::NearestTiesToEven => PyRM::RM_NearestTiesEven,
            FPRM::NearestTiesToAway => PyRM::RM_NearestTiesAwayFromZero,
            FPRM::TowardZero => PyRM::RM_TowardsZero,
            FPRM::TowardPositive => PyRM::RM_TowardsPositiveInf,
            FPRM::TowardNegative => PyRM::RM_TowardsNegativeInf,
        }
    }
}

impl From<&FPRM> for PyRM {
    fn from(rm: &FPRM) -> PyRM {
        match rm {
            FPRM::NearestTiesToEven => PyRM::RM_NearestTiesEven,
            FPRM::NearestTiesToAway => PyRM::RM_NearestTiesAwayFromZero,
            FPRM::TowardZero => PyRM::RM_TowardsZero,
            FPRM::TowardPositive => PyRM::RM_TowardsPositiveInf,
            FPRM::TowardNegative => PyRM::RM_TowardsNegativeInf,
        }
    }
}

#[pyclass(name = "FSort", module = "clarirs.ast.fp")]
#[derive(Clone)]
pub struct PyFSort(FSort);

impl PyFSort {
    pub fn new(fsort: &FSort) -> Self {
        PyFSort(fsort.clone())
    }
}

impl From<PyFSort> for FSort {
    fn from(val: PyFSort) -> Self {
        val.0
    }
}

impl From<FSort> for PyFSort {
    fn from(val: FSort) -> Self {
        PyFSort(val)
    }
}

impl From<&FSort> for PyFSort {
    fn from(val: &FSort) -> Self {
        PyFSort(val.clone())
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
    pub fn new(py: Python, inner: &FloatAst<'static>) -> Result<Py<FP>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name(
        py: Python,
        inner: &FloatAst<'static>,
        name: Option<String>,
    ) -> Result<Py<FP>, ClaripyError> {
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
                PyClassInitializer::from(Base::new_with_name(py, name))
                    .add_subclass(Bits::new())
                    .add_subclass(FP {
                        inner: inner.clone(),
                    }),
            )?;
            let weakref = PyWeakrefReference::new(this.bind(py))?;
            PY_FP_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }

    pub fn concrete_value(&self) -> Result<Option<f64>, ClaripyError> {
        Ok(match self.inner.simplify()?.op() {
            FloatOp::FPV(value) => value.to_f64(),
            _ => None,
        })
    }
}

#[pymethods]
impl FP {
    #[getter]
    pub fn op(&self) -> String {
        self.inner.op().to_opstring()
    }

    #[getter]
    pub fn args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        self.inner.op().extract_py_args(py)
    }

    #[getter]
    pub fn variables(&self, py: Python) -> Result<Py<PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.into_py_any(py))
                .collect::<Result<Vec<_>, _>>()?
                .iter(),
        )?
        .unbind())
    }

    #[getter]
    pub fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    #[getter]
    pub fn annotations(&self, py: Python) -> PyResult<Vec<PyObject>> {
        let pickle_loads = py.import("pickle")?.getattr("loads")?;
        self.inner
            .get_annotations()
            .iter()
            .map(|a| pickle_loads.call1((PyBytes::new(py, a.value()),)))
            .map(|a| a.map(|a| a.unbind()))
            .collect()
    }

    pub fn hash(&self) -> u64 {
        self.inner.hash()
    }

    pub fn __hash__(&self) -> usize {
        self.hash() as usize
    }

    #[getter]
    pub fn depth(&self) -> u32 {
        self.inner.depth()
    }

    pub fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    pub fn simplify(&self, py: Python) -> Result<Py<FP>, ClaripyError> {
        FP::new(py, &self.inner.simplify()?)
    }

    pub fn size(&self) -> usize {
        self.inner.size() as usize
    }

    pub fn __len__(&self) -> usize {
        self.size()
    }

    pub fn annotate(&self, py: Python, annotation: Bound<PyAny>) -> Result<Py<FP>, ClaripyError> {
        let pickle_dumps = py.import("pickle")?.getattr("dumps")?;
        let annotation_bytes = pickle_dumps
            .call1((&annotation,))?
            .downcast::<PyBytes>()?
            .extract::<Vec<u8>>()?;
        let eliminatable = annotation.getattr("eliminatable")?.extract::<bool>()?;
        let relocatable = annotation.getattr("relocatable")?.extract::<bool>()?;
        FP::new(
            py,
            &GLOBAL_CONTEXT.annotated(
                &self.inner,
                Annotation::new("".to_string(), annotation_bytes, eliminatable, relocatable),
            )?,
        )
    }
}

#[pyfunction(signature = (name, sort, explicit_name = false))]
pub fn FPS(
    py: Python,
    name: &str,
    sort: PyFSort,
    explicit_name: bool,
) -> Result<Py<FP>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = FPS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("FP{}_{}_{}", sort.0.size(), name, counter)
    };
    FP::new_with_name(py, &GLOBAL_CONTEXT.fps(&name, sort)?, Some(name))
}

#[pyfunction]
pub fn FPV(py: Python, value: f64, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    let float_value = Float::try_from(value)?;
    FP::new(
        py,
        &GLOBAL_CONTEXT.fpv(float_value.to_fsort(sort.into(), FPRM::default())?)?,
    )
}

#[pyfunction]
pub fn fpFP(
    _py: Python,
    _sign: Bound<BV>,
    _exponent: Bound<BV>,
    _significand: Bound<BV>,
) -> Result<Py<FP>, ClaripyError> {
    todo!("fpFP")
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
        &GLOBAL_CONTEXT.fp_to_fp(&fp.inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToFPUnsigned", signature = (bv, sort, rm = None))]
pub fn BvToFpUnsigned(
    py: Python,
    bv: Bound<BV>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.bv_to_fp_unsigned(&bv.get().inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToIEEEBV", signature = (fp))]
pub fn fpToIEEEBV(py: Python, fp: Bound<FP>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.fp_to_ieeebv(&fp.get().inner)?)
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
        &GLOBAL_CONTEXT.fp_to_ubv(&fp.get().inner, len, rm.unwrap_or_default())?,
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
        &GLOBAL_CONTEXT.fp_to_sbv(&fp.get().inner, len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpNeg", signature = (lhs, rm = None))]
pub fn FpNeg(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_neg(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpAbs", signature = (lhs, rm = None))]
pub fn FpAbs(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_abs(&lhs.get().inner, rm.unwrap_or_default())?,
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
        &GLOBAL_CONTEXT.fp_add(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
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
        &GLOBAL_CONTEXT.fp_sub(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
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
        &GLOBAL_CONTEXT.fp_mul(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
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
        &GLOBAL_CONTEXT.fp_div(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSqrt", signature = (lhs, rm = None))]
pub fn FpSqrt(py: Python, lhs: Bound<FP>, rm: Option<PyRM>) -> Result<Py<FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_sqrt(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpEQ", signature = (lhs, rhs))]
pub fn FpEq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_eq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpNeq", signature = (lhs, rhs))]
pub fn FpNeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_neq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLT", signature = (lhs, rhs))]
pub fn FpLt(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_lt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLEQ", signature = (lhs, rhs))]
pub fn FpLeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_leq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGT", signature = (lhs, rhs))]
pub fn FpGt(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_gt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGEQ", signature = (lhs, rhs))]
pub fn FpGeq(py: Python, lhs: Bound<FP>, rhs: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_geq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpIsNaN", signature = (fp))]
pub fn FpIsNan(py: Python, fp: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.fp_is_nan(&fp.get().inner)?)
}

#[pyfunction(name = "fpIsInf", signature = (fp))]
pub fn FpIsInf(py: Python, fp: Bound<FP>) -> Result<Py<Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.fp_is_inf(&fp.get().inner)?)
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyFSort>()?;
    m.add_class::<FP>()?;

    add_pyfunctions!(
        m,
        FPS,
        FPV,
        fpFP,
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
