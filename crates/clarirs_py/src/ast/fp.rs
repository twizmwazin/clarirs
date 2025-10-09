#![allow(non_snake_case)]

use std::sync::{
    LazyLock,
    atomic::{AtomicUsize, Ordering},
};

use clarirs_core::ast::float::{FloatExt, FloatOpExt};
use dashmap::DashMap;
use pyo3::types::{PyFrozenSet, PyWeakrefReference};

use crate::prelude::*;
use clarirs_core::smtlib::ToSmtLib;

static FPS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_FP_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

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

#[pyclass(name = "FSort", module = "claripy.ast.fp")]
#[derive(Clone)]
pub struct PyFSort(FSort);

impl PyFSort {
    pub fn new(fsort: &FSort) -> Self {
        PyFSort(*fsort)
    }
}

#[pymethods]
impl PyFSort {
    #[getter]
    pub fn length(&self) -> u32 {
        self.0.size()
    }

    #[staticmethod]
    pub fn from_size(size: u32) -> Result<Self, ClaripyError> {
        Ok(PyFSort(match size {
            32 => FSort::f32(),
            64 => FSort::f64(),
            _ => {
                return Err(ClaripyError::InvalidOperation(
                    "Unsuported float size".to_string(),
                ));
            }
        }))
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
        PyFSort(*val)
    }
}

pub fn fsort_float() -> PyFSort {
    PyFSort(FSort::f32())
}

pub fn fsort_double() -> PyFSort {
    PyFSort(FSort::f64())
}

#[pyclass(extends=Bits, subclass, frozen, weakref, module="claripy.ast.bits")]
pub struct FP {
    pub(crate) inner: FloatAst<'static>,
}

impl FP {
    pub fn new<'py>(
        py: Python<'py>,
        inner: &FloatAst<'static>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name<'py>(
        py: Python<'py>,
        inner: &FloatAst<'static>,
        name: Option<String>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        if let Some(cache_hit) = PY_FP_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<FP>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit)
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

            Ok(this.into_bound(py))
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
        self.inner.to_opstring()
    }

    #[getter]
    pub fn args<'py>(&self, py: Python<'py>) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        self.inner.extract_py_args(py)
    }

    #[getter]
    pub fn variables<'py>(&self, py: Python<'py>) -> Result<Bound<'py, PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.into_py_any(py))
                .collect::<Result<Vec<_>, _>>()?
                .iter(),
        )?)
    }

    #[getter]
    pub fn symbolic(&self) -> bool {
        self.inner.symbolic()
    }

    #[getter]
    pub fn concrete(&self) -> bool {
        !self.inner.symbolic()
    }

    #[getter]
    pub fn annotations(&self) -> PyResult<Vec<PyAnnotation>> {
        Ok(self
            .inner
            .annotations()
            .iter()
            .cloned()
            .map(PyAnnotation::from)
            .collect())
    }

    pub fn hash(&self) -> u64 {
        self.inner.hash()
    }

    pub fn __hash__(&self) -> usize {
        self.hash() as usize
    }

    pub fn __repr__(&self) -> String {
        self.inner.to_smtlib()
    }

    #[getter]
    pub fn depth(&self) -> u32 {
        self.inner.depth()
    }

    pub fn is_leaf(&self) -> bool {
        self.inner.depth() == 1
    }

    pub fn simplify<'py>(&self, py: Python<'py>) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(py, &self.inner.simplify()?)
    }

    pub fn size(&self) -> usize {
        self.inner.size() as usize
    }

    pub fn __len__(&self) -> usize {
        self.size()
    }

    pub fn has_annotation_type(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<bool, ClaripyError> {
        Ok(self
            .annotations()?
            .iter()
            .any(|annotation| annotation_type.matches(annotation.0.type_())))
    }

    pub fn get_annotations_by_type(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<Vec<PyAnnotation>, ClaripyError> {
        Ok(self
            .annotations()?
            .into_iter()
            .filter(|annotation| annotation_type.matches(annotation.0.type_()))
            .collect())
    }

    pub fn get_annotation(
        &self,
        annotation_type: PyAnnotationType,
    ) -> Result<Option<PyAnnotation>, ClaripyError> {
        Ok(self
            .annotations()?
            .into_iter()
            .find(|annotation| annotation_type.matches(annotation.0.type_())))
    }

    pub fn append_annotation<'py>(
        &self,
        py: Python<'py>,
        annotation: PyAnnotation,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        Self::new(
            py,
            &GLOBAL_CONTEXT.annotate(&self.inner, annotation.0.clone())?,
        )
    }

    pub fn append_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let mut inner = self.inner.clone();
        for annotation in annotations {
            inner = GLOBAL_CONTEXT.annotate(&inner, annotation.0)?;
        }
        Self::new(py, &inner)
    }

    #[pyo3(signature = (*annotations))]
    pub fn annotate<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        Self::new(
            py,
            &annotations
                .iter()
                .try_fold(self.inner.clone(), |acc, annotation| {
                    GLOBAL_CONTEXT.annotate(&acc, annotation.0.clone())
                })?,
        )
    }

    pub fn insert_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let mut inner = self.inner.clone();
        for annotation in annotations {
            inner = GLOBAL_CONTEXT.annotate(&inner, annotation.0)?;
        }
        Self::new(py, &inner)
    }

    /// This actually just removes all annotations and adds the new ones.
    pub fn replace_annotations<'py>(
        &self,
        py: Python<'py>,
        annotations: Vec<PyAnnotation>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_float_annotated(
            self.inner.op().clone(),
            annotations.into_iter().map(|a| a.0).collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn remove_annotation<'py>(
        &self,
        py: Python<'py>,
        annotation: PyAnnotation,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_float_annotated(
            self.inner.op().clone(),
            self.inner
                .annotations()
                .iter()
                .filter(|a| **a != annotation.0)
                .cloned()
                .collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn clear_annotations<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_float(self.inner.op().clone())?;
        Self::new(py, &inner)
    }

    pub fn clear_annotation_type<'py>(
        &self,
        py: Python<'py>,
        annotation_type: PyAnnotationType,
    ) -> Result<Bound<'py, Self>, ClaripyError> {
        let inner = self.inner.context().make_float_annotated(
            self.inner.op().clone(),
            self.inner
                .annotations()
                .iter()
                .filter(|a| !annotation_type.matches(a.type_()))
                .cloned()
                .collect(),
        )?;
        Self::new(py, &inner)
    }

    pub fn raw_to_bv(self_: Bound<'_, FP>) -> Result<Bound<'_, BV>, ClaripyError> {
        BV::new(
            self_.py(),
            &GLOBAL_CONTEXT.fp_to_ieeebv(&self_.get().inner)?,
        )
    }

    pub fn raw_to_fp(self_: Bound<'_, FP>) -> Result<Bound<'_, FP>, ClaripyError> {
        Ok(self_)
    }

    pub fn to_bv(self_: Bound<'_, FP>) -> Result<Bound<'_, BV>, ClaripyError> {
        BV::new(
            self_.py(),
            &GLOBAL_CONTEXT.fp_to_sbv(
                &self_.get().inner,
                self_.get().inner.sort().size(),
                FPRM::default(),
            )?,
        )
    }

    pub fn __eq__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_eq(&self.inner, &other.into())?)
    }

    pub fn __ne__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_neq(&self.inner, &other.into())?)
    }

    pub fn __lt__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_lt(&self.inner, &other.into())?)
    }

    pub fn __le__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_leq(&self.inner, &other.into())?)
    }

    pub fn __gt__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_gt(&self.inner, &other.into())?)
    }

    pub fn __ge__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(py, &GLOBAL_CONTEXT.fp_geq(&self.inner, &other.into())?)
    }

    pub fn __abs__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(py, &GLOBAL_CONTEXT.fp_abs(&self.inner)?)
    }

    pub fn __neg__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(py, &GLOBAL_CONTEXT.fp_neg(&self.inner)?)
    }

    pub fn __add__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(
            py,
            &GLOBAL_CONTEXT.fp_add(&self.inner, &other.into(), PyRM::default())?,
        )
    }

    pub fn __sub__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(
            py,
            &GLOBAL_CONTEXT.fp_sub(&self.inner, &other.into(), PyRM::default())?,
        )
    }

    pub fn __mul__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(
            py,
            &GLOBAL_CONTEXT.fp_mul(&self.inner, &other.into(), PyRM::default())?,
        )
    }

    pub fn __truediv__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceFP<'py>,
    ) -> Result<Bound<'py, FP>, ClaripyError> {
        FP::new(
            py,
            &GLOBAL_CONTEXT.fp_div(&self.inner, &other.into(), PyRM::default())?,
        )
    }
}

#[pyfunction(signature = (name, sort, explicit_name = false))]
pub fn FPS<'py>(
    py: Python<'py>,
    name: &str,
    sort: PyFSort,
    explicit_name: bool,
) -> Result<Bound<'py, FP>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = FPS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("FP{}_{}_{}", sort.0.size(), name, counter)
    };
    FP::new_with_name(py, &GLOBAL_CONTEXT.fps(&name, sort)?, Some(name))
}

#[pyfunction]
pub fn FPV(py: Python<'_>, value: f64, sort: PyFSort) -> Result<Bound<'_, FP>, ClaripyError> {
    let float_value = Float::from(value);
    FP::new(
        py,
        &GLOBAL_CONTEXT.fpv(float_value.to_fsort(sort.into(), FPRM::default())?)?,
    )
}

#[pyfunction]
pub fn fpFP<'py>(
    _py: Python<'py>,
    _sign: Bound<'py, BV>,
    _exponent: Bound<'py, BV>,
    _significand: Bound<'py, BV>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    todo!("fpFP")
}

#[pyfunction(name = "fpToFP", signature = (fp, sort, rm = None))]
pub fn FpToFP<'py>(
    py: Python<'py>,
    fp: PyRef<'py, FP>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_to_fp(&fp.inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToFPUnsigned", signature = (bv, sort, rm = None))]
pub fn BvToFpUnsigned<'py>(
    py: Python<'py>,
    bv: Bound<'py, BV>,
    sort: PyFSort,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.bv_to_fp_unsigned(&bv.get().inner, sort, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToIEEEBV", signature = (fp))]
pub fn fpToIEEEBV<'py>(
    py: Python<'py>,
    fp: Bound<'py, FP>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.fp_to_ieeebv(&fp.get().inner)?)
}

#[pyfunction(name = "fpToUBV", signature = (fp, len, rm = None))]
pub fn FpToUbv<'py>(
    py: Python<'py>,
    fp: Bound<'py, FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.fp_to_ubv(&fp.get().inner, len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpToSBV", signature = (fp, len, rm = None))]
pub fn FpToBv<'py>(
    py: Python<'py>,
    fp: Bound<'py, FP>,
    len: u32,
    rm: Option<PyRM>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.fp_to_sbv(&fp.get().inner, len, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpNeg", signature = (lhs))]
pub fn FpNeg<'py>(py: Python<'py>, lhs: Bound<'py, FP>) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(py, &GLOBAL_CONTEXT.fp_neg(&lhs.get().inner)?)
}

#[pyfunction(name = "fpAbs", signature = (lhs))]
pub fn FpAbs<'py>(py: Python<'py>, lhs: Bound<'py, FP>) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(py, &GLOBAL_CONTEXT.fp_abs(&lhs.get().inner)?)
}

#[pyfunction(name = "fpAdd", signature = (lhs, rhs, rm = None))]
pub fn FpAdd<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_add(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSub", signature = (lhs, rhs, rm = None))]
pub fn FpSub<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_sub(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpMul", signature = (lhs, rhs, rm = None))]
pub fn FpMul<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_mul(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpDiv", signature = (lhs, rhs, rm = None))]
pub fn FpDiv<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_div(&lhs.get().inner, &rhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpSqrt", signature = (lhs, rm = None))]
pub fn FpSqrt<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rm: Option<PyRM>,
) -> Result<Bound<'py, FP>, ClaripyError> {
    FP::new(
        py,
        &GLOBAL_CONTEXT.fp_sqrt(&lhs.get().inner, rm.unwrap_or_default())?,
    )
}

#[pyfunction(name = "fpEQ", signature = (lhs, rhs))]
pub fn FpEq<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_eq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpNeq", signature = (lhs, rhs))]
pub fn FpNeq<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_neq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLT", signature = (lhs, rhs))]
pub fn FpLt<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_lt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpLEQ", signature = (lhs, rhs))]
pub fn FpLeq<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_leq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGT", signature = (lhs, rhs))]
pub fn FpGt<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_gt(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpGEQ", signature = (lhs, rhs))]
pub fn FpGeq<'py>(
    py: Python<'py>,
    lhs: Bound<'py, FP>,
    rhs: Bound<'py, FP>,
) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(
        py,
        &GLOBAL_CONTEXT.fp_geq(&lhs.get().inner, &rhs.get().inner)?,
    )
}

#[pyfunction(name = "fpIsNaN", signature = (fp))]
pub fn FpIsNan<'py>(py: Python<'py>, fp: Bound<'py, FP>) -> Result<Bound<'py, Bool>, ClaripyError> {
    Bool::new(py, &GLOBAL_CONTEXT.fp_is_nan(&fp.get().inner)?)
}

#[pyfunction(name = "fpIsInf", signature = (fp))]
pub fn FpIsInf<'py>(py: Python<'py>, fp: Bound<'py, FP>) -> Result<Bound<'py, Bool>, ClaripyError> {
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
