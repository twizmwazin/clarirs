#![allow(non_snake_case)]

use std::iter::once;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use clarirs_core::ast::bitvec::BitVecExt;
use dashmap::DashMap;
use num_bigint::{BigInt, BigUint};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::types::{PyBytes, PyFrozenSet, PySlice, PyWeakrefReference};

use crate::ast::{and, not, or, xor};
use crate::prelude::*;
use crate::pyslicemethodsext::PySliceMethodsExt;
use clarirs_core::smtlib::ToSmtLib;

static BVS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BV_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Bits, subclass, frozen, weakref, module="clarirs.ast.bv")]
pub struct BV {
    pub(crate) inner: BitVecAst<'static>,
}

impl BV {
    pub fn new<'py>(
        py: Python<'py>,
        inner: &BitVecAst<'static>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name<'py>(
        py: Python<'py>,
        inner: &BitVecAst<'static>,
        name: Option<String>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        if let Some(cache_hit) = PY_BV_CACHE.get(&inner.hash()).and_then(|cache_hit| {
            cache_hit
                .bind(py)
                .upgrade_as::<BV>()
                .expect("bool cache poisoned")
        }) {
            Ok(cache_hit)
        } else {
            let this = Bound::new(
                py,
                PyClassInitializer::from(Base::new_with_name(py, name))
                    .add_subclass(Bits::new())
                    .add_subclass(BV {
                        inner: inner.clone(),
                    }),
            )?;
            let weakref = PyWeakrefReference::new(&this)?;
            PY_BV_CACHE.insert(inner.hash(), weakref.unbind());

            Ok(this)
        }
    }
}

#[pymethods]
impl BV {
    #[new]
    pub fn py_new<'py>(
        py: Python<'py>,
        op: &str,
        args: Vec<PyObject>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &match op {
                "BVS" => {
                    GLOBAL_CONTEXT.bvs(args[0].extract::<String>(py)?, args[1].extract(py)?)?
                }
                "BVV" => GLOBAL_CONTEXT
                    .bvv_from_biguint_with_size(&args[0].extract(py)?, args[1].extract(py)?)?,
                "__neg__" => GLOBAL_CONTEXT.not(&args[0].downcast_bound::<BV>(py)?.get().inner)?,
                "__and__" => GLOBAL_CONTEXT.and(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__or__" => GLOBAL_CONTEXT.or(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__xor__" => GLOBAL_CONTEXT.xor(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__abs__" => GLOBAL_CONTEXT.abs(&args[0].downcast_bound::<BV>(py)?.get().inner)?,
                "__add__" => GLOBAL_CONTEXT.add(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__sub__" => GLOBAL_CONTEXT.sub(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__mul__" => GLOBAL_CONTEXT.mul(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__floordiv__" => GLOBAL_CONTEXT.udiv(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SDiv" => GLOBAL_CONTEXT.sdiv(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__mod__" => GLOBAL_CONTEXT.urem(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "SMod" => GLOBAL_CONTEXT.srem(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__pow__" => GLOBAL_CONTEXT.pow(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__lshift__" => GLOBAL_CONTEXT.shl(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "LShR" => GLOBAL_CONTEXT.lshr(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "__rshift__" => GLOBAL_CONTEXT.ashr(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "RotateLeft" => GLOBAL_CONTEXT.rotate_left(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "RotateRight" => GLOBAL_CONTEXT.rotate_right(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "ZeroExt" => GLOBAL_CONTEXT.zero_ext(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    args[1].extract(py)?,
                )?,
                "SignExt" => GLOBAL_CONTEXT.sign_ext(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    args[1].extract(py)?,
                )?,
                "Extract" => GLOBAL_CONTEXT.extract(
                    &args[2].downcast_bound::<BV>(py)?.get().inner,
                    args[0].extract(py)?,
                    args[1].extract(py)?,
                )?,
                "Concat" => GLOBAL_CONTEXT.concat(
                    &args[0].downcast_bound::<BV>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "Reverse" => {
                    GLOBAL_CONTEXT.reverse(&args[0].downcast_bound::<BV>(py)?.get().inner)?
                }
                "fpToIEEEBV" => {
                    GLOBAL_CONTEXT.fp_to_ieeebv(&args[0].downcast_bound::<FP>(py)?.get().inner)?
                }
                // "fpToUBV" => GLOBAL_CONTEXT.fp_to_ubv(
                //     &args[0].downcast_bound::<FP>(py)?.get().inner,
                // )?,
                // "fpToSBV" => GLOBAL_CONTEXT.fp_to_sbv(
                //     &args[0].downcast_bound::<FP>(py)?.get().inner,
                // )?,
                "StrLen" => GLOBAL_CONTEXT
                    .strlen(&args[0].downcast_bound::<PyAstString>(py)?.get().inner)?,
                "StrIndexOf" => GLOBAL_CONTEXT.strindexof(
                    &args[0].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[1].downcast_bound::<PyAstString>(py)?.get().inner,
                    &args[2].downcast_bound::<BV>(py)?.get().inner,
                )?,
                "StrToBV" => GLOBAL_CONTEXT
                    .strtobv(&args[0].downcast_bound::<PyAstString>(py)?.get().inner)?,
                "If" => GLOBAL_CONTEXT.if_(
                    &args[0].downcast_bound::<Bool>(py)?.get().inner,
                    &args[1].downcast_bound::<BV>(py)?.get().inner,
                    &args[2].downcast_bound::<BV>(py)?.get().inner,
                )?,
                _ => return Err(ClaripyError::InvalidOperation(op.to_string())),
            },
        )
    }

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

    pub fn simplify<'py>(&self, py: Python<'py>) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &self.inner.simplify()?)
    }

    pub fn size(&self) -> usize {
        self.inner.size() as usize
    }

    pub fn __len__(&self) -> usize {
        self.size()
    }

    #[getter]
    pub fn length(&self) -> usize {
        self.size()
    }

    #[getter]
    pub fn concrete_value(&self) -> Result<Option<BigUint>, ClaripyError> {
        Ok(match self.inner.simplify()?.op() {
            BitVecOp::BVV(bv) => Some(bv.as_biguint()),
            _ => None,
        })
    }

    pub fn __getitem__<'py>(
        self_: Bound<'py, BV>,
        range: Bound<'py, PyAny>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        if let Ok(slice) = range.downcast::<PySlice>() {
            if slice.step()?.is_some() {
                return Err(ClaripyError::InvalidOperation(
                    "slicing with step is not supported".to_string(),
                ));
            }

            let py = self_.py();
            let size = self_.get().size() as isize;

            // We use weird backwards SMTLIB indexing rules that are not python
            // rules. These conditions should fix it up to make the default
            // values correct
            let mut start = slice.start()?.unwrap_or(size - 1);
            let mut stop = slice.stop()?.unwrap_or(0);

            if start < 0 {
                start += size;
            }
            if stop < 0 {
                stop += size;
            }

            Extract(self_.py(), start as u32, stop as u32, self_)?
                .get()
                .simplify(py)
        } else if let Ok(int_val) = range.extract::<u32>() {
            Extract(self_.py(), int_val, int_val, self_)
        } else {
            Err(ClaripyError::FailedToExtractArg(range.unbind()))
        }
    }

    pub fn annotate<'py>(
        &self,
        py: Python<'py>,
        annotation: Bound<PyAny>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        let pickle_dumps = py.import("pickle")?.getattr("dumps")?;
        let annotation_bytes = pickle_dumps
            .call1((&annotation,))?
            .downcast::<PyBytes>()?
            .extract::<Vec<u8>>()?;
        let eliminatable = annotation.getattr("eliminatable")?.extract::<bool>()?;
        let relocatable = annotation.getattr("relocatable")?.extract::<bool>()?;
        BV::new(
            py,
            &GLOBAL_CONTEXT.annotated(
                &self.inner,
                Annotation::new("".to_string(), annotation_bytes, eliminatable, relocatable),
            )?,
        )
    }

    pub fn __add__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.add(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __radd__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__add__(py, other)
    }

    pub fn __sub__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sub(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rsub__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__sub__(py, other)
    }

    pub fn __mul__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.mul(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rmul__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__mul__(py, other)
    }

    pub fn __truediv__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rtruediv__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__truediv__(py, other)
    }

    pub fn __floordiv__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rfloordiv__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__floordiv__(py, other)
    }

    pub fn __pow__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
        _modulo: PyObject,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        // TODO: handle modulo
        BV::new(
            py,
            &GLOBAL_CONTEXT.pow(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rpow__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
        _modulo: PyObject,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__pow__(py, other, _modulo)
    }

    pub fn __mod__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.urem(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rmod__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__mod__(py, other)
    }

    pub fn SDiv<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sdiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SMod<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.srem(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __and__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rand__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__and__(py, other)
    }

    pub fn __or__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ror__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__or__(py, other)
    }

    pub fn __xor__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rxor__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__xor__(py, other)
    }

    pub fn __lshift__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.shl(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rlshift__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__lshift__(py, other)
    }

    pub fn __rshift__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.ashr(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rrshift__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        self.__rshift__(py, other)
    }

    pub fn LShR<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.lshr(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __neg__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __invert__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __pos__(self_: Bound<BV>) -> Result<Bound<BV>, ClaripyError> {
        Ok(self_)
    }

    pub fn __abs__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.abs(&self.inner)?)
    }

    pub fn __eq__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.eq_(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ne__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __lt__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __le__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __gt__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ge__<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn ULT<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn ULE<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn UGT<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn UGE<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SLT<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.slt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SLE<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sle(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SGT<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sgt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SGE<'py>(
        &self,
        py: Python<'py>,
        other: CoerceBV,
    ) -> Result<Bound<'py, Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn Extract<'py>(
        &self,
        py: Python<'py>,
        upper_bound: u32,
        lower_bound: u32,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.extract(&self.inner, upper_bound, lower_bound)?,
        )
    }

    #[pyo3(signature = (*args))]
    pub fn concat<'py>(
        self_: Bound<'py, BV>,
        py: Python<'py>,
        args: Vec<Bound<'py, BV>>,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        Concat(py, once(self_).chain(args.iter().cloned()).collect())
    }

    pub fn zero_extend<'py>(
        &self,
        py: Python<'py>,
        amount: u32,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.zero_ext(&self.inner, amount)?)
    }

    pub fn sign_extend<'py>(
        &self,
        py: Python<'py>,
        amount: u32,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.sign_ext(&self.inner, amount)?)
    }

    #[getter]
    pub fn reversed<'py>(&self, py: Python<'py>) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.reverse(&self.inner)?)
    }

    pub fn get_bytes<'py>(
        self_: Bound<'py, BV>,
        py: Python<'py>,
        index: u32,
        size: u32,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        Extract(py, (index + size) * 8 - 1, index * 8, self_)?
            .get()
            .simplify(py)
    }

    pub fn get_byte<'py>(
        self_: Bound<'py, BV>,
        py: Python<'py>,
        index: u32,
    ) -> Result<Bound<'py, BV>, ClaripyError> {
        BV::get_bytes(self_, py, index, 1)
    }

    pub fn chop<'py>(
        self_: Bound<'py, BV>,
        py: Python<'py>,
        bits: u32,
    ) -> Result<Vec<Bound<'py, BV>>, ClaripyError> {
        self_.get().inner.chop(bits).map(|r| {
            r.into_iter()
                .map(|r| BV::new(py, &r))
                .collect::<Result<Vec<_>, _>>()
        })?
    }
}

#[pyfunction(signature = (name, size, explicit_name = false))]
pub fn BVS(
    py: Python<'_>,
    name: String,
    size: u32,
    explicit_name: bool,
) -> Result<Bound<'_, BV>, ClaripyError> {
    let name: String = if explicit_name {
        name.to_string()
    } else {
        let counter = BVS_COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("BV{}_{}_{}", size, name, counter)
    };
    BV::new_with_name(py, &GLOBAL_CONTEXT.bvs(&name, size)?, Some(name.clone()))
}

#[allow(non_snake_case)]
#[pyfunction(signature = (value, size = None))]
pub fn BVV<'py>(
    py: Python<'py>,
    value: Bound<PyAny>,
    size: Option<u32>,
) -> Result<Bound<'py, BV>, PyErr> {
    if let Ok(int_val) = value.extract::<BigUint>() {
        if let Some(size) = size {
            let a = GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, size)
                .map_err(ClaripyError::from)?;
            return Ok(BV::new(py, &a)?);
        } else {
            return Err(PyErr::new::<PyValueError, _>("size must be specified"));
        }
    }
    if let Ok(int_val) = value.extract::<BigInt>() {
        if let Some(size) = size {
            let uint_value = int_val.to_biguint().unwrap_or(
                ((BigInt::from(1) << (size - 1)) + int_val)
                    .to_biguint()
                    .expect("BigInt to BigUInt failed"),
            );
            let a = GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&uint_value, size)
                .map_err(ClaripyError::from)?;
            return Ok(BV::new(py, &a)?);
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
            &GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, bytes_val.len() as u32 * 8)
                .map_err(ClaripyError::from)?,
        )?);
    }
    if let Ok(str_val) = value.extract::<String>() {
        log::warn!("string value passed to BVV, assuming utf-8/big-endian");
        let bytes_val = str_val.as_bytes();
        let int_val = BigUint::from_bytes_le(bytes_val);
        if size.is_some() {
            log::warn!("BVV size specified with string, value will be ignored");
        }
        return Ok(BV::new(
            py,
            &GLOBAL_CONTEXT
                .bvv_from_biguint_with_size(&int_val, bytes_val.len() as u32 * 8)
                .map_err(ClaripyError::from)?,
        )?);
    }
    Err(PyErr::new::<PyTypeError, _>(
        "BVV value must be a int, bytes, or str",
    ))
}

macro_rules! binop {
    ($name:ident, $context_method:ident, $ret:ty) => {
        #[pyfunction]
        pub fn $name<'py>(
            py: Python<'py>,
            lhs: CoerceBV<'py>,
            rhs: CoerceBV<'py>,
        ) -> Result<Bound<'py, $ret>, ClaripyError> {
            let (elhs, erhs) = CoerceBV::extract_pair(py, &lhs, &rhs)?;
            <$ret>::new(
                py,
                &GLOBAL_CONTEXT.$context_method(&elhs.get().inner, &erhs.get().inner)?,
            )
        }
    };
}

binop!(Add, add, BV);
binop!(Sub, sub, BV);
binop!(Mul, mul, BV);
binop!(UDiv, udiv, BV);
binop!(SDiv, sdiv, BV);
binop!(UMod, urem, BV);
binop!(SMod, srem, BV);
binop!(Pow, pow, BV);
binop!(ShL, shl, BV);
binop!(LShR, lshr, BV);
binop!(AShR, ashr, BV);
binop!(RotateLeft, rotate_left, BV);
binop!(RotateRight, rotate_right, BV);
binop!(Concat_inner, concat, BV);

#[pyfunction(signature = (*args))]
pub fn Concat<'py>(
    py: Python<'py>,
    args: Vec<Bound<'py, BV>>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    let mut args = args.into_iter();
    let first = args.next().ok_or(ClaripyError::MissingArgIndex(0))?;
    args.try_fold(first, |acc, arg| Concat_inner(py, acc.into(), arg.into()))
}

#[pyfunction]
pub fn Extract<'py>(
    py: Python<'py>,
    upper: u32,
    lower: u32,
    base: Bound<'py, BV>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.extract(&base.get().inner, upper, lower)?,
    )
}

#[pyfunction]
pub fn ZeroExt<'py>(
    py: Python<'py>,
    amount: u32,
    base: Bound<'py, BV>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.zero_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn SignExt<'py>(
    py: Python<'py>,
    amount: u32,
    base: Bound<'py, BV>,
) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.sign_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn Reverse<'py>(py: Python<'py>, base: Bound<'py, BV>) -> Result<Bound<'py, BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.reverse(&base.get().inner)?)
}

binop!(ULT, ult, Bool);
binop!(ULE, ule, Bool);
binop!(UGT, ugt, Bool);
binop!(UGE, uge, Bool);
binop!(SLT, slt, Bool);
binop!(SLE, sle, Bool);
binop!(SGT, sgt, Bool);
binop!(SGE, sge, Bool);
binop!(Eq_, eq_, Bool);
binop!(Neq, neq, Bool);

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<BV>()?;

    add_pyfunctions!(
        m,
        BVS,
        BVV,
        not,
        and,
        or,
        xor,
        Add,
        Sub,
        Mul,
        UDiv,
        SDiv,
        UMod,
        SMod,
        Pow,
        ShL,
        LShR,
        AShR,
        RotateLeft,
        RotateRight,
        Concat,
        Extract,
        ZeroExt,
        SignExt,
        Reverse,
        ULT,
        ULE,
        UGT,
        UGE,
        SLT,
        SLE,
        SGT,
        SGE,
        Eq_,
        super::r#if,
    );

    Ok(())
}
