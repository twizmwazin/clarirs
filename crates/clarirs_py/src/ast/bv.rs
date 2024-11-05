#![allow(non_snake_case)]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::LazyLock;

use clarirs_core::ast::bitvec::BitVecExt;
use dashmap::DashMap;
use num_bigint::{BigInt, BigUint};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::types::{PyBytes, PyFrozenSet, PyWeakrefReference};

use crate::ast::{And, Not, Or, Xor};
use crate::prelude::*;

static BVS_COUNTER: AtomicUsize = AtomicUsize::new(0);
static PY_BV_CACHE: LazyLock<DashMap<u64, Py<PyWeakrefReference>>> = LazyLock::new(DashMap::new);

#[pyclass(extends=Bits, subclass, frozen, weakref, module="clarirs.ast.bv")]
pub struct BV {
    pub(crate) inner: BitVecAst<'static>,
}

impl BV {
    pub fn new(py: Python, inner: &BitVecAst<'static>) -> Result<Py<BV>, ClaripyError> {
        Self::new_with_name(py, inner, None)
    }

    pub fn new_with_name(
        py: Python,
        inner: &BitVecAst<'static>,
        name: Option<String>,
    ) -> Result<Py<BV>, ClaripyError> {
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
                PyClassInitializer::from(Base::new_with_name(py, name))
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
impl BV {
    #[new]
    pub fn py_new(py: Python, op: &str, args: Vec<PyObject>) -> Result<Py<BV>, ClaripyError> {
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
        self.inner.op().to_opstring()
    }

    #[getter]
    pub fn args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        self.inner.op().extract_py_args(py)
    }

    #[getter]
    pub fn variables(&self, py: Python) -> Result<Py<PyFrozenSet>, ClaripyError> {
        Ok(PyFrozenSet::new_bound(
            py,
            self.inner
                .variables()
                .iter()
                .map(|v| v.to_object(py))
                .collect::<Vec<_>>()
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
        let pickle_loads = py.import_bound("pickle")?.getattr("loads")?;
        self.inner
            .get_annotations()
            .iter()
            .map(|a| pickle_loads.call1((PyBytes::new_bound(py, a.value()),)))
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

    pub fn size(&self) -> usize {
        self.inner.size() as usize
    }

    pub fn __len__(&self) -> usize {
        self.size()
    }

    pub fn annotate(&self, py: Python, annotation: Bound<PyAny>) -> Result<Py<BV>, ClaripyError> {
        let pickle_dumps = py.import_bound("pickle")?.getattr("dumps")?;
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

    pub fn __add__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.add(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __radd__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__add__(py, other)
    }

    pub fn __sub__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sub(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rsub__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__sub__(py, other)
    }

    pub fn __mul__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.mul(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rmul__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__mul__(py, other)
    }

    pub fn __truediv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rtruediv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__truediv__(py, other)
    }

    pub fn __floordiv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rfloordiv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__floordiv__(py, other)
    }

    pub fn __pow__(
        &self,
        py: Python,
        other: CoerceBV,
        _modulo: PyObject,
    ) -> Result<Py<BV>, ClaripyError> {
        // TODO: handle modulo
        BV::new(
            py,
            &GLOBAL_CONTEXT.pow(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rpow__(
        &self,
        py: Python,
        other: CoerceBV,
        _modulo: PyObject,
    ) -> Result<Py<BV>, ClaripyError> {
        self.__pow__(py, other, _modulo)
    }

    pub fn __mod__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.urem(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rmod__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__mod__(py, other)
    }

    pub fn SDiv(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sdiv(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SMod(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.srem(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __and__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rand__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__and__(py, other)
    }

    pub fn __or__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ror__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__or__(py, other)
    }

    pub fn __xor__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rxor__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__xor__(py, other)
    }

    pub fn __lshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.shl(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rlshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__lshift__(py, other)
    }

    pub fn __rshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.ashr(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __rrshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__rshift__(py, other)
    }

    pub fn LShR(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.lshr(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __neg__(&self, py: Python) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __invert__(&self, py: Python) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.not(&self.inner)?)
    }

    pub fn __pos__(self_: Py<BV>) -> Result<Py<BV>, ClaripyError> {
        Ok(self_)
    }

    pub fn __abs__(&self, py: Python) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.abs(&self.inner)?)
    }

    pub fn __eq__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.eq_(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ne__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __lt__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __le__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __gt__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn __ge__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn ULT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn ULE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn UGT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn UGE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SLT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.slt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SLE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sle(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SGT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sgt(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn SGE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sge(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn Extract(
        &self,
        py: Python,
        upper_bound: u32,
        lower_bound: u32,
    ) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.extract(&self.inner, upper_bound, lower_bound)?,
        )
    }

    pub fn concat(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.concat(&self.inner, &other.extract_like(py, self)?.get().inner)?,
        )
    }

    pub fn zero_extend(&self, py: Python, amount: u32) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.zero_ext(&self.inner, amount)?)
    }

    pub fn sign_extend(&self, py: Python, amount: u32) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.sign_ext(&self.inner, amount)?)
    }

    #[getter]
    pub fn reversed(&self, py: Python) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.reverse(&self.inner)?)
    }
}

#[pyfunction(signature = (name, size, explicit_name = false))]
pub fn BVS(
    py: Python,
    name: String,
    size: u32,
    explicit_name: bool,
) -> Result<Py<BV>, ClaripyError> {
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
pub fn BVV(py: Python, value: Bound<PyAny>, size: Option<u32>) -> Result<Py<BV>, PyErr> {
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
        log::warn!("string value passed to BVV, assuming utf-8");
        let bytes_val = str_val.as_bytes();
        let int_val = BigUint::from_bytes_le(bytes_val);
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
    Err(PyErr::new::<PyTypeError, _>(
        "BVV value must be a int, bytes, or str",
    ))
}

macro_rules! binop {
    ($name:ident, $context_method:ident, $ret:ty) => {
        #[pyfunction]
        pub fn $name(py: Python, lhs: CoerceBV, rhs: CoerceBV) -> Result<Py<$ret>, ClaripyError> {
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
pub fn Concat(py: Python, args: Vec<Bound<BV>>) -> Result<Py<BV>, ClaripyError> {
    let mut args = args.into_iter();
    let first = args.next().ok_or(ClaripyError::MissingArgIndex(0))?;
    args.try_fold(first, |acc, arg| {
        Concat_inner(py, acc.into(), arg.unbind().into()).map(|r| r.bind(py).clone())
    })
    .map(|r| r.unbind())
}

#[pyfunction]
pub fn Extract(py: Python, end: u32, start: u32, base: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.extract(&base.get().inner, start, end)?)
}

#[pyfunction]
pub fn ZeroExt(py: Python, amount: u32, base: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.zero_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn SignExt(py: Python, amount: u32, base: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.sign_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn Reverse(py: Python, base: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
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
        Not,
        And,
        Or,
        Xor,
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
        super::If,
    );

    Ok(())
}
