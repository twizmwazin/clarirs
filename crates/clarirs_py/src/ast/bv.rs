#![allow(non_snake_case)]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::LazyLock;

use clarirs_core::ast::bitvec::BitVecExt;
use dashmap::DashMap;
use num_bigint::BigUint;
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
            &GLOBAL_CONTEXT.add(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __radd__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__add__(py, other)
    }

    pub fn __sub__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sub(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rsub__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__sub__(py, other)
    }

    pub fn __mul__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.mul(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rmul__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__mul__(py, other)
    }

    pub fn __truediv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rtruediv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__truediv__(py, other)
    }

    pub fn __floordiv__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.udiv(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
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
            &GLOBAL_CONTEXT.pow(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
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
            &GLOBAL_CONTEXT.urem(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rmod__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__mod__(py, other)
    }

    pub fn SDiv(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.sdiv(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn SMod(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.srem(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __and__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.and(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rand__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__and__(py, other)
    }

    pub fn __or__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.or(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __ror__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__or__(py, other)
    }

    pub fn __xor__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.xor(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rxor__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__xor__(py, other)
    }

    pub fn __lshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.shl(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rlshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__lshift__(py, other)
    }

    pub fn __rshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.ashr(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __rrshift__(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        self.__rshift__(py, other)
    }

    pub fn LShR(&self, py: Python, other: CoerceBV) -> Result<Py<BV>, ClaripyError> {
        BV::new(
            py,
            &GLOBAL_CONTEXT.lshr(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
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
            &GLOBAL_CONTEXT.eq_(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __ne__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.neq(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __lt__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __le__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __gt__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn __ge__(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn ULT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ult(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn ULE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ule(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn UGT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.ugt(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn UGE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.uge(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn SLT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.slt(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn SLE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sle(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn SGT(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sgt(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn SGE(&self, py: Python, other: CoerceBV) -> Result<Py<Bool>, ClaripyError> {
        Bool::new(
            py,
            &GLOBAL_CONTEXT.sge(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
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
            &GLOBAL_CONTEXT.concat(&self.inner, &<CoerceBV as Into<BitVecAst>>::into(other))?,
        )
    }

    pub fn zero_ext(&self, py: Python, amount: u32) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &GLOBAL_CONTEXT.zero_ext(&self.inner, amount)?)
    }

    pub fn sign_ext(&self, py: Python, amount: u32) -> Result<Py<BV>, ClaripyError> {
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
    ($name:ident, $context_method:ident, $return_type:ty, $lhs:ty, $rhs:ty) => {
        #[pyfunction]
        pub fn $name(
            py: Python,
            lhs: Bound<$lhs>,
            rhs: Bound<$rhs>,
        ) -> Result<Py<$return_type>, ClaripyError> {
            <$return_type>::new(
                py,
                &GLOBAL_CONTEXT.$context_method(&lhs.get().inner, &rhs.get().inner)?,
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
binop!(ShL, shl, BV, BV, BV);
binop!(LShR, lshr, BV, BV, BV);
binop!(AShR, ashr, BV, BV, BV);
binop!(RotateLeft, rotate_left, BV, BV, BV);
binop!(RotateRight, rotate_right, BV, BV, BV);
binop!(Concat, concat, BV, BV, BV);

#[pyfunction]
pub fn Extract(py: Python, base: Bound<BV>, start: u32, end: u32) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.extract(&base.get().inner, start, end)?)
}

#[pyfunction]
pub fn ZeroExt(py: Python, base: Bound<BV>, amount: u32) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.zero_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn SignExt(py: Python, base: Bound<BV>, amount: u32) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.sign_ext(&base.get().inner, amount)?)
}

#[pyfunction]
pub fn Reverse(py: Python, base: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
    BV::new(py, &GLOBAL_CONTEXT.reverse(&base.get().inner)?)
}

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
pub fn If(
    py: Python,
    cond: Bound<Bool>,
    then_: Bound<BV>,
    else_: Bound<BV>,
) -> Result<Py<BV>, ClaripyError> {
    BV::new(
        py,
        &GLOBAL_CONTEXT.if_(&cond.get().inner, &then_.get().inner, &else_.get().inner)?,
    )
}

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
        If,
    );

    Ok(())
}
