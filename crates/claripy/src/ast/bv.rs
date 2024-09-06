#![allow(non_snake_case)]

use num_bigint::BigUint;

use super::shared_ops;
use super::{bits::Bits, bool::Bool};
use crate::prelude::*;

#[pyclass(extends=Bits, subclass, frozen, weakref, module="claripy.ast.bv")]
pub struct BV {}

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

pyop!(m, BVS, bvs, BV, name: String, size: u32);
pyop!(m, BVV, bvv_from_biguint_with_size, BV, value: BigUint, size: u32);

pyop!(m, Add, add, BV, BV, BV);
pyop!(m, Sub, sub, BV, BV, BV);
pyop!(m, Mul, mul, BV, BV, BV);
pyop!(m, UDiv, udiv, BV, BV, BV);
pyop!(m, SDiv, sdiv, BV, BV, BV);
pyop!(m, UMod, urem, BV, BV, BV);
pyop!(m, SMod, srem, BV, BV, BV);
pyop!(m, Pow, pow, BV, BV, BV);
pyop!(m, LShL, lshl, BV, BV, BV);
pyop!(m, LShR, lshr, BV, BV, BV);
pyop!(m, AShR, ashr, BV, BV, BV);
pyop!(m, AShL, ashl, BV, BV, BV);
pyop!(m, Concat, concat, BV, BV, BV);
pyop!(m, Extract, extract, BV, BV, start: u32, end: u32);

pyop!(m, ULT, ult, Bool, BV, BV);
pyop!(m, ULE, ule, Bool, BV, BV);
pyop!(m, UGT, ugt, Bool, BV, BV);
pyop!(m, UGE, uge, Bool, BV, BV);
pyop!(m, SLT, slt, Bool, BV, BV);
pyop!(m, SLE, sle, Bool, BV, BV);
pyop!(m, SGT, sgt, Bool, BV, BV);
pyop!(m, SGE, sge, Bool, BV, BV);

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
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
