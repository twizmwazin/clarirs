use ast::fp::{PyFSort, PyRM};

use crate::prelude::*;

pub trait ExtractPyArgs {
    fn extract_py_args<'py>(&self, py: Python<'py>)
    -> Result<Vec<Bound<'py, PyAny>>, ClaripyError>;
}

impl ExtractPyArgs for BoolAst<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(match self.op() {
            BooleanOp::BoolS(name) => vec![name.into_bound_py_any(py)?],
            BooleanOp::BoolV(val) => vec![val.into_bound_py_any(py)?],
            BooleanOp::Not(expr) => vec![Bool::new(py, expr)?.into_any()],
            BooleanOp::And(lhs, rhs)
            | BooleanOp::Or(lhs, rhs)
            | BooleanOp::Xor(lhs, rhs)
            | BooleanOp::BoolEq(lhs, rhs)
            | BooleanOp::BoolNeq(lhs, rhs) => vec![
                Bool::new(py, lhs)?.into_any(),
                Bool::new(py, rhs)?.into_any(),
            ],
            BooleanOp::Eq(lhs, rhs)
            | BooleanOp::Neq(lhs, rhs)
            | BooleanOp::ULT(lhs, rhs)
            | BooleanOp::ULE(lhs, rhs)
            | BooleanOp::UGT(lhs, rhs)
            | BooleanOp::UGE(lhs, rhs)
            | BooleanOp::SLT(lhs, rhs)
            | BooleanOp::SLE(lhs, rhs)
            | BooleanOp::SGT(lhs, rhs)
            | BooleanOp::SGE(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            BooleanOp::FpEq(lhs, rhs)
            | BooleanOp::FpNeq(lhs, rhs)
            | BooleanOp::FpLt(lhs, rhs)
            | BooleanOp::FpLeq(lhs, rhs)
            | BooleanOp::FpGt(lhs, rhs)
            | BooleanOp::FpGeq(lhs, rhs) => {
                vec![FP::new(py, lhs)?.into_any(), FP::new(py, rhs)?.into_any()]
            }
            BooleanOp::FpIsNan(expr) | BooleanOp::FpIsInf(expr) => {
                vec![FP::new(py, expr)?.into_any()]
            }
            BooleanOp::StrContains(lhs, rhs)
            | BooleanOp::StrPrefixOf(lhs, rhs)
            | BooleanOp::StrSuffixOf(lhs, rhs)
            | BooleanOp::StrEq(lhs, rhs)
            | BooleanOp::StrNeq(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            BooleanOp::StrIsDigit(expr) => vec![PyAstString::new(py, expr)?.into_any()],
            BooleanOp::If(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                Bool::new(py, then_)?.into_any(),
                Bool::new(py, else_)?.into_any(),
            ],
        })
    }
}

impl ExtractPyArgs for BitVecAst<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(match self.op() {
            BitVecOp::BVS(name, size) => {
                vec![name.into_bound_py_any(py)?, size.into_bound_py_any(py)?]
            }
            BitVecOp::BVV(bit_vec) => vec![
                bit_vec.to_biguint().into_bound_py_any(py)?,
                bit_vec.len().into_bound_py_any(py)?,
            ],
            BitVecOp::Not(expr) | BitVecOp::Neg(expr) => {
                vec![BV::new(py, expr)?.into_any()]
            }
            BitVecOp::And(lhs, rhs)
            | BitVecOp::Or(lhs, rhs)
            | BitVecOp::Xor(lhs, rhs)
            | BitVecOp::Add(lhs, rhs)
            | BitVecOp::Sub(lhs, rhs)
            | BitVecOp::Mul(lhs, rhs)
            | BitVecOp::UDiv(lhs, rhs)
            | BitVecOp::SDiv(lhs, rhs)
            | BitVecOp::URem(lhs, rhs)
            | BitVecOp::SRem(lhs, rhs)
            | BitVecOp::ShL(lhs, rhs)
            | BitVecOp::LShR(lhs, rhs)
            | BitVecOp::AShR(lhs, rhs)
            | BitVecOp::RotateLeft(lhs, rhs)
            | BitVecOp::RotateRight(lhs, rhs)
            | BitVecOp::Concat(lhs, rhs)
            | BitVecOp::Union(lhs, rhs)
            | BitVecOp::Intersection(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            BitVecOp::ZeroExt(expr, amount) | BitVecOp::SignExt(expr, amount) => {
                vec![BV::new(py, expr)?.into_any(), amount.into_bound_py_any(py)?]
            }
            BitVecOp::Extract(expr, end, start) => vec![
                end.into_bound_py_any(py)?,
                start.into_bound_py_any(py)?,
                BV::new(py, expr)?.into_any(),
            ],
            BitVecOp::Reverse(expr) => vec![BV::new(py, expr)?.into_any()],
            BitVecOp::FpToIEEEBV(expr) => vec![FP::new(py, expr)?.into_any()],
            BitVecOp::FpToUBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            BitVecOp::FpToSBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            BitVecOp::StrLen(expr) | BitVecOp::StrToBV(expr) => {
                vec![PyAstString::new(py, expr)?.into_any()]
            }
            BitVecOp::StrIndexOf(base, search, offset) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, search)?.into_any(),
                BV::new(py, offset)?.into_any(),
            ],
            BitVecOp::If(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                BV::new(py, then_)?.into_any(),
                BV::new(py, else_)?.into_any(),
            ],
            BitVecOp::SI(size, bits, lower_bound, upper_bound) => {
                vec![
                    size.into_bound_py_any(py)?,
                    bits.into_bound_py_any(py)?,
                    lower_bound.into_bound_py_any(py)?,
                    upper_bound.into_bound_py_any(py)?,
                ]
            }
        })
    }
}

impl ExtractPyArgs for FloatAst<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(match self.op() {
            FloatOp::FPS(name, fsort) => vec![
                name.into_bound_py_any(py)?,
                Bound::new(py, PyFSort::from(fsort))?.into_any(),
            ],
            FloatOp::FPV(value) => vec![value.to_f64().into_bound_py_any(py)?],
            FloatOp::FpNeg(expr) | FloatOp::FpAbs(expr) => vec![FP::new(py, expr)?.into_any()],
            FloatOp::FpAdd(lhs, rhs, rm)
            | FloatOp::FpSub(lhs, rhs, rm)
            | FloatOp::FpMul(lhs, rhs, rm)
            | FloatOp::FpDiv(lhs, rhs, rm) => vec![
                FP::new(py, lhs)?.into_any(),
                FP::new(py, rhs)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            FloatOp::FpSqrt(expr, rm) => vec![
                FP::new(py, expr)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            FloatOp::FpToFp(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            FloatOp::BvToFp(arc, _)
            | FloatOp::BvToFpSigned(arc, _, _)
            | FloatOp::BvToFpUnsigned(arc, _, _) => vec![BV::new(py, arc)?.into_any()],
            FloatOp::If(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                FP::new(py, then_)?.into_any(),
                FP::new(py, else_)?.into_any(),
            ],
        })
    }
}

impl ExtractPyArgs for StringAst<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(match self.op() {
            StringOp::StringS(name) => vec![name.into_bound_py_any(py)?],
            StringOp::StringV(value) => vec![value.into_bound_py_any(py)?],
            StringOp::StrConcat(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            StringOp::StrSubstr(base, start, end) => vec![
                PyAstString::new(py, base)?.into_any(),
                BV::new(py, start)?.into_any(),
                BV::new(py, end)?.into_any(),
            ],
            StringOp::StrReplace(base, old, new) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, old)?.into_any(),
                PyAstString::new(py, new)?.into_any(),
            ],
            StringOp::BVToStr(expr) => vec![BV::new(py, expr)?.into_any()],
            StringOp::If(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                PyAstString::new(py, then_)?.into_any(),
                PyAstString::new(py, else_)?.into_any(),
            ],
        })
    }
}

impl ExtractPyArgs for DynAst<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        match self {
            DynAst::Boolean(expr) => expr.extract_py_args(py),
            DynAst::BitVec(expr) => expr.extract_py_args(py),
            DynAst::Float(expr) => expr.extract_py_args(py),
            DynAst::String(expr) => expr.extract_py_args(py),
        }
    }
}
