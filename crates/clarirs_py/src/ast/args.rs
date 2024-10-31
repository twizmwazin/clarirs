use ast::fp::{PyFSort, PyRM};

use crate::prelude::*;

pub trait ExtractPyArgs {
    fn extract_py_args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError>;
}

impl ExtractPyArgs for BooleanOp<'static> {
    fn extract_py_args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        Ok(match self {
            BooleanOp::BoolS(name) => vec![name.to_object(py)],
            BooleanOp::BoolV(val) => vec![val.to_object(py)],
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
            BooleanOp::Annotated(inner, _) => inner.op().extract_py_args(py)?,
        })
    }
}

impl ExtractPyArgs for BitVecOp<'static> {
    fn extract_py_args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        Ok(match self {
            BitVecOp::BVS(name, size) => vec![name.to_object(py), size.to_object(py)],
            BitVecOp::BVV(bit_vec) => vec![bit_vec.as_biguint().to_object(py)],
            BitVecOp::SI(_, bit_vec, bit_vec1, bit_vec2, _) => todo!(),
            BitVecOp::Not(expr) => vec![BV::new(py, expr)?.into_any()],
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
            | BitVecOp::Pow(lhs, rhs)
            | BitVecOp::ShL(lhs, rhs)
            | BitVecOp::LShR(lhs, rhs)
            | BitVecOp::AShR(lhs, rhs)
            | BitVecOp::RotateLeft(lhs, rhs)
            | BitVecOp::RotateRight(lhs, rhs)
            | BitVecOp::Concat(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            BitVecOp::ZeroExt(expr, amount) | BitVecOp::SignExt(expr, amount) => {
                vec![BV::new(py, expr)?.into_any(), amount.to_object(py)]
            }
            BitVecOp::Extract(expr, end, start) => vec![
                BV::new(py, expr)?.into_any(),
                end.to_object(py),
                start.to_object(py),
            ],
            BitVecOp::Reverse(expr) => vec![BV::new(py, expr)?.into_any()],
            BitVecOp::FpToIEEEBV(expr) => vec![FP::new(py, expr)?.into_any()],
            BitVecOp::FpToUBV(arc, _, fprm) => todo!(),
            BitVecOp::FpToSBV(arc, _, fprm) => todo!(),
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
            BitVecOp::Annotated(inner, _) => inner.op().extract_py_args(py)?,
        })
    }
}

impl ExtractPyArgs for FloatOp<'static> {
    fn extract_py_args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        Ok(match self {
            FloatOp::FPS(name, fsort) => vec![
                name.to_object(py),
                Py::new(py, PyFSort::from(fsort))?.into_any(),
            ],
            FloatOp::FPV(value) => vec![value.as_f64().to_object(py)],
            FloatOp::FpNeg(expr, rm) | FloatOp::FpAbs(expr, rm) => vec![
                FP::new(py, expr)?.into_any(),
                Py::new(py, PyRM::from(rm))?.into_any(),
            ],
            FloatOp::FpAdd(lhs, rhs, rm)
            | FloatOp::FpSub(lhs, rhs, rm)
            | FloatOp::FpMul(lhs, rhs, rm)
            | FloatOp::FpDiv(lhs, rhs, rm) => vec![
                FP::new(py, lhs)?.into_any(),
                FP::new(py, rhs)?.into_any(),
                Py::new(py, PyRM::from(rm))?.into_any(),
            ],
            FloatOp::FpSqrt(expr, rm) => vec![
                FP::new(py, expr)?.into_any(),
                Py::new(py, PyRM::from(rm))?.into_any(),
            ],
            FloatOp::FpToFp(arc, fsort, fprm) => todo!(),
            FloatOp::BvToFpUnsigned(arc, fsort, fprm) => todo!(),
            FloatOp::If(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                FP::new(py, then_)?.into_any(),
                FP::new(py, else_)?.into_any(),
            ],
            FloatOp::Annotated(inner, _) => inner.op().extract_py_args(py)?,
        })
    }
}

impl ExtractPyArgs for StringOp<'static> {
    fn extract_py_args(&self, py: Python) -> Result<Vec<PyObject>, ClaripyError> {
        Ok(match self {
            StringOp::StringS(name) => vec![name.to_object(py)],
            StringOp::StringV(value) => vec![value.to_object(py)],
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
            StringOp::Annotated(inner, _) => inner.op().extract_py_args(py)?,
        })
    }
}
