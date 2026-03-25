use ast::fp::{PyFSort, PyRM};

use crate::prelude::*;

pub trait ExtractPyArgs {
    fn extract_py_args<'py>(&self, py: Python<'py>)
    -> Result<Vec<Bound<'py, PyAny>>, ClaripyError>;
}

impl ExtractPyArgs for AstRef<'static> {
    fn extract_py_args<'py>(
        &self,
        py: Python<'py>,
    ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
        Ok(match self.op() {
            // Bool ops
            Op::BoolS(name) => vec![name.as_str().into_bound_py_any(py)?],
            Op::BoolV(val) => vec![val.into_bound_py_any(py)?],
            Op::Not(expr) => vec![Bool::new(py, expr)?.into_any()],
            Op::And(args) | Op::Or(args) => args
                .iter()
                .map(|a| Bool::new(py, a).map(|b| b.into_any()))
                .collect::<Result<Vec<_>, _>>()?,
            Op::Xor(lhs, rhs)
            | Op::BoolEq(lhs, rhs)
            | Op::BoolNeq(lhs, rhs) => vec![
                Bool::new(py, lhs)?.into_any(),
                Bool::new(py, rhs)?.into_any(),
            ],
            Op::Eq(lhs, rhs)
            | Op::Neq(lhs, rhs)
            | Op::ULT(lhs, rhs)
            | Op::ULE(lhs, rhs)
            | Op::UGT(lhs, rhs)
            | Op::UGE(lhs, rhs)
            | Op::SLT(lhs, rhs)
            | Op::SLE(lhs, rhs)
            | Op::SGT(lhs, rhs)
            | Op::SGE(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            Op::FpEq(lhs, rhs)
            | Op::FpNeq(lhs, rhs)
            | Op::FpLt(lhs, rhs)
            | Op::FpLeq(lhs, rhs)
            | Op::FpGt(lhs, rhs)
            | Op::FpGeq(lhs, rhs) => {
                vec![FP::new(py, lhs)?.into_any(), FP::new(py, rhs)?.into_any()]
            }
            Op::FpIsNan(expr) | Op::FpIsInf(expr) => {
                vec![FP::new(py, expr)?.into_any()]
            }
            Op::StrContains(lhs, rhs)
            | Op::StrPrefixOf(lhs, rhs)
            | Op::StrSuffixOf(lhs, rhs)
            | Op::StrEq(lhs, rhs)
            | Op::StrNeq(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            Op::StrIsDigit(expr) => vec![PyAstString::new(py, expr)?.into_any()],
            Op::ITE(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                Bool::new(py, then_)?.into_any(),
                Bool::new(py, else_)?.into_any(),
            ],

            // BitVec ops
            Op::BVS(name, size) => {
                vec![
                    name.as_str().into_bound_py_any(py)?,
                    size.into_bound_py_any(py)?,
                ]
            }
            Op::BVV(bit_vec) => vec![
                bit_vec.to_biguint().into_bound_py_any(py)?,
                bit_vec.len().into_bound_py_any(py)?,
            ],
            Op::BVNot(expr) | Op::Neg(expr) => {
                vec![BV::new(py, expr)?.into_any()]
            }
            Op::BVAnd(args)
            | Op::BVOr(args)
            | Op::BVXor(args)
            | Op::Add(args)
            | Op::Mul(args) => args
                .iter()
                .map(|arg| BV::new(py, arg).map(|b| b.into_any()))
                .collect::<Result<Vec<_>, _>>()?,
            Op::Sub(lhs, rhs)
            | Op::UDiv(lhs, rhs)
            | Op::SDiv(lhs, rhs)
            | Op::URem(lhs, rhs)
            | Op::SRem(lhs, rhs)
            | Op::ShL(lhs, rhs)
            | Op::LShR(lhs, rhs)
            | Op::AShR(lhs, rhs)
            | Op::RotateLeft(lhs, rhs)
            | Op::RotateRight(lhs, rhs)
            | Op::Union(lhs, rhs)
            | Op::Intersection(lhs, rhs)
            | Op::Widen(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            Op::Concat(args) => args
                .iter()
                .map(|arg| BV::new(py, arg).map(|b| b.into_any()))
                .collect::<Result<Vec<_>, _>>()?,
            Op::ZeroExt(expr, amount) | Op::SignExt(expr, amount) => {
                vec![amount.into_bound_py_any(py)?, BV::new(py, expr)?.into_any()]
            }
            Op::Extract(expr, end, start) => vec![
                end.into_bound_py_any(py)?,
                start.into_bound_py_any(py)?,
                BV::new(py, expr)?.into_any(),
            ],
            Op::ByteReverse(expr) => vec![BV::new(py, expr)?.into_any()],
            Op::FpToIEEEBV(expr) => vec![FP::new(py, expr)?.into_any()],
            Op::FpToUBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            Op::FpToSBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            Op::StrLen(expr) | Op::StrToBV(expr) => {
                vec![PyAstString::new(py, expr)?.into_any()]
            }
            Op::StrIndexOf(base, search, offset) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, search)?.into_any(),
                BV::new(py, offset)?.into_any(),
            ],
            Op::ITE(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                BV::new(py, then_)?.into_any(),
                BV::new(py, else_)?.into_any(),
            ],

            // Float ops
            Op::FPS(name, fsort) => vec![
                name.as_str().into_bound_py_any(py)?,
                Bound::new(py, PyFSort::from(fsort))?.into_any(),
            ],
            Op::FPV(value) => vec![value.to_f64().into_bound_py_any(py)?],
            Op::FpFP(sign, exp, sig) => vec![
                BV::new(py, sign)?.into_any(),
                BV::new(py, exp)?.into_any(),
                BV::new(py, sig)?.into_any(),
            ],
            Op::FpNeg(expr) | Op::FpAbs(expr) => vec![FP::new(py, expr)?.into_any()],
            Op::FpAdd(lhs, rhs, rm)
            | Op::FpSub(lhs, rhs, rm)
            | Op::FpMul(lhs, rhs, rm)
            | Op::FpDiv(lhs, rhs, rm) => vec![
                FP::new(py, lhs)?.into_any(),
                FP::new(py, rhs)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            Op::FpSqrt(expr, rm) => vec![
                FP::new(py, expr)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            Op::FpToFp(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            Op::BvToFp(arc, _)
            | Op::BvToFpSigned(arc, _, _)
            | Op::BvToFpUnsigned(arc, _, _) => vec![BV::new(py, arc)?.into_any()],
            Op::ITE(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                FP::new(py, then_)?.into_any(),
                FP::new(py, else_)?.into_any(),
            ],

            // String ops
            Op::StringS(name) => vec![name.as_str().into_bound_py_any(py)?],
            Op::StringV(value) => vec![value.into_bound_py_any(py)?],
            Op::StrConcat(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            Op::StrSubstr(base, start, end) => vec![
                PyAstString::new(py, base)?.into_any(),
                BV::new(py, start)?.into_any(),
                BV::new(py, end)?.into_any(),
            ],
            Op::StrReplace(base, old, new) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, old)?.into_any(),
                PyAstString::new(py, new)?.into_any(),
            ],
            Op::BVToStr(expr) => vec![BV::new(py, expr)?.into_any()],
            Op::ITE(cond, then_, else_) => vec![
                Bool::new(py, cond)?.into_any(),
                PyAstString::new(py, then_)?.into_any(),
                PyAstString::new(py, else_)?.into_any(),
            ],
        })
    }
}
