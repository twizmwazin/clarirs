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
            // Boolean
            AstOp::BoolS(name) => vec![name.as_str().into_bound_py_any(py)?],
            AstOp::BoolV(val) => vec![val.into_bound_py_any(py)?],

            // Cross-sort ops
            AstOp::Not(expr) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    vec![Bool::new(py, expr)?.into_any()]
                } else {
                    vec![BV::new(py, expr)?.into_any()]
                }
            }
            AstOp::And(args) | AstOp::Or(args) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    args.iter()
                        .map(|a| Bool::new(py, a).map(|b| b.into_any()))
                        .collect::<Result<Vec<_>, _>>()?
                } else {
                    args.iter()
                        .map(|a| BV::new(py, a).map(|b| b.into_any()))
                        .collect::<Result<Vec<_>, _>>()?
                }
            }
            AstOp::Xor(args) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    args.iter()
                        .map(|a| Bool::new(py, a).map(|b| b.into_any()))
                        .collect::<Result<Vec<_>, _>>()?
                } else {
                    args.iter()
                        .map(|a| BV::new(py, a).map(|b| b.into_any()))
                        .collect::<Result<Vec<_>, _>>()?
                }
            }
            AstOp::Eq(lhs, rhs) | AstOp::Neq(lhs, rhs) => {
                // Determine the type of the children
                let child_theory = lhs.op().base_theories();
                if child_theory == Theories::BOOLEAN {
                    vec![
                        Bool::new(py, lhs)?.into_any(),
                        Bool::new(py, rhs)?.into_any(),
                    ]
                } else if child_theory == Theories::BITVEC {
                    vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
                } else if child_theory == Theories::FLOAT {
                    vec![FP::new(py, lhs)?.into_any(), FP::new(py, rhs)?.into_any()]
                } else {
                    vec![
                        PyAstString::new(py, lhs)?.into_any(),
                        PyAstString::new(py, rhs)?.into_any(),
                    ]
                }
            }
            AstOp::If(cond, then_, else_) => {
                let result_theory = then_.op().base_theories();
                if result_theory == Theories::BOOLEAN {
                    vec![
                        Bool::new(py, cond)?.into_any(),
                        Bool::new(py, then_)?.into_any(),
                        Bool::new(py, else_)?.into_any(),
                    ]
                } else if result_theory == Theories::BITVEC {
                    vec![
                        Bool::new(py, cond)?.into_any(),
                        BV::new(py, then_)?.into_any(),
                        BV::new(py, else_)?.into_any(),
                    ]
                } else if result_theory == Theories::FLOAT {
                    vec![
                        Bool::new(py, cond)?.into_any(),
                        FP::new(py, then_)?.into_any(),
                        FP::new(py, else_)?.into_any(),
                    ]
                } else {
                    vec![
                        Bool::new(py, cond)?.into_any(),
                        PyAstString::new(py, then_)?.into_any(),
                        PyAstString::new(py, else_)?.into_any(),
                    ]
                }
            }

            // BV comparisons (result is Bool but children are BV)
            AstOp::ULT(lhs, rhs)
            | AstOp::ULE(lhs, rhs)
            | AstOp::UGT(lhs, rhs)
            | AstOp::UGE(lhs, rhs)
            | AstOp::SLT(lhs, rhs)
            | AstOp::SLE(lhs, rhs)
            | AstOp::SGT(lhs, rhs)
            | AstOp::SGE(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }

            // FP comparisons (result is Bool but children are FP)
            AstOp::FpLt(lhs, rhs)
            | AstOp::FpLeq(lhs, rhs)
            | AstOp::FpGt(lhs, rhs)
            | AstOp::FpGeq(lhs, rhs) => {
                vec![FP::new(py, lhs)?.into_any(), FP::new(py, rhs)?.into_any()]
            }
            AstOp::FpIsNan(expr) | AstOp::FpIsInf(expr) => {
                vec![FP::new(py, expr)?.into_any()]
            }

            // String comparisons (result is Bool but children are String)
            AstOp::StrContains(lhs, rhs)
            | AstOp::StrPrefixOf(lhs, rhs)
            | AstOp::StrSuffixOf(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            AstOp::StrIsDigit(expr) => vec![PyAstString::new(py, expr)?.into_any()],

            // BV
            AstOp::BVS(name, size) => {
                vec![
                    name.as_str().into_bound_py_any(py)?,
                    size.into_bound_py_any(py)?,
                ]
            }
            AstOp::BVV(bit_vec) => vec![
                bit_vec.to_biguint().into_bound_py_any(py)?,
                bit_vec.len().into_bound_py_any(py)?,
            ],
            AstOp::Neg(expr) => {
                vec![BV::new(py, expr)?.into_any()]
            }
            AstOp::Add(args) | AstOp::Mul(args) => args
                .iter()
                .map(|arg| BV::new(py, arg).map(|b| b.into_any()))
                .collect::<Result<Vec<_>, _>>()?,
            AstOp::Sub(lhs, rhs)
            | AstOp::UDiv(lhs, rhs)
            | AstOp::SDiv(lhs, rhs)
            | AstOp::URem(lhs, rhs)
            | AstOp::SRem(lhs, rhs)
            | AstOp::ShL(lhs, rhs)
            | AstOp::LShR(lhs, rhs)
            | AstOp::AShR(lhs, rhs)
            | AstOp::RotateLeft(lhs, rhs)
            | AstOp::RotateRight(lhs, rhs)
            | AstOp::Union(lhs, rhs)
            | AstOp::Intersection(lhs, rhs)
            | AstOp::Widen(lhs, rhs) => {
                vec![BV::new(py, lhs)?.into_any(), BV::new(py, rhs)?.into_any()]
            }
            AstOp::Concat(args) => args
                .iter()
                .map(|arg| BV::new(py, arg).map(|b| b.into_any()))
                .collect::<Result<Vec<_>, _>>()?,
            AstOp::ZeroExt(expr, amount) | AstOp::SignExt(expr, amount) => {
                vec![amount.into_bound_py_any(py)?, BV::new(py, expr)?.into_any()]
            }
            AstOp::Extract(expr, end, start) => vec![
                end.into_bound_py_any(py)?,
                start.into_bound_py_any(py)?,
                BV::new(py, expr)?.into_any(),
            ],
            AstOp::ByteReverse(expr) => vec![BV::new(py, expr)?.into_any()],
            AstOp::FpToIEEEBV(expr) => vec![FP::new(py, expr)?.into_any()],
            AstOp::FpToUBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            AstOp::FpToSBV(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            AstOp::StrLen(expr) | AstOp::StrToBV(expr) => {
                vec![PyAstString::new(py, expr)?.into_any()]
            }
            AstOp::StrIndexOf(base, search, offset) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, search)?.into_any(),
                BV::new(py, offset)?.into_any(),
            ],

            // Float
            AstOp::FPS(name, fsort) => vec![
                name.as_str().into_bound_py_any(py)?,
                Bound::new(py, PyFSort::from(fsort))?.into_any(),
            ],
            AstOp::FPV(value) => vec![value.to_f64().into_bound_py_any(py)?],
            AstOp::FpFP(sign, exp, sig) => vec![
                BV::new(py, sign)?.into_any(),
                BV::new(py, exp)?.into_any(),
                BV::new(py, sig)?.into_any(),
            ],
            AstOp::FpNeg(expr) | AstOp::FpAbs(expr) => vec![FP::new(py, expr)?.into_any()],
            AstOp::FpAdd(lhs, rhs, rm)
            | AstOp::FpSub(lhs, rhs, rm)
            | AstOp::FpMul(lhs, rhs, rm)
            | AstOp::FpDiv(lhs, rhs, rm) => vec![
                FP::new(py, lhs)?.into_any(),
                FP::new(py, rhs)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            AstOp::FpSqrt(expr, rm) => vec![
                FP::new(py, expr)?.into_any(),
                Bound::new(py, PyRM::from(rm))?.into_any(),
            ],
            AstOp::FpToFp(arc, _, _) => vec![FP::new(py, arc)?.into_any()],
            AstOp::BvToFp(arc, _)
            | AstOp::BvToFpSigned(arc, _, _)
            | AstOp::BvToFpUnsigned(arc, _, _) => vec![BV::new(py, arc)?.into_any()],

            // String
            AstOp::StringS(name) => vec![name.as_str().into_bound_py_any(py)?],
            AstOp::StringV(value) => vec![value.into_bound_py_any(py)?],
            AstOp::StrConcat(lhs, rhs) => vec![
                PyAstString::new(py, lhs)?.into_any(),
                PyAstString::new(py, rhs)?.into_any(),
            ],
            AstOp::StrSubstr(base, start, end) => vec![
                PyAstString::new(py, base)?.into_any(),
                BV::new(py, start)?.into_any(),
                BV::new(py, end)?.into_any(),
            ],
            AstOp::StrReplace(base, old, new) => vec![
                PyAstString::new(py, base)?.into_any(),
                PyAstString::new(py, old)?.into_any(),
                PyAstString::new(py, new)?.into_any(),
            ],
            AstOp::BVToStr(expr) => vec![BV::new(py, expr)?.into_any()],
        })
    }
}
