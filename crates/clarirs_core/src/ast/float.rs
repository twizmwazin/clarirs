use std::collections::BTreeSet;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum FloatOp<'c> {
    FPS(InternedString, FSort),
    FPV(Float),
    FpNeg(FloatAst<'c>),
    FpAbs(FloatAst<'c>),
    FpAdd(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSub(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpMul(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpDiv(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSqrt(FloatAst<'c>, FPRM),
    /// Transform a float to another float of a different size, preserving the value.
    FpToFp(FloatAst<'c>, FSort, FPRM),
    /// Construct a float from sign, exponent, and significand bitvectors
    FpFP(BitVecAst<'c>, BitVecAst<'c>, BitVecAst<'c>),
    /// Transform an IEEE 754 bitvector to a float
    BvToFp(BitVecAst<'c>, FSort),
    /// Transform a signed 2's complement bitvector to a float
    BvToFpSigned(BitVecAst<'c>, FSort, FPRM),
    /// Transform an unsigned 2's complement bitvector to a float
    BvToFpUnsigned(BitVecAst<'c>, FSort, FPRM),
    ITE(AstRef<'c, BooleanOp<'c>>, FloatAst<'c>, FloatAst<'c>),
}

pub type FloatAst<'c> = AstRef<'c, FloatOp<'c>>;

pub struct FloatOpChildIter<'a, 'c> {
    op: &'a FloatOp<'c>,
    index: u8,
}

impl<'c> FloatOp<'c> {
    pub fn child_iter(&self) -> FloatOpChildIter<'_, 'c> {
        FloatOpChildIter { op: self, index: 0 }
    }
}

impl<'a, 'c> Iterator for FloatOpChildIter<'a, 'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = match (self.op, self.index) {
            // 0 children
            (FloatOp::FPS(..), _) | (FloatOp::FPV(_), _) => None,

            // 1 child variants - index 0
            (FloatOp::FpNeg(a), 0)
            | (FloatOp::FpAbs(a), 0)
            | (FloatOp::FpSqrt(a, _), 0)
            | (FloatOp::FpToFp(a, _, _), 0) => Some(a.into()),

            (FloatOp::BvToFp(a, _), 0)
            | (FloatOp::BvToFpSigned(a, _, _), 0)
            | (FloatOp::BvToFpUnsigned(a, _, _), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (FloatOp::FpAdd(a, _, _), 0)
            | (FloatOp::FpSub(a, _, _), 0)
            | (FloatOp::FpMul(a, _, _), 0)
            | (FloatOp::FpDiv(a, _, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (FloatOp::FpAdd(_, b, _), 1)
            | (FloatOp::FpSub(_, b, _), 1)
            | (FloatOp::FpMul(_, b, _), 1)
            | (FloatOp::FpDiv(_, b, _), 1) => Some(b.into()),

            // 3 child variants - FpFP(sign, exp, sig)
            (FloatOp::FpFP(sign, _, _), 0) => Some(sign.into()),
            (FloatOp::FpFP(_, exp, _), 1) => Some(exp.into()),
            (FloatOp::FpFP(_, _, sig), 2) => Some(sig.into()),

            // 3 child variants - If(cond, then, else)
            (FloatOp::ITE(a, _, _), 0) => Some(a.into()),
            (FloatOp::ITE(_, b, _), 1) => Some(b.into()),
            (FloatOp::ITE(_, _, c), 2) => Some(c.into()),

            _ => None,
        };

        if result.is_some() {
            self.index += 1;
        }

        result
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len();
        (remaining, Some(remaining))
    }
}

impl<'a, 'c> ExactSizeIterator for FloatOpChildIter<'a, 'c> {
    fn len(&self) -> usize {
        let total: usize = match self.op {
            FloatOp::FPS(..) | FloatOp::FPV(_) => 0,

            FloatOp::FpNeg(_)
            | FloatOp::FpAbs(_)
            | FloatOp::FpSqrt(..)
            | FloatOp::FpToFp(..)
            | FloatOp::BvToFp(..)
            | FloatOp::BvToFpSigned(..)
            | FloatOp::BvToFpUnsigned(..) => 1,

            FloatOp::FpAdd(..) | FloatOp::FpSub(..) | FloatOp::FpMul(..) | FloatOp::FpDiv(..) => 2,

            FloatOp::FpFP(..) | FloatOp::ITE(..) => 3,
        };
        total.saturating_sub(self.index as usize)
    }
}

impl std::hash::Hash for FloatOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "float".hash(state);
        std::mem::discriminant(self).hash(state);
        match self {
            FloatOp::FPS(s, sort) => {
                s.hash(state);
                sort.hash(state);
            }
            FloatOp::FPV(f) => {
                f.hash(state);
            }
            FloatOp::FpNeg(a) => {
                a.hash(state);
            }
            FloatOp::FpAbs(a) => {
                a.hash(state);
            }
            FloatOp::FpAdd(a, b, rm) => {
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpSub(a, b, rm) => {
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpMul(a, b, rm) => {
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpDiv(a, b, rm) => {
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpSqrt(a, rm) => {
                a.hash(state);
                rm.hash(state);
            }
            FloatOp::FpToFp(a, sort, rm) => {
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::FpFP(sign, exp, sig) => {
                sign.hash(state);
                exp.hash(state);
                sig.hash(state);
            }
            FloatOp::BvToFp(a, sort) => {
                a.hash(state);
                sort.hash(state);
            }
            FloatOp::BvToFpSigned(a, sort, rm) => {
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::ITE(a, b, c) => {
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for FloatOp<'c> {
    type ChildIter<'a>
        = FloatOpChildIter<'a, 'c>
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
        FloatOp::child_iter(self)
    }

    fn variables(&self) -> BTreeSet<InternedString> {
        if let FloatOp::FPS(s, _) = self {
            let mut set = BTreeSet::new();
            set.insert(s.clone());
            set
        } else {
            let mut set = BTreeSet::new();
            for child in self.child_iter() {
                set.extend(child.variables().into_iter());
            }
            set
        }
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        self.size() == other.size()
    }

    fn base_theories(&self) -> Theories {
        Theories::FLOAT
    }
}

pub trait FloatExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> FloatExt<'c> for FloatOp<'c> {
    fn size(&self) -> u32 {
        match self {
            FloatOp::FPS(_, sort) => sort.size(),
            FloatOp::FPV(value) => value.fsort().size(),
            FloatOp::FpNeg(a)
            | FloatOp::FpAbs(a)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpAdd(a, _, _)
            | FloatOp::FpSub(a, _, _)
            | FloatOp::FpMul(a, _, _)
            | FloatOp::FpDiv(a, _, _)
            | FloatOp::ITE(_, a, _) => a.size(),
            FloatOp::FpToFp(_, sort, _)
            | FloatOp::BvToFp(_, sort)
            | FloatOp::BvToFpSigned(_, sort, _)
            | FloatOp::BvToFpUnsigned(_, sort, _) => sort.size(),
            FloatOp::FpFP(sign, exp, sig) => {
                use crate::ast::bitvec::BitVecOpExt;
                sign.op().size() + exp.op().size() + sig.op().size()
            }
        }
    }
}

impl<'c> FloatExt<'c> for FloatAst<'c> {
    fn size(&self) -> u32 {
        self.op().size()
    }
}

pub trait FloatOpExt<'c> {
    fn sort(&self) -> FSort;
}

impl<'c> FloatOpExt<'c> for FloatOp<'c> {
    fn sort(&self) -> FSort {
        match self {
            FloatOp::FPS(_, sort) => *sort,
            FloatOp::FPV(value) => value.fsort(),
            FloatOp::FpNeg(a)
            | FloatOp::FpAbs(a)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpAdd(a, _, _)
            | FloatOp::FpSub(a, _, _)
            | FloatOp::FpMul(a, _, _)
            | FloatOp::FpDiv(a, _, _)
            | FloatOp::ITE(_, a, _) => a.sort(),
            FloatOp::FpToFp(_, sort, _)
            | FloatOp::BvToFp(_, sort)
            | FloatOp::BvToFpSigned(_, sort, _)
            | FloatOp::BvToFpUnsigned(_, sort, _) => *sort,
            FloatOp::FpFP(_sign, exp, sig) => {
                use crate::ast::bitvec::BitVecOpExt;
                // The significand includes the implicit bit, mantissa doesn't
                FSort::new(exp.op().size(), sig.op().size().saturating_sub(1))
            }
        }
    }
}

impl<'c> FloatOpExt<'c> for FloatAst<'c> {
    fn sort(&self) -> FSort {
        self.op().sort()
    }
}
