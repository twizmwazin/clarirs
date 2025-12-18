use std::collections::BTreeSet;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BooleanOp<'c> {
    BoolS(InternedString),
    BoolV(bool),
    Not(BoolAst<'c>),
    And(BoolAst<'c>, BoolAst<'c>),
    Or(BoolAst<'c>, BoolAst<'c>),
    Xor(BoolAst<'c>, BoolAst<'c>),
    BoolEq(BoolAst<'c>, BoolAst<'c>),
    BoolNeq(BoolAst<'c>, BoolAst<'c>),
    Eq(BitVecAst<'c>, BitVecAst<'c>),
    Neq(BitVecAst<'c>, BitVecAst<'c>),
    ULT(BitVecAst<'c>, BitVecAst<'c>),
    ULE(BitVecAst<'c>, BitVecAst<'c>),
    UGT(BitVecAst<'c>, BitVecAst<'c>),
    UGE(BitVecAst<'c>, BitVecAst<'c>),
    SLT(BitVecAst<'c>, BitVecAst<'c>),
    SLE(BitVecAst<'c>, BitVecAst<'c>),
    SGT(BitVecAst<'c>, BitVecAst<'c>),
    SGE(BitVecAst<'c>, BitVecAst<'c>),
    FpEq(FloatAst<'c>, FloatAst<'c>),
    FpNeq(FloatAst<'c>, FloatAst<'c>),
    FpLt(FloatAst<'c>, FloatAst<'c>),
    FpLeq(FloatAst<'c>, FloatAst<'c>),
    FpGt(FloatAst<'c>, FloatAst<'c>),
    FpGeq(FloatAst<'c>, FloatAst<'c>),
    FpIsNan(FloatAst<'c>),
    FpIsInf(FloatAst<'c>),
    StrContains(StringAst<'c>, StringAst<'c>),
    StrPrefixOf(StringAst<'c>, StringAst<'c>),
    StrSuffixOf(StringAst<'c>, StringAst<'c>),
    StrIsDigit(StringAst<'c>),
    StrEq(StringAst<'c>, StringAst<'c>),
    StrNeq(StringAst<'c>, StringAst<'c>),
    ITE(BoolAst<'c>, BoolAst<'c>, BoolAst<'c>),
}

pub type BoolAst<'c> = AstRef<'c, BooleanOp<'c>>;

pub struct BooleanOpChildIter<'a, 'c> {
    op: &'a BooleanOp<'c>,
    index: u8,
}

impl<'c> BooleanOp<'c> {
    pub fn child_iter(&self) -> BooleanOpChildIter<'_, 'c> {
        BooleanOpChildIter { op: self, index: 0 }
    }
}

impl<'a, 'c> Iterator for BooleanOpChildIter<'a, 'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = match (self.op, self.index) {
            // 0 children
            (BooleanOp::BoolS(_), _) | (BooleanOp::BoolV(_), _) => None,

            // 1 child variants - index 0
            (BooleanOp::Not(a), 0) => Some(a.into()),
            (BooleanOp::FpIsNan(a), 0) | (BooleanOp::FpIsInf(a), 0) => Some(a.into()),
            (BooleanOp::StrIsDigit(a), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (BooleanOp::And(a, _), 0)
            | (BooleanOp::Or(a, _), 0)
            | (BooleanOp::Xor(a, _), 0)
            | (BooleanOp::BoolEq(a, _), 0)
            | (BooleanOp::BoolNeq(a, _), 0) => Some(a.into()),

            (BooleanOp::Eq(a, _), 0)
            | (BooleanOp::Neq(a, _), 0)
            | (BooleanOp::ULT(a, _), 0)
            | (BooleanOp::ULE(a, _), 0)
            | (BooleanOp::UGT(a, _), 0)
            | (BooleanOp::UGE(a, _), 0)
            | (BooleanOp::SLT(a, _), 0)
            | (BooleanOp::SLE(a, _), 0)
            | (BooleanOp::SGT(a, _), 0)
            | (BooleanOp::SGE(a, _), 0) => Some(a.into()),

            (BooleanOp::FpEq(a, _), 0)
            | (BooleanOp::FpNeq(a, _), 0)
            | (BooleanOp::FpLt(a, _), 0)
            | (BooleanOp::FpLeq(a, _), 0)
            | (BooleanOp::FpGt(a, _), 0)
            | (BooleanOp::FpGeq(a, _), 0) => Some(a.into()),

            (BooleanOp::StrContains(a, _), 0)
            | (BooleanOp::StrPrefixOf(a, _), 0)
            | (BooleanOp::StrSuffixOf(a, _), 0)
            | (BooleanOp::StrEq(a, _), 0)
            | (BooleanOp::StrNeq(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (BooleanOp::And(_, b), 1)
            | (BooleanOp::Or(_, b), 1)
            | (BooleanOp::Xor(_, b), 1)
            | (BooleanOp::BoolEq(_, b), 1)
            | (BooleanOp::BoolNeq(_, b), 1) => Some(b.into()),

            (BooleanOp::Eq(_, b), 1)
            | (BooleanOp::Neq(_, b), 1)
            | (BooleanOp::ULT(_, b), 1)
            | (BooleanOp::ULE(_, b), 1)
            | (BooleanOp::UGT(_, b), 1)
            | (BooleanOp::UGE(_, b), 1)
            | (BooleanOp::SLT(_, b), 1)
            | (BooleanOp::SLE(_, b), 1)
            | (BooleanOp::SGT(_, b), 1)
            | (BooleanOp::SGE(_, b), 1) => Some(b.into()),

            (BooleanOp::FpEq(_, b), 1)
            | (BooleanOp::FpNeq(_, b), 1)
            | (BooleanOp::FpLt(_, b), 1)
            | (BooleanOp::FpLeq(_, b), 1)
            | (BooleanOp::FpGt(_, b), 1)
            | (BooleanOp::FpGeq(_, b), 1) => Some(b.into()),

            (BooleanOp::StrContains(_, b), 1)
            | (BooleanOp::StrPrefixOf(_, b), 1)
            | (BooleanOp::StrSuffixOf(_, b), 1)
            | (BooleanOp::StrEq(_, b), 1)
            | (BooleanOp::StrNeq(_, b), 1) => Some(b.into()),

            // 3 child variants
            (BooleanOp::ITE(a, _, _), 0) => Some(a.into()),
            (BooleanOp::ITE(_, b, _), 1) => Some(b.into()),
            (BooleanOp::ITE(_, _, c), 2) => Some(c.into()),

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

impl<'a, 'c> ExactSizeIterator for BooleanOpChildIter<'a, 'c> {
    fn len(&self) -> usize {
        let total: usize = match self.op {
            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => 0,

            BooleanOp::Not(_)
            | BooleanOp::FpIsNan(_)
            | BooleanOp::FpIsInf(_)
            | BooleanOp::StrIsDigit(_) => 1,

            BooleanOp::And(..)
            | BooleanOp::Or(..)
            | BooleanOp::Xor(..)
            | BooleanOp::BoolEq(..)
            | BooleanOp::BoolNeq(..)
            | BooleanOp::Eq(..)
            | BooleanOp::Neq(..)
            | BooleanOp::ULT(..)
            | BooleanOp::ULE(..)
            | BooleanOp::UGT(..)
            | BooleanOp::UGE(..)
            | BooleanOp::SLT(..)
            | BooleanOp::SLE(..)
            | BooleanOp::SGT(..)
            | BooleanOp::SGE(..)
            | BooleanOp::FpEq(..)
            | BooleanOp::FpNeq(..)
            | BooleanOp::FpLt(..)
            | BooleanOp::FpLeq(..)
            | BooleanOp::FpGt(..)
            | BooleanOp::FpGeq(..)
            | BooleanOp::StrContains(..)
            | BooleanOp::StrPrefixOf(..)
            | BooleanOp::StrSuffixOf(..)
            | BooleanOp::StrEq(..)
            | BooleanOp::StrNeq(..) => 2,

            BooleanOp::ITE(..) => 3,
        };
        total.saturating_sub(self.index as usize)
    }
}

impl std::hash::Hash for BooleanOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "bool".hash(state);
        match self {
            BooleanOp::BoolS(s) => {
                0.hash(state);
                s.hash(state);
            }
            BooleanOp::BoolV(b) => {
                1.hash(state);
                b.hash(state);
            }
            BooleanOp::Not(a) => {
                2.hash(state);
                a.hash(state);
            }
            BooleanOp::And(a, b) => {
                3.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::Or(a, b) => {
                4.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::Xor(a, b) => {
                5.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::BoolEq(a, b) => {
                6.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::BoolNeq(a, b) => {
                7.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::Eq(a, b) => {
                8.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::Neq(a, b) => {
                9.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::ULT(a, b) => {
                10.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::ULE(a, b) => {
                11.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::UGT(a, b) => {
                12.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::UGE(a, b) => {
                13.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::SLT(a, b) => {
                14.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::SLE(a, b) => {
                15.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::SGT(a, b) => {
                16.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::SGE(a, b) => {
                17.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpEq(a, b) => {
                18.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpNeq(a, b) => {
                19.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpLt(a, b) => {
                20.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpLeq(a, b) => {
                21.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpGt(a, b) => {
                22.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpGeq(a, b) => {
                23.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::FpIsNan(a) => {
                24.hash(state);
                a.hash(state);
            }
            BooleanOp::FpIsInf(a) => {
                25.hash(state);
                a.hash(state);
            }
            BooleanOp::StrContains(a, b) => {
                26.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::StrPrefixOf(a, b) => {
                27.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::StrSuffixOf(a, b) => {
                28.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::StrIsDigit(a) => {
                29.hash(state);
                a.hash(state);
            }
            BooleanOp::StrEq(a, b) => {
                30.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::StrNeq(a, b) => {
                31.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BooleanOp::ITE(a, b, c) => {
                32.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for BooleanOp<'c> {
    type ChildIter<'a>
        = BooleanOpChildIter<'a, 'c>
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
        BooleanOp::child_iter(self)
    }

    fn get_child(&self, index: usize) -> Option<DynAst<'c>> {
        match (self, index) {
            // 1 child variants - index 0
            (BooleanOp::Not(a), 0) => Some(a.into()),
            (BooleanOp::FpIsNan(a), 0) | (BooleanOp::FpIsInf(a), 0) => Some(a.into()),
            (BooleanOp::StrIsDigit(a), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (BooleanOp::And(a, _), 0)
            | (BooleanOp::Or(a, _), 0)
            | (BooleanOp::Xor(a, _), 0)
            | (BooleanOp::BoolEq(a, _), 0)
            | (BooleanOp::BoolNeq(a, _), 0) => Some(a.into()),

            (BooleanOp::Eq(a, _), 0)
            | (BooleanOp::Neq(a, _), 0)
            | (BooleanOp::ULT(a, _), 0)
            | (BooleanOp::ULE(a, _), 0)
            | (BooleanOp::UGT(a, _), 0)
            | (BooleanOp::UGE(a, _), 0)
            | (BooleanOp::SLT(a, _), 0)
            | (BooleanOp::SLE(a, _), 0)
            | (BooleanOp::SGT(a, _), 0)
            | (BooleanOp::SGE(a, _), 0) => Some(a.into()),

            (BooleanOp::FpEq(a, _), 0)
            | (BooleanOp::FpNeq(a, _), 0)
            | (BooleanOp::FpLt(a, _), 0)
            | (BooleanOp::FpLeq(a, _), 0)
            | (BooleanOp::FpGt(a, _), 0)
            | (BooleanOp::FpGeq(a, _), 0) => Some(a.into()),

            (BooleanOp::StrContains(a, _), 0)
            | (BooleanOp::StrPrefixOf(a, _), 0)
            | (BooleanOp::StrSuffixOf(a, _), 0)
            | (BooleanOp::StrEq(a, _), 0)
            | (BooleanOp::StrNeq(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (BooleanOp::And(_, b), 1)
            | (BooleanOp::Or(_, b), 1)
            | (BooleanOp::Xor(_, b), 1)
            | (BooleanOp::BoolEq(_, b), 1)
            | (BooleanOp::BoolNeq(_, b), 1) => Some(b.into()),

            (BooleanOp::Eq(_, b), 1)
            | (BooleanOp::Neq(_, b), 1)
            | (BooleanOp::ULT(_, b), 1)
            | (BooleanOp::ULE(_, b), 1)
            | (BooleanOp::UGT(_, b), 1)
            | (BooleanOp::UGE(_, b), 1)
            | (BooleanOp::SLT(_, b), 1)
            | (BooleanOp::SLE(_, b), 1)
            | (BooleanOp::SGT(_, b), 1)
            | (BooleanOp::SGE(_, b), 1) => Some(b.into()),

            (BooleanOp::FpEq(_, b), 1)
            | (BooleanOp::FpNeq(_, b), 1)
            | (BooleanOp::FpLt(_, b), 1)
            | (BooleanOp::FpLeq(_, b), 1)
            | (BooleanOp::FpGt(_, b), 1)
            | (BooleanOp::FpGeq(_, b), 1) => Some(b.into()),

            (BooleanOp::StrContains(_, b), 1)
            | (BooleanOp::StrPrefixOf(_, b), 1)
            | (BooleanOp::StrSuffixOf(_, b), 1)
            | (BooleanOp::StrEq(_, b), 1)
            | (BooleanOp::StrNeq(_, b), 1) => Some(b.into()),

            // 3 child variants
            (BooleanOp::ITE(a, _, _), 0) => Some(a.into()),
            (BooleanOp::ITE(_, b, _), 1) => Some(b.into()),
            (BooleanOp::ITE(_, _, c), 2) => Some(c.into()),

            _ => None,
        }
    }

    fn is_true(&self) -> bool {
        matches!(self, BooleanOp::BoolV(true))
    }

    fn is_false(&self) -> bool {
        matches!(self, BooleanOp::BoolV(false))
    }

    fn variables(&self) -> BTreeSet<InternedString> {
        if let BooleanOp::BoolS(s) = self {
            let mut set = BTreeSet::new();
            set.insert(s.clone());
            set
        } else {
            self.child_iter()
                .map(|x| x.variables())
                .fold(BTreeSet::new(), |acc, x| acc.union(&x).cloned().collect())
        }
    }

    fn check_same_sort(&self, _: &Self) -> bool {
        true
    }
}
