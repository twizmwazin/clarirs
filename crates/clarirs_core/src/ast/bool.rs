use std::collections::HashSet;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BooleanOp<'c> {
    BoolS(String),
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
    If(BoolAst<'c>, BoolAst<'c>, BoolAst<'c>),
    Annotated(BoolAst<'c>, Annotation),
}

pub type BoolAst<'c> = AstRef<'c, BooleanOp<'c>>;

impl<'c> Op<'c> for BooleanOp<'c> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        match self {
            // Cases with no children
            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => vec![],

            // Cases with one child
            BooleanOp::Not(a) | BooleanOp::Annotated(a, _) => vec![a.into()],

            BooleanOp::FpIsNan(a) | BooleanOp::FpIsInf(a) => vec![a.into()],
            BooleanOp::StrIsDigit(a) => vec![a.into()],

            // Cases with two children
            BooleanOp::And(a, b)
            | BooleanOp::Or(a, b)
            | BooleanOp::Xor(a, b)
            | BooleanOp::BoolEq(a, b)
            | BooleanOp::BoolNeq(a, b) => {
                vec![a.into(), b.into()]
            }
            BooleanOp::Eq(a, b)
            | BooleanOp::Neq(a, b)
            | BooleanOp::ULT(a, b)
            | BooleanOp::ULE(a, b)
            | BooleanOp::UGT(a, b)
            | BooleanOp::UGE(a, b)
            | BooleanOp::SLT(a, b)
            | BooleanOp::SLE(a, b)
            | BooleanOp::SGT(a, b)
            | BooleanOp::SGE(a, b) => vec![a.into(), b.into()],
            BooleanOp::FpEq(a, b)
            | BooleanOp::FpNeq(a, b)
            | BooleanOp::FpLt(a, b)
            | BooleanOp::FpLeq(a, b)
            | BooleanOp::FpGt(a, b)
            | BooleanOp::FpGeq(a, b) => vec![a.into(), b.into()],
            BooleanOp::StrContains(a, b)
            | BooleanOp::StrPrefixOf(a, b)
            | BooleanOp::StrSuffixOf(a, b)
            | BooleanOp::StrEq(a, b)
            | BooleanOp::StrNeq(a, b) => vec![a.into(), b.into()],

            // Cases with three children
            BooleanOp::If(a, b, c) => vec![a.into(), b.into(), c.into()],
        }
        .into_iter()
    }

    fn is_true(&self) -> bool {
        matches!(self, BooleanOp::BoolV(true))
    }

    fn is_false(&self) -> bool {
        matches!(self, BooleanOp::BoolV(false))
    }

    fn variables(&self) -> HashSet<String> {
        if let BooleanOp::BoolS(s) = self {
            let mut set = HashSet::new();
            set.insert(s.clone());
            set
        } else {
            self.child_iter()
                .map(|x| x.variables())
                .fold(HashSet::new(), |acc, x| acc.union(&x).cloned().collect())
        }
    }
}
