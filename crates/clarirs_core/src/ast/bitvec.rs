use std::collections::HashSet;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

use super::float::FloatExt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BitVecOp<'c> {
    BVS(String, u32),
    BVV(BitVec),
    Not(BitVecAst<'c>),
    And(BitVecAst<'c>, BitVecAst<'c>),
    Or(BitVecAst<'c>, BitVecAst<'c>),
    Xor(BitVecAst<'c>, BitVecAst<'c>),
    Abs(BitVecAst<'c>),
    Add(BitVecAst<'c>, BitVecAst<'c>),
    Sub(BitVecAst<'c>, BitVecAst<'c>),
    Mul(BitVecAst<'c>, BitVecAst<'c>),
    UDiv(BitVecAst<'c>, BitVecAst<'c>),
    SDiv(BitVecAst<'c>, BitVecAst<'c>),
    URem(BitVecAst<'c>, BitVecAst<'c>),
    SRem(BitVecAst<'c>, BitVecAst<'c>),
    Pow(BitVecAst<'c>, BitVecAst<'c>),
    ShL(BitVecAst<'c>, BitVecAst<'c>),
    LShR(BitVecAst<'c>, BitVecAst<'c>),
    AShR(BitVecAst<'c>, BitVecAst<'c>),
    RotateLeft(BitVecAst<'c>, BitVecAst<'c>),
    RotateRight(BitVecAst<'c>, BitVecAst<'c>),
    ZeroExt(BitVecAst<'c>, u32),
    SignExt(BitVecAst<'c>, u32),
    Extract(BitVecAst<'c>, u32, u32),
    Concat(BitVecAst<'c>, BitVecAst<'c>),
    Reverse(BitVecAst<'c>),
    FpToIEEEBV(FloatAst<'c>),
    FpToUBV(FloatAst<'c>, u32, FPRM),
    FpToSBV(FloatAst<'c>, u32, FPRM),
    StrLen(StringAst<'c>),
    StrIndexOf(StringAst<'c>, StringAst<'c>, BitVecAst<'c>),
    StrToBV(StringAst<'c>),
    If(AstRef<'c, BooleanOp<'c>>, BitVecAst<'c>, BitVecAst<'c>),
    Annotated(BitVecAst<'c>, Annotation),
}

pub type BitVecAst<'c> = AstRef<'c, BitVecOp<'c>>;

impl std::hash::Hash for BitVecOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "bv".hash(state);
        match self {
            BitVecOp::BVS(s, size) => {
                0.hash(state);
                s.hash(state);
                size.hash(state);
            }
            BitVecOp::BVV(bv) => {
                1.hash(state);
                bv.hash(state);
            }
            BitVecOp::Not(a) => {
                2.hash(state);
                a.hash(state);
            }
            BitVecOp::And(a, b) => {
                3.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Or(a, b) => {
                4.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Xor(a, b) => {
                5.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Abs(a) => {
                6.hash(state);
                a.hash(state);
            }
            BitVecOp::Add(a, b) => {
                7.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Sub(a, b) => {
                8.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Mul(a, b) => {
                9.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::UDiv(a, b) => {
                10.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::SDiv(a, b) => {
                11.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::URem(a, b) => {
                12.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::SRem(a, b) => {
                13.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Pow(a, b) => {
                14.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::ShL(a, b) => {
                15.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::LShR(a, b) => {
                16.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::AShR(a, b) => {
                17.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::RotateLeft(a, b) => {
                18.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::RotateRight(a, b) => {
                19.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::ZeroExt(a, size) => {
                20.hash(state);
                a.hash(state);
                size.hash(state);
            }
            BitVecOp::SignExt(a, size) => {
                21.hash(state);
                a.hash(state);
                size.hash(state);
            }
            BitVecOp::Extract(a, low, high) => {
                22.hash(state);
                a.hash(state);
                low.hash(state);
                high.hash(state);
            }
            BitVecOp::Concat(a, b) => {
                23.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Reverse(a) => {
                24.hash(state);
                a.hash(state);
            }
            BitVecOp::FpToIEEEBV(a) => {
                25.hash(state);
                a.hash(state);
            }
            BitVecOp::FpToUBV(a, size, rm) => {
                26.hash(state);
                a.hash(state);
                size.hash(state);
                rm.hash(state);
            }
            BitVecOp::FpToSBV(a, size, rm) => {
                27.hash(state);
                a.hash(state);
                size.hash(state);
                rm.hash(state);
            }
            BitVecOp::StrLen(a) => {
                28.hash(state);
                a.hash(state);
            }
            BitVecOp::StrIndexOf(a, b, c) => {
                29.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            BitVecOp::StrToBV(a) => {
                30.hash(state);
                a.hash(state);
            }
            BitVecOp::If(a, b, c) => {
                31.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            BitVecOp::Annotated(a, anno) => {
                32.hash(state);
                a.hash(state);
                anno.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for BitVecOp<'c> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        match self {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) => vec![],

            BitVecOp::Not(a)
            | BitVecOp::Abs(a)
            | BitVecOp::Reverse(a)
            | BitVecOp::ZeroExt(a, _)
            | BitVecOp::SignExt(a, _)
            | BitVecOp::Extract(a, _, _)
            | BitVecOp::Annotated(a, _) => vec![a.into()],
            BitVecOp::StrLen(a) | BitVecOp::StrToBV(a) => vec![a.into()],
            BitVecOp::FpToIEEEBV(a) | BitVecOp::FpToUBV(a, _, _) | BitVecOp::FpToSBV(a, _, _) => {
                vec![a.into()]
            }

            BitVecOp::And(a, b)
            | BitVecOp::Or(a, b)
            | BitVecOp::Xor(a, b)
            | BitVecOp::Add(a, b)
            | BitVecOp::Sub(a, b)
            | BitVecOp::Mul(a, b)
            | BitVecOp::UDiv(a, b)
            | BitVecOp::SDiv(a, b)
            | BitVecOp::URem(a, b)
            | BitVecOp::SRem(a, b)
            | BitVecOp::Pow(a, b)
            | BitVecOp::ShL(a, b)
            | BitVecOp::LShR(a, b)
            | BitVecOp::AShR(a, b)
            | BitVecOp::RotateLeft(a, b)
            | BitVecOp::RotateRight(a, b)
            | BitVecOp::Concat(a, b) => vec![a.into(), b.into()],

            BitVecOp::StrIndexOf(a, b, c) => vec![a.into(), b.into(), c.into()],
            BitVecOp::If(a, b, c) => vec![a.into(), b.into(), c.into()],
        }
        .into_iter()
    }

    fn variables(&self) -> HashSet<String> {
        if let BitVecOp::BVS(s, _) = self {
            let mut set = HashSet::new();
            set.insert(s.clone());
            set
        } else {
            self.child_iter()
                .map(|x| x.variables())
                .fold(HashSet::new(), |acc, x| acc.union(&x).cloned().collect())
        }
    }

    fn get_annotations(&self) -> Vec<Annotation> {
        if let BitVecOp::Annotated(inner, anno) = self {
            inner
                .get_annotations()
                .into_iter()
                .chain(vec![anno.clone()])
                .collect()
        } else {
            vec![]
        }
    }
}

pub trait BitVecExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> BitVecExt<'c> for BitVecAst<'c> {
    fn size(&self) -> u32 {
        match self.op() {
            BitVecOp::BVS(_, size) | BitVecOp::ZeroExt(_, size) | BitVecOp::SignExt(_, size) => {
                *size
            }
            BitVecOp::BVV(bv) => bv.len() as u32,
            BitVecOp::Not(a)
            | BitVecOp::Abs(a)
            | BitVecOp::Reverse(a)
            | BitVecOp::If(_, a, _)
            | BitVecOp::Annotated(a, _) => a.size(),
            BitVecOp::And(a, _)
            | BitVecOp::Or(a, _)
            | BitVecOp::Xor(a, _)
            | BitVecOp::Add(a, _)
            | BitVecOp::Sub(a, _)
            | BitVecOp::Mul(a, _)
            | BitVecOp::UDiv(a, _)
            | BitVecOp::SDiv(a, _)
            | BitVecOp::URem(a, _)
            | BitVecOp::SRem(a, _)
            | BitVecOp::Pow(a, _)
            | BitVecOp::ShL(a, _)
            | BitVecOp::LShR(a, _)
            | BitVecOp::AShR(a, _)
            | BitVecOp::RotateLeft(a, _)
            | BitVecOp::RotateRight(a, _) => a.size(),
            BitVecOp::Extract(_, low, high) => high - low,
            BitVecOp::Concat(a, b) => a.size() + b.size(),
            BitVecOp::FpToIEEEBV(fp) => fp.size(),
            BitVecOp::FpToUBV(_, _, _) | BitVecOp::FpToSBV(_, _, _) => 64,
            BitVecOp::StrLen(_) | BitVecOp::StrToBV(_) | BitVecOp::StrIndexOf(_, _, _) => 64,
        }
    }
}
