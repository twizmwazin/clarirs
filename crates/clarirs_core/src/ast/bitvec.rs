use std::collections::BTreeSet;

use serde::Serialize;

use crate::prelude::*;

use super::float::FloatExt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BitVecOp<'c> {
    BVS(InternedString, u32),
    BVV(BitVec),
    Not(BitVecAst<'c>),
    And(BitVecAst<'c>, BitVecAst<'c>),
    Or(BitVecAst<'c>, BitVecAst<'c>),
    Xor(BitVecAst<'c>, BitVecAst<'c>),
    Neg(BitVecAst<'c>),
    Add(BitVecAst<'c>, BitVecAst<'c>),
    Sub(BitVecAst<'c>, BitVecAst<'c>),
    Mul(BitVecAst<'c>, BitVecAst<'c>),
    UDiv(BitVecAst<'c>, BitVecAst<'c>),
    SDiv(BitVecAst<'c>, BitVecAst<'c>),
    URem(BitVecAst<'c>, BitVecAst<'c>),
    SRem(BitVecAst<'c>, BitVecAst<'c>),
    ShL(BitVecAst<'c>, BitVecAst<'c>),
    LShR(BitVecAst<'c>, BitVecAst<'c>),
    AShR(BitVecAst<'c>, BitVecAst<'c>),
    RotateLeft(BitVecAst<'c>, BitVecAst<'c>),
    RotateRight(BitVecAst<'c>, BitVecAst<'c>),
    ZeroExt(BitVecAst<'c>, u32),
    SignExt(BitVecAst<'c>, u32),
    Extract(BitVecAst<'c>, u32, u32),
    Concat(Vec<BitVecAst<'c>>),
    ByteReverse(BitVecAst<'c>),
    FpToIEEEBV(FloatAst<'c>),
    FpToUBV(FloatAst<'c>, u32, FPRM),
    FpToSBV(FloatAst<'c>, u32, FPRM),
    StrLen(StringAst<'c>),
    StrIndexOf(StringAst<'c>, StringAst<'c>, BitVecAst<'c>),
    StrToBV(StringAst<'c>),
    ITE(AstRef<'c, BooleanOp<'c>>, BitVecAst<'c>, BitVecAst<'c>),

    // VSA Ops
    Union(BitVecAst<'c>, BitVecAst<'c>),
    Intersection(BitVecAst<'c>, BitVecAst<'c>),
}

pub type BitVecAst<'c> = AstRef<'c, BitVecOp<'c>>;

pub struct BitVecOpChildIter<'a, 'c> {
    op: &'a BitVecOp<'c>,
    index: usize,
}

impl<'c> BitVecOp<'c> {
    pub fn child_iter(&self) -> BitVecOpChildIter<'_, 'c> {
        BitVecOpChildIter { op: self, index: 0 }
    }
}

impl<'a, 'c> Iterator for BitVecOpChildIter<'a, 'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = match (self.op, self.index) {
            // 0 children
            (BitVecOp::BVS(..), _) | (BitVecOp::BVV(..), _) => None,

            // 1 child variants - index 0
            (BitVecOp::Not(a), 0)
            | (BitVecOp::Neg(a), 0)
            | (BitVecOp::ByteReverse(a), 0)
            | (BitVecOp::ZeroExt(a, _), 0)
            | (BitVecOp::SignExt(a, _), 0)
            | (BitVecOp::Extract(a, _, _), 0) => Some(a.into()),

            (BitVecOp::StrLen(a), 0) | (BitVecOp::StrToBV(a), 0) => Some(a.into()),

            (BitVecOp::FpToIEEEBV(a), 0)
            | (BitVecOp::FpToUBV(a, _, _), 0)
            | (BitVecOp::FpToSBV(a, _, _), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (BitVecOp::And(a, _), 0)
            | (BitVecOp::Or(a, _), 0)
            | (BitVecOp::Xor(a, _), 0)
            | (BitVecOp::Add(a, _), 0)
            | (BitVecOp::Sub(a, _), 0)
            | (BitVecOp::Mul(a, _), 0)
            | (BitVecOp::UDiv(a, _), 0)
            | (BitVecOp::SDiv(a, _), 0)
            | (BitVecOp::URem(a, _), 0)
            | (BitVecOp::SRem(a, _), 0)
            | (BitVecOp::ShL(a, _), 0)
            | (BitVecOp::LShR(a, _), 0)
            | (BitVecOp::AShR(a, _), 0)
            | (BitVecOp::RotateLeft(a, _), 0)
            | (BitVecOp::RotateRight(a, _), 0)
            | (BitVecOp::Union(a, _), 0)
            | (BitVecOp::Intersection(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (BitVecOp::And(_, b), 1)
            | (BitVecOp::Or(_, b), 1)
            | (BitVecOp::Xor(_, b), 1)
            | (BitVecOp::Add(_, b), 1)
            | (BitVecOp::Sub(_, b), 1)
            | (BitVecOp::Mul(_, b), 1)
            | (BitVecOp::UDiv(_, b), 1)
            | (BitVecOp::SDiv(_, b), 1)
            | (BitVecOp::URem(_, b), 1)
            | (BitVecOp::SRem(_, b), 1)
            | (BitVecOp::ShL(_, b), 1)
            | (BitVecOp::LShR(_, b), 1)
            | (BitVecOp::AShR(_, b), 1)
            | (BitVecOp::RotateLeft(_, b), 1)
            | (BitVecOp::RotateRight(_, b), 1)
            | (BitVecOp::Union(_, b), 1)
            | (BitVecOp::Intersection(_, b), 1) => Some(b.into()),

            // 3 child variants
            (BitVecOp::StrIndexOf(a, _, _), 0) => Some(a.into()),
            (BitVecOp::StrIndexOf(_, b, _), 1) => Some(b.into()),
            (BitVecOp::StrIndexOf(_, _, c), 2) => Some(c.into()),

            (BitVecOp::ITE(a, _, _), 0) => Some(a.into()),
            (BitVecOp::ITE(_, b, _), 1) => Some(b.into()),
            (BitVecOp::ITE(_, _, c), 2) => Some(c.into()),

            // N-ary Concat - variable children
            (BitVecOp::Concat(args), i) if i < args.len() => Some(args[i].clone().into()),

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

impl<'a, 'c> ExactSizeIterator for BitVecOpChildIter<'a, 'c> {
    fn len(&self) -> usize {
        let total: usize = match self.op {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) => 0,

            BitVecOp::Not(..)
            | BitVecOp::Neg(..)
            | BitVecOp::ByteReverse(..)
            | BitVecOp::ZeroExt(..)
            | BitVecOp::SignExt(..)
            | BitVecOp::Extract(..)
            | BitVecOp::StrLen(..)
            | BitVecOp::StrToBV(..)
            | BitVecOp::FpToIEEEBV(..)
            | BitVecOp::FpToUBV(..)
            | BitVecOp::FpToSBV(..) => 1,

            BitVecOp::And(..)
            | BitVecOp::Or(..)
            | BitVecOp::Xor(..)
            | BitVecOp::Add(..)
            | BitVecOp::Sub(..)
            | BitVecOp::Mul(..)
            | BitVecOp::UDiv(..)
            | BitVecOp::SDiv(..)
            | BitVecOp::URem(..)
            | BitVecOp::SRem(..)
            | BitVecOp::ShL(..)
            | BitVecOp::LShR(..)
            | BitVecOp::AShR(..)
            | BitVecOp::RotateLeft(..)
            | BitVecOp::RotateRight(..)
            | BitVecOp::Union(..)
            | BitVecOp::Intersection(..) => 2,

            BitVecOp::Concat(args) => args.len(),

            BitVecOp::StrIndexOf(..) | BitVecOp::ITE(..) => 3,
        };
        total.saturating_sub(self.index)
    }
}

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
            BitVecOp::Neg(a) => {
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
            BitVecOp::Extract(a, high, low) => {
                22.hash(state);
                a.hash(state);
                high.hash(state);
                low.hash(state);
            }
            BitVecOp::Concat(args) => {
                23.hash(state);
                args.hash(state);
            }
            BitVecOp::ByteReverse(a) => {
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
            BitVecOp::ITE(a, b, c) => {
                31.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            BitVecOp::Union(a, b) => {
                34.hash(state);
                a.hash(state);
                b.hash(state);
            }
            BitVecOp::Intersection(a, b) => {
                35.hash(state);
                a.hash(state);
                b.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for BitVecOp<'c> {
    type ChildIter<'a>
        = BitVecOpChildIter<'a, 'c>
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
        BitVecOp::child_iter(self)
    }

    fn get_child(&self, index: usize) -> Option<DynAst<'c>> {
        match (self, index) {
            // 1 child variants - index 0
            (BitVecOp::Not(a), 0)
            | (BitVecOp::Neg(a), 0)
            | (BitVecOp::ByteReverse(a), 0)
            | (BitVecOp::ZeroExt(a, _), 0)
            | (BitVecOp::SignExt(a, _), 0)
            | (BitVecOp::Extract(a, _, _), 0) => Some(a.into()),

            (BitVecOp::StrLen(a), 0) | (BitVecOp::StrToBV(a), 0) => Some(a.into()),

            (BitVecOp::FpToIEEEBV(a), 0)
            | (BitVecOp::FpToUBV(a, _, _), 0)
            | (BitVecOp::FpToSBV(a, _, _), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (BitVecOp::And(a, _), 0)
            | (BitVecOp::Or(a, _), 0)
            | (BitVecOp::Xor(a, _), 0)
            | (BitVecOp::Add(a, _), 0)
            | (BitVecOp::Sub(a, _), 0)
            | (BitVecOp::Mul(a, _), 0)
            | (BitVecOp::UDiv(a, _), 0)
            | (BitVecOp::SDiv(a, _), 0)
            | (BitVecOp::URem(a, _), 0)
            | (BitVecOp::SRem(a, _), 0)
            | (BitVecOp::ShL(a, _), 0)
            | (BitVecOp::LShR(a, _), 0)
            | (BitVecOp::AShR(a, _), 0)
            | (BitVecOp::RotateLeft(a, _), 0)
            | (BitVecOp::RotateRight(a, _), 0)
            | (BitVecOp::Union(a, _), 0)
            | (BitVecOp::Intersection(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (BitVecOp::And(_, b), 1)
            | (BitVecOp::Or(_, b), 1)
            | (BitVecOp::Xor(_, b), 1)
            | (BitVecOp::Add(_, b), 1)
            | (BitVecOp::Sub(_, b), 1)
            | (BitVecOp::Mul(_, b), 1)
            | (BitVecOp::UDiv(_, b), 1)
            | (BitVecOp::SDiv(_, b), 1)
            | (BitVecOp::URem(_, b), 1)
            | (BitVecOp::SRem(_, b), 1)
            | (BitVecOp::ShL(_, b), 1)
            | (BitVecOp::LShR(_, b), 1)
            | (BitVecOp::AShR(_, b), 1)
            | (BitVecOp::RotateLeft(_, b), 1)
            | (BitVecOp::RotateRight(_, b), 1)
            | (BitVecOp::Union(_, b), 1)
            | (BitVecOp::Intersection(_, b), 1) => Some(b.into()),

            // 3 child variants
            (BitVecOp::StrIndexOf(a, _, _), 0) => Some(a.into()),
            (BitVecOp::StrIndexOf(_, b, _), 1) => Some(b.into()),
            (BitVecOp::StrIndexOf(_, _, c), 2) => Some(c.into()),

            (BitVecOp::ITE(a, _, _), 0) => Some(a.into()),
            (BitVecOp::ITE(_, b, _), 1) => Some(b.into()),
            (BitVecOp::ITE(_, _, c), 2) => Some(c.into()),

            // N-ary Concat
            (BitVecOp::Concat(args), i) if i < args.len() => Some(args[i].clone().into()),

            _ => None,
        }
    }

    fn variables(&self) -> BTreeSet<InternedString> {
        if let BitVecOp::BVS(s, _) = self {
            let mut set = BTreeSet::new();
            set.insert(s.clone());
            set
        } else {
            self.child_iter()
                .map(|x| x.variables())
                .fold(BTreeSet::new(), |acc, x| acc.union(&x).cloned().collect())
        }
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        self.size() == other.size()
    }
}

pub trait BitVecOpExt<'c> {
    fn size(&self) -> u32;
}

pub trait BitVecAstExt<'c> {
    /// Chop the BV into `bits` sized pieces. Returns in little-endian order.
    fn chop(&self, bits: u32) -> Result<Vec<BitVecAst<'c>>, ClarirsError>;
}

impl<'c> BitVecOpExt<'c> for BitVecOp<'c> {
    fn size(&self) -> u32 {
        match self {
            BitVecOp::BVS(_, size) => *size,
            BitVecOp::BVV(bv) => bv.len(),
            BitVecOp::Not(a)
            | BitVecOp::Neg(a)
            | BitVecOp::ByteReverse(a)
            | BitVecOp::ITE(_, a, _) => a.size(),
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
            | BitVecOp::ShL(a, _)
            | BitVecOp::LShR(a, _)
            | BitVecOp::AShR(a, _)
            | BitVecOp::RotateLeft(a, _)
            | BitVecOp::RotateRight(a, _)
            | BitVecOp::Union(a, _)
            | BitVecOp::Intersection(a, _) => a.size(),
            BitVecOp::Extract(_, high, low) => high - low + 1,
            BitVecOp::Concat(args) => args.iter().map(|a| a.size()).sum(),
            BitVecOp::ZeroExt(a, ext) | BitVecOp::SignExt(a, ext) => a.size() + ext,
            BitVecOp::FpToIEEEBV(fp) => fp.size(),
            BitVecOp::FpToUBV(_, size, _) | BitVecOp::FpToSBV(_, size, _) => *size,
            BitVecOp::StrLen(_) | BitVecOp::StrToBV(_) | BitVecOp::StrIndexOf(_, _, _) => 64,
        }
    }
}

impl<'c> BitVecOpExt<'c> for BitVecAst<'c> {
    fn size(&self) -> u32 {
        self.size
    }
}

impl<'c> BitVecAstExt<'c> for BitVecAst<'c> {
    fn chop(&self, bits: u32) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        if self.size() % bits != 0 {
            return Err(ClarirsError::InvalidChopSize {
                size: self.size(),
                bits,
            });
        }

        let mut res = vec![];
        for i in 0..self.size() / bits {
            res.push(
                self.context()
                    .extract(self, ((i + 1) * bits) - 1, i * bits)?,
            );
        }
        res.reverse();

        Ok(res)
    }
}
