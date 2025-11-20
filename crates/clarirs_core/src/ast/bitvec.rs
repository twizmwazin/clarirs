use std::collections::BTreeSet;
use std::sync::Arc;
use std::vec::IntoIter;

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
    Concat(BitVecAst<'c>, BitVecAst<'c>),
    ByteReverse(BitVecAst<'c>),
    FpToIEEEBV(FloatAst<'c>),
    FpToUBV(FloatAst<'c>, u32, FPRM),
    FpToSBV(FloatAst<'c>, u32, FPRM),
    StrLen(StringAst<'c>),
    StrIndexOf(StringAst<'c>, StringAst<'c>, BitVecAst<'c>),
    StrToBV(StringAst<'c>),
    If(AstRef<'c, BooleanOp<'c>>, BitVecAst<'c>, BitVecAst<'c>),

    // VSA Ops
    Union(BitVecAst<'c>, BitVecAst<'c>),
    Intersection(BitVecAst<'c>, BitVecAst<'c>),
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
            BitVecOp::Concat(a, b) => {
                23.hash(state);
                a.hash(state);
                b.hash(state);
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
            BitVecOp::If(a, b, c) => {
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
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        match self {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) => vec![],
            BitVecOp::Not(a)
            | BitVecOp::Neg(a)
            | BitVecOp::ByteReverse(a)
            | BitVecOp::ZeroExt(a, _)
            | BitVecOp::SignExt(a, _)
            | BitVecOp::Extract(a, _, _) => vec![a.into()],
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
            | BitVecOp::ShL(a, b)
            | BitVecOp::LShR(a, b)
            | BitVecOp::AShR(a, b)
            | BitVecOp::RotateLeft(a, b)
            | BitVecOp::RotateRight(a, b)
            | BitVecOp::Concat(a, b)
            | BitVecOp::Union(a, b)
            | BitVecOp::Intersection(a, b) => vec![a.into(), b.into()],
            BitVecOp::StrIndexOf(a, b, c) => vec![a.into(), b.into(), c.into()],
            BitVecOp::If(a, b, c) => vec![a.into(), b.into(), c.into()],
        }
        .into_iter()
    }

    fn variables(&self) -> Arc<BTreeSet<InternedString>> {
        if let BitVecOp::BVS(s, _) = self {
            let mut set = BTreeSet::new();
            set.insert(s.clone());
            return Arc::new(set);
        }

        let mut child_iter = self.child_iter();

        // Handle the common cases efficiently without allocating Vecs
        let first_child = match child_iter.next() {
            None => return Arc::new(BTreeSet::new()), // No children
            Some(child) => child,
        };

        let first_vars = first_child.variables();

        let second_child = match child_iter.next() {
            None => return first_vars, // Single child - reuse directly
            Some(child) => child,
        };

        let second_vars = second_child.variables();

        // Check if we have more children
        let third_child = child_iter.next();

        if third_child.is_none() {
            // Two children - common case for binary operations
            if Arc::ptr_eq(&first_vars, &second_vars) {
                return first_vars; // Both children have same variables
            }

            // Check if one is a superset of the other
            if second_vars.iter().all(|v| first_vars.contains(v)) {
                return first_vars; // first is superset
            }
            if first_vars.iter().all(|v| second_vars.contains(v)) {
                return second_vars; // second is superset
            }

            // Need to create union
            let mut result = (*first_vars).clone();
            result.extend(second_vars.iter().cloned());
            return Arc::new(result);
        }

        // Three or more children - collect and process
        let mut child_vars = vec![first_vars, second_vars, third_child.unwrap().variables()];
        child_vars.extend(child_iter.map(|c| c.variables()));

        // Check if all children have the same variables
        let first_vars = &child_vars[0];
        if child_vars.iter().all(|v| Arc::ptr_eq(v, first_vars)) {
            return Arc::clone(first_vars);
        }

        // Check if one child's variables is a superset of all others
        for candidate in &child_vars {
            let mut is_superset = true;
            for other in &child_vars {
                if Arc::ptr_eq(candidate, other) {
                    continue;
                }
                if !other.iter().all(|v| candidate.contains(v)) {
                    is_superset = false;
                    break;
                }
            }
            if is_superset {
                return Arc::clone(candidate);
            }
        }

        // Need to create a new set - compute union
        let mut result = BTreeSet::new();
        for vars in child_vars {
            result.extend(vars.iter().cloned());
        }
        Arc::new(result)
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
            | BitVecOp::If(_, a, _) => a.size(),
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
            BitVecOp::Concat(a, b) => a.size() + b.size(),
            BitVecOp::ZeroExt(a, ext) | BitVecOp::SignExt(a, ext) => a.size() + ext,
            BitVecOp::FpToIEEEBV(fp) => fp.size(),
            BitVecOp::FpToUBV(_, size, _) | BitVecOp::FpToSBV(_, size, _) => *size,
            BitVecOp::StrLen(_) | BitVecOp::StrToBV(_) | BitVecOp::StrIndexOf(_, _, _) => 64,
        }
    }
}

impl<'c> BitVecOpExt<'c> for BitVecAst<'c> {
    fn size(&self) -> u32 {
        self.op().size()
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
