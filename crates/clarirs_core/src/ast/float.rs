use std::collections::BTreeSet;
use std::sync::Arc;
use std::vec::IntoIter;

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
    If(AstRef<'c, BooleanOp<'c>>, FloatAst<'c>, FloatAst<'c>),
}

pub type FloatAst<'c> = AstRef<'c, FloatOp<'c>>;

impl std::hash::Hash for FloatOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "float".hash(state);
        match self {
            FloatOp::FPS(s, sort) => {
                0.hash(state);
                s.hash(state);
                sort.hash(state);
            }
            FloatOp::FPV(f) => {
                1.hash(state);
                f.hash(state);
            }
            FloatOp::FpNeg(a) => {
                2.hash(state);
                a.hash(state);
            }
            FloatOp::FpAbs(a) => {
                3.hash(state);
                a.hash(state);
            }
            FloatOp::FpAdd(a, b, rm) => {
                4.hash(state);
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpSub(a, b, rm) => {
                5.hash(state);
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpMul(a, b, rm) => {
                6.hash(state);
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpDiv(a, b, rm) => {
                7.hash(state);
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            FloatOp::FpSqrt(a, rm) => {
                8.hash(state);
                a.hash(state);
                rm.hash(state);
            }
            FloatOp::FpToFp(a, sort, rm) => {
                9.hash(state);
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::FpFP(sign, exp, sig) => {
                10.hash(state);
                sign.hash(state);
                exp.hash(state);
                sig.hash(state);
            }
            FloatOp::BvToFp(a, sort) => {
                11.hash(state);
                a.hash(state);
                sort.hash(state);
            }
            FloatOp::BvToFpSigned(a, sort, rm) => {
                12.hash(state);
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                13.hash(state);
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::If(a, b, c) => {
                14.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for FloatOp<'c> {
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        match self {
            FloatOp::FPS(_, _) | FloatOp::FPV(_) => vec![].into_iter(),

            FloatOp::FpNeg(a)
            | FloatOp::FpAbs(a)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpToFp(a, _, _) => vec![a.into()].into_iter(),
            FloatOp::FpFP(sign, exp, sig) => vec![sign.into(), exp.into(), sig.into()].into_iter(),
            FloatOp::BvToFp(a, _)
            | FloatOp::BvToFpSigned(a, _, _)
            | FloatOp::BvToFpUnsigned(a, _, _) => vec![a.into()].into_iter(),

            FloatOp::FpAdd(a, b, _)
            | FloatOp::FpSub(a, b, _)
            | FloatOp::FpMul(a, b, _)
            | FloatOp::FpDiv(a, b, _) => vec![a.into(), b.into()].into_iter(),
            FloatOp::If(a, b, c) => vec![a.into(), b.into(), c.into()].into_iter(),
        }
    }

    fn variables(&self) -> Arc<BTreeSet<InternedString>> {
        if let FloatOp::FPS(s, _) = self {
            let mut set = BTreeSet::new();
            set.insert(s.clone());
            Arc::new(set)
        } else {
            let children: Vec<_> = self.child_iter().collect();

            // If there are no children, return empty set
            if children.is_empty() {
                return Arc::new(BTreeSet::new());
            }

            // If there's only one child, reuse its variables
            if children.len() == 1 {
                return children[0].variables();
            }

            // For multiple children, check if we can reuse one child's set
            let child_vars: Vec<_> = children.iter().map(|c| c.variables()).collect();

            // Check if all children have the same variables (common case)
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
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        self.size() == other.size()
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
            | FloatOp::If(_, a, _) => a.size(),
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
            | FloatOp::If(_, a, _) => a.sort(),
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
