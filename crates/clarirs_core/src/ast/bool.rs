use std::collections::BTreeSet;
use std::sync::Arc;
use std::vec::IntoIter;

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
    If(BoolAst<'c>, BoolAst<'c>, BoolAst<'c>),
}

pub type BoolAst<'c> = AstRef<'c, BooleanOp<'c>>;

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
            BooleanOp::If(a, b, c) => {
                32.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for BooleanOp<'c> {
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        match self {
            // Cases with no children
            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => vec![],

            // Cases with one child
            BooleanOp::Not(a) => vec![a.into()],

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

    fn variables(&self) -> Arc<BTreeSet<InternedString>> {
        if let BooleanOp::BoolS(s) = self {
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

    fn check_same_sort(&self, _: &Self) -> bool {
        true
    }
}
