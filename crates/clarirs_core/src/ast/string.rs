use std::collections::BTreeSet;
use std::sync::Arc;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum StringOp<'c> {
    StringS(InternedString),
    StringV(String),
    StrConcat(StringAst<'c>, StringAst<'c>),
    StrSubstr(StringAst<'c>, BitVecAst<'c>, BitVecAst<'c>),
    StrReplace(StringAst<'c>, StringAst<'c>, StringAst<'c>),
    BVToStr(BitVecAst<'c>),
    If(AstRef<'c, BooleanOp<'c>>, StringAst<'c>, StringAst<'c>),
}

pub type StringAst<'c> = AstRef<'c, StringOp<'c>>;

impl std::hash::Hash for StringOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "string".hash(state);
        match self {
            StringOp::StringS(s) => {
                0.hash(state);
                s.hash(state);
            }
            StringOp::StringV(s) => {
                1.hash(state);
                s.hash(state);
            }
            StringOp::StrConcat(a, b) => {
                2.hash(state);
                a.hash(state);
                b.hash(state);
            }
            StringOp::StrSubstr(a, b, c) => {
                3.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            StringOp::StrReplace(a, b, c) => {
                4.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            StringOp::BVToStr(a) => {
                5.hash(state);
                a.hash(state);
            }
            StringOp::If(a, b, c) => {
                6.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for StringOp<'c> {
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        match self {
            StringOp::StringS(..) | StringOp::StringV(..) => vec![],

            StringOp::BVToStr(a) => vec![a.into()],

            StringOp::StrConcat(a, b) => vec![a.into(), b.into()],

            StringOp::StrSubstr(a, b, c) => vec![a.into(), b.into(), c.into()],
            StringOp::StrReplace(a, b, c) => vec![a.into(), b.into(), c.into()],

            StringOp::If(a, b, c) => vec![a.into(), b.into(), c.into()],
        }
        .into_iter()
    }

    fn variables(&self) -> Arc<BTreeSet<InternedString>> {
        if let StringOp::StringS(s) = self {
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
