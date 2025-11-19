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

    fn check_same_sort(&self, _: &Self) -> bool {
        true
    }
}
