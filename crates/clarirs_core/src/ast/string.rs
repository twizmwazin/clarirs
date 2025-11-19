use std::collections::BTreeSet;
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

    fn variables(&self) -> BTreeSet<InternedString> {
        if let StringOp::StringS(s) = self {
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
