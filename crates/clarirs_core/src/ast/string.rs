use std::collections::HashSet;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum StringOp<'c> {
    StringS(String),
    StringV(String),
    StrConcat(StringAst<'c>, StringAst<'c>),
    StrSubstr(StringAst<'c>, BitVecAst<'c>, BitVecAst<'c>),
    StrReplace(StringAst<'c>, StringAst<'c>, StringAst<'c>),
    BVToStr(BitVecAst<'c>),
    If(AstRef<'c, BooleanOp<'c>>, StringAst<'c>, StringAst<'c>),
    Annotated(StringAst<'c>, Annotation),
}

pub type StringAst<'c> = AstRef<'c, StringOp<'c>>;

impl<'c> Op<'c> for StringOp<'c> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        match self {
            StringOp::StringS(..) | StringOp::StringV(..) => vec![],

            StringOp::BVToStr(a) => vec![a.into()],
            StringOp::Annotated(a, _) => vec![a.into()],

            StringOp::StrConcat(a, b) => vec![a.into(), b.into()],

            StringOp::StrSubstr(a, b, c) => vec![a.into(), b.into(), c.into()],
            StringOp::StrReplace(a, b, c) => vec![a.into(), b.into(), c.into()],

            StringOp::If(a, b, c) => vec![a.into(), b.into(), c.into()],
        }
        .into_iter()
    }

    fn variables(&self) -> HashSet<String> {
        if let StringOp::StringS(s) = self {
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
