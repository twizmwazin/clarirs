use std::collections::BTreeSet;

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

pub struct StringOpChildIter<'a, 'c> {
    op: &'a StringOp<'c>,
    index: u8,
}

impl<'c> StringOp<'c> {
    pub fn child_iter(&self) -> StringOpChildIter<'_, 'c> {
        StringOpChildIter { op: self, index: 0 }
    }
}

impl<'a, 'c> Iterator for StringOpChildIter<'a, 'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = match (self.op, self.index) {
            // 0 children
            (StringOp::StringS(_), _) | (StringOp::StringV(_), _) => None,

            // 1 child variants - index 0
            (StringOp::BVToStr(a), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (StringOp::StrConcat(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (StringOp::StrConcat(_, b), 1) => Some(b.into()),

            // 3 child variants - StrSubstr(str, start, len)
            (StringOp::StrSubstr(a, _, _), 0) => Some(a.into()),
            (StringOp::StrSubstr(_, b, _), 1) => Some(b.into()),
            (StringOp::StrSubstr(_, _, c), 2) => Some(c.into()),

            // 3 child variants - StrReplace(str, from, to)
            (StringOp::StrReplace(a, _, _), 0) => Some(a.into()),
            (StringOp::StrReplace(_, b, _), 1) => Some(b.into()),
            (StringOp::StrReplace(_, _, c), 2) => Some(c.into()),

            // 3 child variants - If(cond, then, else)
            (StringOp::If(a, _, _), 0) => Some(a.into()),
            (StringOp::If(_, b, _), 1) => Some(b.into()),
            (StringOp::If(_, _, c), 2) => Some(c.into()),

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

impl<'a, 'c> ExactSizeIterator for StringOpChildIter<'a, 'c> {
    fn len(&self) -> usize {
        let total: usize = match self.op {
            StringOp::StringS(_) | StringOp::StringV(_) => 0,
            StringOp::BVToStr(_) => 1,
            StringOp::StrConcat(..) => 2,
            StringOp::StrSubstr(..) | StringOp::StrReplace(..) | StringOp::If(..) => 3,
        };
        total.saturating_sub(self.index as usize)
    }
}

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
    type ChildIter<'a> = StringOpChildIter<'a, 'c> where Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
        StringOp::child_iter(self)
    }

    fn get_child(&self, index: usize) -> Option<DynAst<'c>> {
        match (self, index) {
            // 1 child variants - index 0
            (StringOp::BVToStr(a), 0) => Some(a.into()),

            // 2 child variants - index 0 (first child)
            (StringOp::StrConcat(a, _), 0) => Some(a.into()),

            // 2 child variants - index 1 (second child)
            (StringOp::StrConcat(_, b), 1) => Some(b.into()),

            // 3 child variants - StrSubstr(str, start, len)
            (StringOp::StrSubstr(a, _, _), 0) => Some(a.into()),
            (StringOp::StrSubstr(_, b, _), 1) => Some(b.into()),
            (StringOp::StrSubstr(_, _, c), 2) => Some(c.into()),

            // 3 child variants - StrReplace(str, from, to)
            (StringOp::StrReplace(a, _, _), 0) => Some(a.into()),
            (StringOp::StrReplace(_, b, _), 1) => Some(b.into()),
            (StringOp::StrReplace(_, _, c), 2) => Some(c.into()),

            // 3 child variants - If(cond, then, else)
            (StringOp::If(a, _, _), 0) => Some(a.into()),
            (StringOp::If(_, b, _), 1) => Some(b.into()),
            (StringOp::If(_, _, c), 2) => Some(c.into()),

            _ => None,
        }
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
