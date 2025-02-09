use std::collections::HashSet;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum FloatOp<'c> {
    FPS(String, FSort),
    FPV(Float),
    FpNeg(FloatAst<'c>, FPRM),
    FpAbs(FloatAst<'c>, FPRM),
    FpAdd(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSub(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpMul(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpDiv(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSqrt(FloatAst<'c>, FPRM),
    FpToFp(FloatAst<'c>, FSort, FPRM),
    BvToFpUnsigned(BitVecAst<'c>, FSort, FPRM),
    If(AstRef<'c, BooleanOp<'c>>, FloatAst<'c>, FloatAst<'c>),
    Annotated(FloatAst<'c>, Annotation),
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
            FloatOp::FpNeg(a, rm) => {
                2.hash(state);
                a.hash(state);
                rm.hash(state);
            }
            FloatOp::FpAbs(a, rm) => {
                3.hash(state);
                a.hash(state);
                rm.hash(state);
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
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                10.hash(state);
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            FloatOp::If(a, b, c) => {
                11.hash(state);
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
            FloatOp::Annotated(a, anno) => {
                12.hash(state);
                a.hash(state);
                anno.hash(state);
            }
        }
    }
}

impl<'c> Op<'c> for FloatOp<'c> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        match self {
            FloatOp::FPS(_, _) | FloatOp::FPV(_) => vec![].into_iter(),

            FloatOp::FpNeg(a, _)
            | FloatOp::FpAbs(a, _)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpToFp(a, _, _)
            | FloatOp::Annotated(a, _) => vec![a.into()].into_iter(),
            FloatOp::BvToFpUnsigned(a, _, _) => vec![a.into()].into_iter(),

            FloatOp::FpAdd(a, b, _)
            | FloatOp::FpSub(a, b, _)
            | FloatOp::FpMul(a, b, _)
            | FloatOp::FpDiv(a, b, _) => vec![a.into(), b.into()].into_iter(),
            FloatOp::If(a, b, c) => vec![a.into(), b.into(), c.into()].into_iter(),
        }
    }

    fn variables(&self) -> HashSet<String> {
        if let FloatOp::FPS(s, _) = self {
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
        if let FloatOp::Annotated(inner, anno) = self {
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

pub trait FloatExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> FloatExt<'c> for FloatAst<'c> {
    fn size(&self) -> u32 {
        match self.op() {
            FloatOp::FPS(_, sort) => sort.size(),
            FloatOp::FPV(value) => value.fsort().size(),
            FloatOp::FpNeg(a, _)
            | FloatOp::FpAbs(a, _)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpAdd(a, _, _)
            | FloatOp::FpSub(a, _, _)
            | FloatOp::FpMul(a, _, _)
            | FloatOp::FpDiv(a, _, _)
            | FloatOp::If(_, a, _)
            | FloatOp::Annotated(a, _) => a.size(),
            FloatOp::FpToFp(_, sort, _) | FloatOp::BvToFpUnsigned(_, sort, _) => sort.size(),
        }
    }
}
