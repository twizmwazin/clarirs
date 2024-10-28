use std::collections::HashSet;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
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
}
