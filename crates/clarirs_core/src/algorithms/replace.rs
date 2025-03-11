use std::mem::discriminant;

use crate::prelude::*;

pub trait Replace<'c, T> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError>
    where
        Self: Sized;
}

impl<'c> Replace<'c, BoolAst<'c>> for BoolAst<'c> {
    fn replace(&self, from: &BoolAst<'c>, to: &BoolAst<'c>) -> Result<Self, ClarirsError> {
        if self == from {
            Ok(to.clone())
        } else {
            match self.op() {
                BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(self.clone()),
                BooleanOp::Not(a) => {
                    let replaced = a.replace(from, to)?;
                    self.context().make_bool(BooleanOp::Not(replaced))
                }
                BooleanOp::And(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::And(a_replaced, b_replaced))
                }
                BooleanOp::Or(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::Or(a_replaced, b_replaced))
                }
                BooleanOp::Xor(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::Xor(a_replaced, b_replaced))
                }
                BooleanOp::BoolEq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::BoolEq(a_replaced, b_replaced))
                }
                BooleanOp::BoolNeq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::BoolNeq(a_replaced, b_replaced))
                }
                BooleanOp::Eq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::Eq(a_replaced, b_replaced))
                }
                BooleanOp::Neq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::Neq(a_replaced, b_replaced))
                }
                BooleanOp::ULT(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::ULT(a_replaced, b_replaced))
                }
                BooleanOp::ULE(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::ULE(a_replaced, b_replaced))
                }
                BooleanOp::UGT(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::UGT(a_replaced, b_replaced))
                }
                BooleanOp::UGE(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::UGE(a_replaced, b_replaced))
                }
                BooleanOp::SLT(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::SLT(a_replaced, b_replaced))
                }
                BooleanOp::SLE(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::SLE(a_replaced, b_replaced))
                }
                BooleanOp::SGT(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::SGT(a_replaced, b_replaced))
                }
                BooleanOp::SGE(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::SGE(a_replaced, b_replaced))
                }
                BooleanOp::FpEq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpEq(a_replaced, b_replaced))
                }
                BooleanOp::FpNeq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpNeq(a_replaced, b_replaced))
                }
                BooleanOp::FpLt(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpLt(a_replaced, b_replaced))
                }
                BooleanOp::FpLeq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpLeq(a_replaced, b_replaced))
                }
                BooleanOp::FpGt(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpGt(a_replaced, b_replaced))
                }
                BooleanOp::FpGeq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::FpGeq(a_replaced, b_replaced))
                }
                BooleanOp::FpIsNan(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bool(BooleanOp::FpIsNan(a_replaced))
                }
                BooleanOp::FpIsInf(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bool(BooleanOp::FpIsInf(a_replaced))
                }
                BooleanOp::StrContains(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::StrContains(a_replaced, b_replaced))
                }
                BooleanOp::StrPrefixOf(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::StrPrefixOf(a_replaced, b_replaced))
                }
                BooleanOp::StrSuffixOf(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::StrSuffixOf(a_replaced, b_replaced))
                }
                BooleanOp::StrIsDigit(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bool(BooleanOp::StrIsDigit(a_replaced))
                }
                BooleanOp::StrEq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::StrEq(a_replaced, b_replaced))
                }
                BooleanOp::StrNeq(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::StrNeq(a_replaced, b_replaced))
                }
                BooleanOp::If(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::If(a_replaced, b_replaced, c_replaced))
                }
                BooleanOp::Annotated(a, anno) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bool(BooleanOp::Annotated(a_replaced, anno.clone()))
                }
            }
        }
    }
}

impl<'c> Replace<'c, BitVecAst<'c>> for BoolAst<'c> {
    fn replace(&self, from: &BitVecAst<'c>, to: &BitVecAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(self.clone()),
            BooleanOp::Not(a) => {
                let replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::Not(replaced))
            }
            BooleanOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::And(a_replaced, b_replaced))
            }
            BooleanOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Or(a_replaced, b_replaced))
            }
            BooleanOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Xor(a_replaced, b_replaced))
            }
            BooleanOp::BoolEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolEq(a_replaced, b_replaced))
            }
            BooleanOp::BoolNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolNeq(a_replaced, b_replaced))
            }
            BooleanOp::Eq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Eq(a_replaced, b_replaced))
            }
            BooleanOp::Neq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Neq(a_replaced, b_replaced))
            }
            BooleanOp::ULT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULT(a_replaced, b_replaced))
            }
            BooleanOp::ULE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULE(a_replaced, b_replaced))
            }
            BooleanOp::UGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGT(a_replaced, b_replaced))
            }
            BooleanOp::UGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGE(a_replaced, b_replaced))
            }
            BooleanOp::SLT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLT(a_replaced, b_replaced))
            }
            BooleanOp::SLE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLE(a_replaced, b_replaced))
            }
            BooleanOp::SGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGT(a_replaced, b_replaced))
            }
            BooleanOp::SGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGE(a_replaced, b_replaced))
            }
            BooleanOp::FpEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpEq(a_replaced, b_replaced))
            }
            BooleanOp::FpNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpNeq(a_replaced, b_replaced))
            }
            BooleanOp::FpLt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLt(a_replaced, b_replaced))
            }
            BooleanOp::FpLeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLeq(a_replaced, b_replaced))
            }
            BooleanOp::FpGt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGt(a_replaced, b_replaced))
            }
            BooleanOp::FpGeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGeq(a_replaced, b_replaced))
            }
            BooleanOp::FpIsNan(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsNan(a_replaced))
            }
            BooleanOp::FpIsInf(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsInf(a_replaced))
            }
            BooleanOp::StrContains(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrContains(a_replaced, b_replaced))
            }
            BooleanOp::StrPrefixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrPrefixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrSuffixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrSuffixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrIsDigit(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::StrIsDigit(a_replaced))
            }
            BooleanOp::StrEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrEq(a_replaced, b_replaced))
            }
            BooleanOp::StrNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrNeq(a_replaced, b_replaced))
            }
            BooleanOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::If(a_replaced, b_replaced, c_replaced))
            }
            BooleanOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, FloatAst<'c>> for BoolAst<'c> {
    fn replace(&self, from: &FloatAst<'c>, to: &FloatAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(self.clone()),
            BooleanOp::Not(a) => {
                let replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::Not(replaced))
            }
            BooleanOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::And(a_replaced, b_replaced))
            }
            BooleanOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Or(a_replaced, b_replaced))
            }
            BooleanOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Xor(a_replaced, b_replaced))
            }
            BooleanOp::BoolEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolEq(a_replaced, b_replaced))
            }
            BooleanOp::BoolNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolNeq(a_replaced, b_replaced))
            }
            BooleanOp::Eq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Eq(a_replaced, b_replaced))
            }
            BooleanOp::Neq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Neq(a_replaced, b_replaced))
            }
            BooleanOp::ULT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULT(a_replaced, b_replaced))
            }
            BooleanOp::ULE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULE(a_replaced, b_replaced))
            }
            BooleanOp::UGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGT(a_replaced, b_replaced))
            }
            BooleanOp::UGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGE(a_replaced, b_replaced))
            }
            BooleanOp::SLT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLT(a_replaced, b_replaced))
            }
            BooleanOp::SLE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLE(a_replaced, b_replaced))
            }
            BooleanOp::SGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGT(a_replaced, b_replaced))
            }
            BooleanOp::SGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGE(a_replaced, b_replaced))
            }
            BooleanOp::FpEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpEq(a_replaced, b_replaced))
            }
            BooleanOp::FpNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpNeq(a_replaced, b_replaced))
            }
            BooleanOp::FpLt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLt(a_replaced, b_replaced))
            }
            BooleanOp::FpLeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLeq(a_replaced, b_replaced))
            }
            BooleanOp::FpGt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGt(a_replaced, b_replaced))
            }
            BooleanOp::FpGeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGeq(a_replaced, b_replaced))
            }
            BooleanOp::FpIsNan(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsNan(a_replaced))
            }
            BooleanOp::FpIsInf(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsInf(a_replaced))
            }
            BooleanOp::StrContains(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrContains(a_replaced, b_replaced))
            }
            BooleanOp::StrPrefixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrPrefixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrSuffixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrSuffixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrIsDigit(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::StrIsDigit(a_replaced))
            }
            BooleanOp::StrEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrEq(a_replaced, b_replaced))
            }
            BooleanOp::StrNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrNeq(a_replaced, b_replaced))
            }
            BooleanOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::If(a_replaced, b_replaced, c_replaced))
            }
            BooleanOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, StringAst<'c>> for BoolAst<'c> {
    fn replace(&self, from: &StringAst<'c>, to: &StringAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(self.clone()),
            BooleanOp::Not(a) => {
                let replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::Not(replaced))
            }
            BooleanOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::And(a_replaced, b_replaced))
            }
            BooleanOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Or(a_replaced, b_replaced))
            }
            BooleanOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Xor(a_replaced, b_replaced))
            }
            BooleanOp::BoolEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolEq(a_replaced, b_replaced))
            }
            BooleanOp::BoolNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::BoolNeq(a_replaced, b_replaced))
            }
            BooleanOp::Eq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Eq(a_replaced, b_replaced))
            }
            BooleanOp::Neq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Neq(a_replaced, b_replaced))
            }
            BooleanOp::ULT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULT(a_replaced, b_replaced))
            }
            BooleanOp::ULE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::ULE(a_replaced, b_replaced))
            }
            BooleanOp::UGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGT(a_replaced, b_replaced))
            }
            BooleanOp::UGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::UGE(a_replaced, b_replaced))
            }
            BooleanOp::SLT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLT(a_replaced, b_replaced))
            }
            BooleanOp::SLE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SLE(a_replaced, b_replaced))
            }
            BooleanOp::SGT(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGT(a_replaced, b_replaced))
            }
            BooleanOp::SGE(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::SGE(a_replaced, b_replaced))
            }
            BooleanOp::FpEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpEq(a_replaced, b_replaced))
            }
            BooleanOp::FpNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpNeq(a_replaced, b_replaced))
            }
            BooleanOp::FpLt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLt(a_replaced, b_replaced))
            }
            BooleanOp::FpLeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpLeq(a_replaced, b_replaced))
            }
            BooleanOp::FpGt(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGt(a_replaced, b_replaced))
            }
            BooleanOp::FpGeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::FpGeq(a_replaced, b_replaced))
            }
            BooleanOp::FpIsNan(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsNan(a_replaced))
            }
            BooleanOp::FpIsInf(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::FpIsInf(a_replaced))
            }
            BooleanOp::StrContains(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrContains(a_replaced, b_replaced))
            }
            BooleanOp::StrPrefixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrPrefixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrSuffixOf(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrSuffixOf(a_replaced, b_replaced))
            }
            BooleanOp::StrIsDigit(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bool(BooleanOp::StrIsDigit(a_replaced))
            }
            BooleanOp::StrEq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrEq(a_replaced, b_replaced))
            }
            BooleanOp::StrNeq(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::StrNeq(a_replaced, b_replaced))
            }
            BooleanOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::If(a_replaced, b_replaced, c_replaced))
            }
            BooleanOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bool(BooleanOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, BoolAst<'c>> for BitVecAst<'c> {
    fn replace(&self, from: &BoolAst<'c>, to: &BoolAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => Ok(self.clone()),
            BitVecOp::Not(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Not(a_replaced))
            }
            BitVecOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::And(a_replaced, b_replaced))
            }
            BitVecOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Or(a_replaced, b_replaced))
            }
            BitVecOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Xor(a_replaced, b_replaced))
            }
            BitVecOp::Neg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Neg(a_replaced))
            }
            BitVecOp::Abs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Abs(a_replaced))
            }
            BitVecOp::Add(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Add(a_replaced, b_replaced))
            }
            BitVecOp::Sub(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Sub(a_replaced, b_replaced))
            }
            BitVecOp::Mul(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Mul(a_replaced, b_replaced))
            }
            BitVecOp::UDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::UDiv(a_replaced, b_replaced))
            }
            BitVecOp::SDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SDiv(a_replaced, b_replaced))
            }
            BitVecOp::URem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::URem(a_replaced, b_replaced))
            }
            BitVecOp::SRem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SRem(a_replaced, b_replaced))
            }
            BitVecOp::Pow(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Pow(a_replaced, b_replaced))
            }
            BitVecOp::ShL(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ShL(a_replaced, b_replaced))
            }
            BitVecOp::LShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::LShR(a_replaced, b_replaced))
            }
            BitVecOp::AShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::AShR(a_replaced, b_replaced))
            }
            BitVecOp::RotateLeft(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateLeft(a_replaced, b_replaced))
            }
            BitVecOp::RotateRight(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateRight(a_replaced, b_replaced))
            }
            BitVecOp::ZeroExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ZeroExt(a_replaced, *size))
            }
            BitVecOp::SignExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SignExt(a_replaced, *size))
            }
            BitVecOp::Extract(a, high, low) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Extract(a_replaced, *high, *low))
            }
            BitVecOp::Concat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Concat(a_replaced, b_replaced))
            }
            BitVecOp::Reverse(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Reverse(a_replaced))
            }
            BitVecOp::FpToIEEEBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::FpToIEEEBV(a_replaced))
            }
            BitVecOp::FpToUBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToUBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::FpToSBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToSBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::StrLen(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrLen(a_replaced))
            }
            BitVecOp::StrIndexOf(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::StrIndexOf(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::StrToBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrToBV(a_replaced))
            }
            BitVecOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::If(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Annotated(a_replaced, anno.clone()))
            }
            BitVecOp::Union(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Union(a_replaced, b_replaced))
            }
            BitVecOp::Intersection(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Intersection(a_replaced, b_replaced))
            }
        }
    }
}

impl<'c> Replace<'c, BitVecAst<'c>> for BitVecAst<'c> {
    fn replace(&self, from: &BitVecAst<'c>, to: &BitVecAst<'c>) -> Result<Self, ClarirsError> {
        if self == from {
            Ok(to.clone())
        } else {
            match self.op() {
                BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => Ok(self.clone()),
                BitVecOp::Not(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::Not(a_replaced))
                }
                BitVecOp::And(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::And(a_replaced, b_replaced))
                }
                BitVecOp::Or(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Or(a_replaced, b_replaced))
                }
                BitVecOp::Xor(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Xor(a_replaced, b_replaced))
                }
                BitVecOp::Neg(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::Neg(a_replaced))
                }
                BitVecOp::Abs(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::Abs(a_replaced))
                }
                BitVecOp::Add(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Add(a_replaced, b_replaced))
                }
                BitVecOp::Sub(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Sub(a_replaced, b_replaced))
                }
                BitVecOp::Mul(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Mul(a_replaced, b_replaced))
                }
                BitVecOp::UDiv(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::UDiv(a_replaced, b_replaced))
                }
                BitVecOp::SDiv(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::SDiv(a_replaced, b_replaced))
                }
                BitVecOp::URem(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::URem(a_replaced, b_replaced))
                }
                BitVecOp::SRem(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::SRem(a_replaced, b_replaced))
                }
                BitVecOp::Pow(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Pow(a_replaced, b_replaced))
                }
                BitVecOp::ShL(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::ShL(a_replaced, b_replaced))
                }
                BitVecOp::LShR(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::LShR(a_replaced, b_replaced))
                }
                BitVecOp::AShR(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::AShR(a_replaced, b_replaced))
                }
                BitVecOp::RotateLeft(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::RotateLeft(a_replaced, b_replaced))
                }
                BitVecOp::RotateRight(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::RotateRight(a_replaced, b_replaced))
                }
                BitVecOp::ZeroExt(a, size) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::ZeroExt(a_replaced, *size))
                }
                BitVecOp::SignExt(a, size) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::SignExt(a_replaced, *size))
                }
                BitVecOp::Extract(a, high, low) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Extract(a_replaced, *high, *low))
                }
                BitVecOp::Concat(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Concat(a_replaced, b_replaced))
                }
                BitVecOp::Reverse(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::Reverse(a_replaced))
                }
                BitVecOp::FpToIEEEBV(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::FpToIEEEBV(a_replaced))
                }
                BitVecOp::FpToUBV(a, size, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::FpToUBV(a_replaced, *size, rm.clone()))
                }
                BitVecOp::FpToSBV(a, size, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::FpToSBV(a_replaced, *size, rm.clone()))
                }
                BitVecOp::StrLen(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::StrLen(a_replaced))
                }
                BitVecOp::StrIndexOf(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::StrIndexOf(a_replaced, b_replaced, c_replaced))
                }
                BitVecOp::StrToBV(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_bitvec(BitVecOp::StrToBV(a_replaced))
                }
                BitVecOp::If(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::If(a_replaced, b_replaced, c_replaced))
                }
                BitVecOp::Annotated(a, anno) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Annotated(a_replaced, anno.clone()))
                }
                BitVecOp::Union(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Union(a_replaced, b_replaced))
                }
                BitVecOp::Intersection(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_bitvec(BitVecOp::Intersection(a_replaced, b_replaced))
                }
            }
        }
    }
}

impl<'c> Replace<'c, FloatAst<'c>> for BitVecAst<'c> {
    fn replace(&self, from: &FloatAst<'c>, to: &FloatAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => Ok(self.clone()),
            BitVecOp::Not(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Not(a_replaced))
            }
            BitVecOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::And(a_replaced, b_replaced))
            }
            BitVecOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Or(a_replaced, b_replaced))
            }
            BitVecOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Xor(a_replaced, b_replaced))
            }
            BitVecOp::Neg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Neg(a_replaced))
            }
            BitVecOp::Abs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Abs(a_replaced))
            }
            BitVecOp::Add(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Add(a_replaced, b_replaced))
            }
            BitVecOp::Sub(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Sub(a_replaced, b_replaced))
            }
            BitVecOp::Mul(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Mul(a_replaced, b_replaced))
            }
            BitVecOp::UDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::UDiv(a_replaced, b_replaced))
            }
            BitVecOp::SDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SDiv(a_replaced, b_replaced))
            }
            BitVecOp::URem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::URem(a_replaced, b_replaced))
            }
            BitVecOp::SRem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SRem(a_replaced, b_replaced))
            }
            BitVecOp::Pow(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Pow(a_replaced, b_replaced))
            }
            BitVecOp::ShL(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ShL(a_replaced, b_replaced))
            }
            BitVecOp::LShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::LShR(a_replaced, b_replaced))
            }
            BitVecOp::AShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::AShR(a_replaced, b_replaced))
            }
            BitVecOp::RotateLeft(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateLeft(a_replaced, b_replaced))
            }
            BitVecOp::RotateRight(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateRight(a_replaced, b_replaced))
            }
            BitVecOp::ZeroExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ZeroExt(a_replaced, *size))
            }
            BitVecOp::SignExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SignExt(a_replaced, *size))
            }
            BitVecOp::Extract(a, high, low) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Extract(a_replaced, *high, *low))
            }
            BitVecOp::Concat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Concat(a_replaced, b_replaced))
            }
            BitVecOp::Reverse(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Reverse(a_replaced))
            }
            BitVecOp::FpToIEEEBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::FpToIEEEBV(a_replaced))
            }
            BitVecOp::FpToUBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToUBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::FpToSBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToSBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::StrLen(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrLen(a_replaced))
            }
            BitVecOp::StrIndexOf(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::StrIndexOf(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::StrToBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrToBV(a_replaced))
            }
            BitVecOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::If(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Annotated(a_replaced, anno.clone()))
            }
            BitVecOp::Union(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Union(a_replaced, b_replaced))
            }
            BitVecOp::Intersection(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Intersection(a_replaced, b_replaced))
            }
        }
    }
}

impl<'c> Replace<'c, StringAst<'c>> for BitVecAst<'c> {
    fn replace(&self, from: &StringAst<'c>, to: &StringAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => Ok(self.clone()),
            BitVecOp::Not(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Not(a_replaced))
            }
            BitVecOp::And(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::And(a_replaced, b_replaced))
            }
            BitVecOp::Or(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Or(a_replaced, b_replaced))
            }
            BitVecOp::Xor(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Xor(a_replaced, b_replaced))
            }
            BitVecOp::Neg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Neg(a_replaced))
            }
            BitVecOp::Abs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Abs(a_replaced))
            }
            BitVecOp::Add(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Add(a_replaced, b_replaced))
            }
            BitVecOp::Sub(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Sub(a_replaced, b_replaced))
            }
            BitVecOp::Mul(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Mul(a_replaced, b_replaced))
            }
            BitVecOp::UDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::UDiv(a_replaced, b_replaced))
            }
            BitVecOp::SDiv(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SDiv(a_replaced, b_replaced))
            }
            BitVecOp::URem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::URem(a_replaced, b_replaced))
            }
            BitVecOp::SRem(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SRem(a_replaced, b_replaced))
            }
            BitVecOp::Pow(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Pow(a_replaced, b_replaced))
            }
            BitVecOp::ShL(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ShL(a_replaced, b_replaced))
            }
            BitVecOp::LShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::LShR(a_replaced, b_replaced))
            }
            BitVecOp::AShR(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::AShR(a_replaced, b_replaced))
            }
            BitVecOp::RotateLeft(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateLeft(a_replaced, b_replaced))
            }
            BitVecOp::RotateRight(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::RotateRight(a_replaced, b_replaced))
            }
            BitVecOp::ZeroExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::ZeroExt(a_replaced, *size))
            }
            BitVecOp::SignExt(a, size) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::SignExt(a_replaced, *size))
            }
            BitVecOp::Extract(a, high, low) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Extract(a_replaced, *high, *low))
            }
            BitVecOp::Concat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Concat(a_replaced, b_replaced))
            }
            BitVecOp::Reverse(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::Reverse(a_replaced))
            }
            BitVecOp::FpToIEEEBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::FpToIEEEBV(a_replaced))
            }
            BitVecOp::FpToUBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToUBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::FpToSBV(a, size, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::FpToSBV(a_replaced, *size, rm.clone()))
            }
            BitVecOp::StrLen(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrLen(a_replaced))
            }
            BitVecOp::StrIndexOf(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::StrIndexOf(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::StrToBV(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_bitvec(BitVecOp::StrToBV(a_replaced))
            }
            BitVecOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::If(a_replaced, b_replaced, c_replaced))
            }
            BitVecOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Annotated(a_replaced, anno.clone()))
            }
            BitVecOp::Union(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Union(a_replaced, b_replaced))
            }
            BitVecOp::Intersection(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_bitvec(BitVecOp::Intersection(a_replaced, b_replaced))
            }
        }
    }
}

impl<'c> Replace<'c, BoolAst<'c>> for FloatAst<'c> {
    fn replace(&self, from: &BoolAst<'c>, to: &BoolAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(self.clone()),
            FloatOp::FpNeg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpNeg(a_replaced))
            }
            FloatOp::FpAbs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpAbs(a_replaced))
            }
            FloatOp::FpAdd(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpAdd(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSub(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSub(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpMul(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpMul(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpDiv(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpDiv(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSqrt(a, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSqrt(a_replaced, rm.clone()))
            }
            FloatOp::FpToFp(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpToFp(a_replaced, sort.clone(), rm.clone()))
            }
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::BvToFpUnsigned(
                    a_replaced,
                    sort.clone(),
                    rm.clone(),
                ))
            }
            FloatOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::If(a_replaced, b_replaced, c_replaced))
            }
            FloatOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, BitVecAst<'c>> for FloatAst<'c> {
    fn replace(&self, from: &BitVecAst<'c>, to: &BitVecAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(self.clone()),
            FloatOp::FpNeg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpNeg(a_replaced))
            }
            FloatOp::FpAbs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpAbs(a_replaced))
            }
            FloatOp::FpAdd(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpAdd(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSub(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSub(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpMul(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpMul(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpDiv(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpDiv(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSqrt(a, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSqrt(a_replaced, rm.clone()))
            }
            FloatOp::FpToFp(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpToFp(a_replaced, sort.clone(), rm.clone()))
            }
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::BvToFpUnsigned(
                    a_replaced,
                    sort.clone(),
                    rm.clone(),
                ))
            }
            FloatOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::If(a_replaced, b_replaced, c_replaced))
            }
            FloatOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, FloatAst<'c>> for FloatAst<'c> {
    fn replace(&self, from: &FloatAst<'c>, to: &FloatAst<'c>) -> Result<Self, ClarirsError> {
        if self == from {
            Ok(to.clone())
        } else {
            match self.op() {
                FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(self.clone()),
                FloatOp::FpNeg(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_float(FloatOp::FpNeg(a_replaced))
                }
                FloatOp::FpAbs(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_float(FloatOp::FpAbs(a_replaced))
                }
                FloatOp::FpAdd(a, b, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpAdd(a_replaced, b_replaced, rm.clone()))
                }
                FloatOp::FpSub(a, b, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpSub(a_replaced, b_replaced, rm.clone()))
                }
                FloatOp::FpMul(a, b, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpMul(a_replaced, b_replaced, rm.clone()))
                }
                FloatOp::FpDiv(a, b, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpDiv(a_replaced, b_replaced, rm.clone()))
                }
                FloatOp::FpSqrt(a, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpSqrt(a_replaced, rm.clone()))
                }
                FloatOp::FpToFp(a, sort, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::FpToFp(a_replaced, sort.clone(), rm.clone()))
                }
                FloatOp::BvToFpUnsigned(a, sort, rm) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_float(FloatOp::BvToFpUnsigned(
                        a_replaced,
                        sort.clone(),
                        rm.clone(),
                    ))
                }
                FloatOp::If(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::If(a_replaced, b_replaced, c_replaced))
                }
                FloatOp::Annotated(a, anno) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_float(FloatOp::Annotated(a_replaced, anno.clone()))
                }
            }
        }
    }
}

impl<'c> Replace<'c, StringAst<'c>> for FloatAst<'c> {
    fn replace(&self, from: &StringAst<'c>, to: &StringAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(self.clone()),
            FloatOp::FpNeg(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpNeg(a_replaced))
            }
            FloatOp::FpAbs(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::FpAbs(a_replaced))
            }
            FloatOp::FpAdd(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpAdd(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSub(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSub(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpMul(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpMul(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpDiv(a, b, rm) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpDiv(a_replaced, b_replaced, rm.clone()))
            }
            FloatOp::FpSqrt(a, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpSqrt(a_replaced, rm.clone()))
            }
            FloatOp::FpToFp(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::FpToFp(a_replaced, sort.clone(), rm.clone()))
            }
            FloatOp::BvToFpUnsigned(a, sort, rm) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_float(FloatOp::BvToFpUnsigned(
                    a_replaced,
                    sort.clone(),
                    rm.clone(),
                ))
            }
            FloatOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::If(a_replaced, b_replaced, c_replaced))
            }
            FloatOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_float(FloatOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, BoolAst<'c>> for StringAst<'c> {
    fn replace(&self, from: &BoolAst<'c>, to: &BoolAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            StringOp::StringS(..) | StringOp::StringV(..) => Ok(self.clone()),
            StringOp::StrConcat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrConcat(a_replaced, b_replaced))
            }
            StringOp::StrSubstr(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrSubstr(a_replaced, b_replaced, c_replaced))
            }
            StringOp::StrReplace(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrReplace(a_replaced, b_replaced, c_replaced))
            }
            StringOp::BVToStr(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_string(StringOp::BVToStr(a_replaced))
            }
            StringOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::If(a_replaced, b_replaced, c_replaced))
            }
            StringOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_string(StringOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, BitVecAst<'c>> for StringAst<'c> {
    fn replace(&self, from: &BitVecAst<'c>, to: &BitVecAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            StringOp::StringS(..) | StringOp::StringV(..) => Ok(self.clone()),
            StringOp::StrConcat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrConcat(a_replaced, b_replaced))
            }
            StringOp::StrSubstr(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrSubstr(a_replaced, b_replaced, c_replaced))
            }
            StringOp::StrReplace(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrReplace(a_replaced, b_replaced, c_replaced))
            }
            StringOp::BVToStr(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_string(StringOp::BVToStr(a_replaced))
            }
            StringOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::If(a_replaced, b_replaced, c_replaced))
            }
            StringOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_string(StringOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, FloatAst<'c>> for StringAst<'c> {
    fn replace(&self, from: &FloatAst<'c>, to: &FloatAst<'c>) -> Result<Self, ClarirsError> {
        match self.op() {
            StringOp::StringS(..) | StringOp::StringV(..) => Ok(self.clone()),
            StringOp::StrConcat(a, b) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrConcat(a_replaced, b_replaced))
            }
            StringOp::StrSubstr(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrSubstr(a_replaced, b_replaced, c_replaced))
            }
            StringOp::StrReplace(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::StrReplace(a_replaced, b_replaced, c_replaced))
            }
            StringOp::BVToStr(a) => {
                let a_replaced = a.replace(from, to)?;
                self.context().make_string(StringOp::BVToStr(a_replaced))
            }
            StringOp::If(a, b, c) => {
                let a_replaced = a.replace(from, to)?;
                let b_replaced = b.replace(from, to)?;
                let c_replaced = c.replace(from, to)?;
                self.context()
                    .make_string(StringOp::If(a_replaced, b_replaced, c_replaced))
            }
            StringOp::Annotated(a, anno) => {
                let a_replaced = a.replace(from, to)?;
                self.context()
                    .make_string(StringOp::Annotated(a_replaced, anno.clone()))
            }
        }
    }
}

impl<'c> Replace<'c, StringAst<'c>> for StringAst<'c> {
    fn replace(&self, from: &StringAst<'c>, to: &StringAst<'c>) -> Result<Self, ClarirsError> {
        if self == from {
            Ok(to.clone())
        } else {
            match self.op() {
                StringOp::StringS(..) | StringOp::StringV(..) => Ok(self.clone()),
                StringOp::StrConcat(a, b) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    self.context()
                        .make_string(StringOp::StrConcat(a_replaced, b_replaced))
                }
                StringOp::StrSubstr(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_string(StringOp::StrSubstr(a_replaced, b_replaced, c_replaced))
                }
                StringOp::StrReplace(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_string(StringOp::StrReplace(a_replaced, b_replaced, c_replaced))
                }
                StringOp::BVToStr(a) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context().make_string(StringOp::BVToStr(a_replaced))
                }
                StringOp::If(a, b, c) => {
                    let a_replaced = a.replace(from, to)?;
                    let b_replaced = b.replace(from, to)?;
                    let c_replaced = c.replace(from, to)?;
                    self.context()
                        .make_string(StringOp::If(a_replaced, b_replaced, c_replaced))
                }
                StringOp::Annotated(a, anno) => {
                    let a_replaced = a.replace(from, to)?;
                    self.context()
                        .make_string(StringOp::Annotated(a_replaced, anno.clone()))
                }
            }
        }
    }
}

// DynAst Imlementations

impl<'c> Replace<'c, BoolAst<'c>> for DynAst<'c> {
    fn replace(&self, from: &BoolAst<'c>, to: &BoolAst<'c>) -> Result<Self, ClarirsError> {
        match self {
            DynAst::Boolean(a) => a.replace(from, to).map(DynAst::Boolean),
            DynAst::BitVec(a) => a.replace(from, to).map(DynAst::BitVec),
            DynAst::Float(a) => a.replace(from, to).map(DynAst::Float),
            DynAst::String(a) => a.replace(from, to).map(DynAst::String),
        }
    }
}

impl<'c> Replace<'c, BitVecAst<'c>> for DynAst<'c> {
    fn replace(&self, from: &BitVecAst<'c>, to: &BitVecAst<'c>) -> Result<Self, ClarirsError> {
        match self {
            DynAst::Boolean(a) => a.replace(from, to).map(DynAst::Boolean),
            DynAst::BitVec(a) => a.replace(from, to).map(DynAst::BitVec),
            DynAst::Float(a) => a.replace(from, to).map(DynAst::Float),
            DynAst::String(a) => a.replace(from, to).map(DynAst::String),
        }
    }
}

impl<'c> Replace<'c, FloatAst<'c>> for DynAst<'c> {
    fn replace(&self, from: &FloatAst<'c>, to: &FloatAst<'c>) -> Result<Self, ClarirsError> {
        match self {
            DynAst::Boolean(a) => a.replace(from, to).map(DynAst::Boolean),
            DynAst::BitVec(a) => a.replace(from, to).map(DynAst::BitVec),
            DynAst::Float(a) => a.replace(from, to).map(DynAst::Float),
            DynAst::String(a) => a.replace(from, to).map(DynAst::String),
        }
    }
}

impl<'c> Replace<'c, StringAst<'c>> for DynAst<'c> {
    fn replace(&self, from: &StringAst<'c>, to: &StringAst<'c>) -> Result<Self, ClarirsError> {
        match self {
            DynAst::Boolean(a) => a.replace(from, to).map(DynAst::Boolean),
            DynAst::BitVec(a) => a.replace(from, to).map(DynAst::BitVec),
            DynAst::Float(a) => a.replace(from, to).map(DynAst::Float),
            DynAst::String(a) => a.replace(from, to).map(DynAst::String),
        }
    }
}

impl<'c> Replace<'c, DynAst<'c>> for BoolAst<'c> {
    fn replace(&self, from: &DynAst<'c>, to: &DynAst<'c>) -> Result<Self, ClarirsError> {
        if discriminant(from) != discriminant(to) {
            return Err(ClarirsError::TypeError(
                "Cannot replace different types".to_string(),
            ));
        }

        match from {
            DynAst::Boolean(from_) => self.replace(from_, to.as_bool().unwrap()),
            DynAst::BitVec(from_) => self.replace(from_, to.as_bitvec().unwrap()),
            DynAst::Float(from_) => self.replace(from_, to.as_float().unwrap()),
            DynAst::String(from_) => self.replace(from_, to.as_string().unwrap()),
        }
    }
}

impl<'c> Replace<'c, DynAst<'c>> for BitVecAst<'c> {
    fn replace(&self, from: &DynAst<'c>, to: &DynAst<'c>) -> Result<Self, ClarirsError> {
        if discriminant(from) != discriminant(to) {
            return Err(ClarirsError::TypeError(
                "Cannot replace different types".to_string(),
            ));
        }

        match from {
            DynAst::Boolean(from_) => self.replace(from_, to.as_bool().unwrap()),
            DynAst::BitVec(from_) => self.replace(from_, to.as_bitvec().unwrap()),
            DynAst::Float(from_) => self.replace(from_, to.as_float().unwrap()),
            DynAst::String(from_) => self.replace(from_, to.as_string().unwrap()),
        }
    }
}

impl<'c> Replace<'c, DynAst<'c>> for FloatAst<'c> {
    fn replace(&self, from: &DynAst<'c>, to: &DynAst<'c>) -> Result<Self, ClarirsError> {
        if discriminant(from) != discriminant(to) {
            return Err(ClarirsError::TypeError(
                "Cannot replace different types".to_string(),
            ));
        }

        match from {
            DynAst::Boolean(from_) => self.replace(from_, to.as_bool().unwrap()),
            DynAst::BitVec(from_) => self.replace(from_, to.as_bitvec().unwrap()),
            DynAst::Float(from_) => self.replace(from_, to.as_float().unwrap()),
            DynAst::String(from_) => self.replace(from_, to.as_string().unwrap()),
        }
    }
}

impl<'c> Replace<'c, DynAst<'c>> for StringAst<'c> {
    fn replace(&self, from: &DynAst<'c>, to: &DynAst<'c>) -> Result<Self, ClarirsError> {
        if discriminant(from) != discriminant(to) {
            return Err(ClarirsError::TypeError(
                "Cannot replace different types".to_string(),
            ));
        }

        match from {
            DynAst::Boolean(from_) => self.replace(from_, to.as_bool().unwrap()),
            DynAst::BitVec(from_) => self.replace(from_, to.as_bitvec().unwrap()),
            DynAst::Float(from_) => self.replace(from_, to.as_float().unwrap()),
            DynAst::String(from_) => self.replace(from_, to.as_string().unwrap()),
        }
    }
}

impl<'c> Replace<'c, DynAst<'c>> for DynAst<'c> {
    fn replace(&self, from: &DynAst<'c>, to: &DynAst<'c>) -> Result<Self, ClarirsError> {
        if discriminant(self) != discriminant(from) {
            return Err(ClarirsError::TypeError(
                "Cannot replace different types".to_string(),
            ));
        }

        if self == from {
            return Ok(to.clone());
        }

        match (self, from) {
            (DynAst::Boolean(self_), DynAst::Boolean(from_)) => self_
                .replace(from_, to.as_bool().unwrap())
                .map(DynAst::Boolean),
            (DynAst::Boolean(self_), DynAst::BitVec(from_)) => self_
                .replace(from_, to.as_bitvec().unwrap())
                .map(DynAst::Boolean),
            (DynAst::Boolean(self_), DynAst::Float(from_)) => self_
                .replace(from_, to.as_float().unwrap())
                .map(DynAst::Boolean),
            (DynAst::Boolean(self_), DynAst::String(from_)) => self_
                .replace(from_, to.as_string().unwrap())
                .map(DynAst::Boolean),
            (DynAst::BitVec(self_), DynAst::Boolean(from_)) => self_
                .replace(from_, to.as_bool().unwrap())
                .map(DynAst::BitVec),
            (DynAst::BitVec(self_), DynAst::BitVec(from_)) => self_
                .replace(from_, to.as_bitvec().unwrap())
                .map(DynAst::BitVec),
            (DynAst::BitVec(self_), DynAst::Float(from_)) => self_
                .replace(from_, to.as_float().unwrap())
                .map(DynAst::BitVec),
            (DynAst::BitVec(self_), DynAst::String(from_)) => self_
                .replace(from_, to.as_string().unwrap())
                .map(DynAst::BitVec),
            (DynAst::Float(self_), DynAst::Boolean(from_)) => self_
                .replace(from_, to.as_bool().unwrap())
                .map(DynAst::Float),
            (DynAst::Float(self_), DynAst::BitVec(from_)) => self_
                .replace(from_, to.as_bitvec().unwrap())
                .map(DynAst::Float),
            (DynAst::Float(self_), DynAst::Float(from_)) => self_
                .replace(from_, to.as_float().unwrap())
                .map(DynAst::Float),
            (DynAst::Float(self_), DynAst::String(from_)) => self_
                .replace(from_, to.as_string().unwrap())
                .map(DynAst::Float),
            (DynAst::String(self_), DynAst::Boolean(from_)) => self_
                .replace(from_, to.as_bool().unwrap())
                .map(DynAst::String),
            (DynAst::String(self_), DynAst::BitVec(from_)) => self_
                .replace(from_, to.as_bitvec().unwrap())
                .map(DynAst::String),
            (DynAst::String(self_), DynAst::Float(from_)) => self_
                .replace(from_, to.as_float().unwrap())
                .map(DynAst::String),
            (DynAst::String(self_), DynAst::String(from_)) => self_
                .replace(from_, to.as_string().unwrap())
                .map(DynAst::String),
        }
    }
}
