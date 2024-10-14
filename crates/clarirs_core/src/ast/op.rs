use serde::{de, Serialize};

use crate::prelude::*;

use crate::ast::node::{AstRef, OpTrait};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BooleanOp<'c> {
    BoolS(String),
    BoolV(bool),
    Not(AstRef<'c, BooleanOp<'c>>),
    And(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    Or(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    Xor(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    Eq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    Neq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    ULT(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    ULE(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    UGT(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    UGE(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    SLT(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    SLE(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    SGT(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    SGE(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpEq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpNeq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpLt(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpLeq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpGt(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpGeq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    FpIsNan(AstRef<'c, BooleanOp<'c>>),
    FpIsInf(AstRef<'c, BooleanOp<'c>>),
    StrContains(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    StrPrefixOf(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    StrSuffixOf(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    StrIsDigit(AstRef<'c, BooleanOp<'c>>),
    StrEq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    StrNeq(AstRef<'c, BooleanOp<'c>>, AstRef<'c, BooleanOp<'c>>),
    If(
        AstRef<'c, BooleanOp<'c>>,
        AstRef<'c, BooleanOp<'c>>,
        AstRef<'c, BooleanOp<'c>>,
    ),
    Annotated(AstRef<'c, BooleanOp<'c>>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum FloatOp<'c> {
    FPS(String, FSort),
    FPV(Float),
    FpNeg(AstRef<'c, FloatOp<'c>>, FPRM),
    FpAbs(AstRef<'c, FloatOp<'c>>, FPRM),
    FpAdd(AstRef<'c, FloatOp<'c>>, AstRef<'c, FloatOp<'c>>, FPRM),
    FpSub(AstRef<'c, FloatOp<'c>>, AstRef<'c, FloatOp<'c>>, FPRM),
    FpMul(AstRef<'c, FloatOp<'c>>, AstRef<'c, FloatOp<'c>>, FPRM),
    FpDiv(AstRef<'c, FloatOp<'c>>, AstRef<'c, FloatOp<'c>>, FPRM),
    FpSqrt(AstRef<'c, FloatOp<'c>>, FPRM),
    FpToFp(AstRef<'c, FloatOp<'c>>, FSort),
    BvToFpUnsigned(AstRef<'c, FloatOp<'c>>, FSort, FPRM),
    If(
        AstRef<'c, FloatOp<'c>>,
        AstRef<'c, FloatOp<'c>>,
        AstRef<'c, FloatOp<'c>>,
    ),
    Annotated(AstRef<'c, FloatOp<'c>>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BitVecOp<'c> {
    BVS(String, u32),
    BVV(BitVec),
    SI(String, BitVec, BitVec, BitVec, u32),
    Not(AstRef<'c, BitVecOp<'c>>),
    And(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Or(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Xor(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Add(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Sub(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Mul(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    UDiv(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    SDiv(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    URem(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    SRem(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Pow(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    LShL(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    LShR(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    AShL(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    AShR(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    RotateLeft(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    RotateRight(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    ZeroExt(AstRef<'c, BitVecOp<'c>>, u32),
    SignExt(AstRef<'c, BitVecOp<'c>>, u32),
    Extract(AstRef<'c, BitVecOp<'c>>, u32, u32),
    Concat(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    Reverse(AstRef<'c, BitVecOp<'c>>),
    FpToIEEEBV(AstRef<'c, BitVecOp<'c>>),
    FpToUBV(AstRef<'c, BitVecOp<'c>>, u32, FPRM),
    FpToSBV(AstRef<'c, BitVecOp<'c>>, u32, FPRM),
    StrLen(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>), // or StrLen(AstRef<'c, BitVecOp<'c>>, u32),
    StrIndexOf(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>),
    StrToBV(AstRef<'c, BitVecOp<'c>>, AstRef<'c, BitVecOp<'c>>), // StrToBV
    If(
        AstRef<'c, BitVecOp<'c>>,
        AstRef<'c, BitVecOp<'c>>,
        AstRef<'c, BitVecOp<'c>>,
    ),
    Annotated(AstRef<'c, BitVecOp<'c>>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum StringOp<'c> {
    StringS(String, u32),
    StringV(String),
    StrConcat(AstRef<'c, StringOp<'c>>, AstRef<'c, StringOp<'c>>), // StrConcat (Vec<AstRef<'c>>) To allow for any number of args,
    StrSubstr(
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
    ),
    StrReplace(
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
    ),
    BVToStr(AstRef<'c, StringOp<'c>>),
    If(
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
        AstRef<'c, StringOp<'c>>,
    ),
    Annotated(AstRef<'c, StringOp<'c>>, Annotation<'c>),
}

impl<'c> OpTrait<'c> for BooleanOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, BooleanOp<'c>>> + 'c> {
        match self {
            // Cases with no children
            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Box::new(std::iter::empty()),

            // Cases with one child
            BooleanOp::Not(a)
            | BooleanOp::FpIsNan(a)
            | BooleanOp::FpIsInf(a)
            | BooleanOp::StrIsDigit(a)
            | BooleanOp::Annotated(a, _) => Box::new(std::iter::once(a.clone())),

            // Cases with two children
            BooleanOp::And(a, b)
            | BooleanOp::Or(a, b)
            | BooleanOp::Xor(a, b)
            | BooleanOp::Eq(a, b)
            | BooleanOp::Neq(a, b)
            | BooleanOp::ULT(a, b)
            | BooleanOp::ULE(a, b)
            | BooleanOp::UGT(a, b)
            | BooleanOp::UGE(a, b)
            | BooleanOp::SLT(a, b)
            | BooleanOp::SLE(a, b)
            | BooleanOp::SGT(a, b)
            | BooleanOp::SGE(a, b)
            | BooleanOp::FpEq(a, b)
            | BooleanOp::FpNeq(a, b)
            | BooleanOp::FpLt(a, b)
            | BooleanOp::FpLeq(a, b)
            | BooleanOp::FpGt(a, b)
            | BooleanOp::FpGeq(a, b)
            | BooleanOp::StrContains(a, b)
            | BooleanOp::StrPrefixOf(a, b)
            | BooleanOp::StrSuffixOf(a, b)
            | BooleanOp::StrEq(a, b)
            | BooleanOp::StrNeq(a, b) => Box::new(vec![a.clone(), b.clone()].into_iter()),

            // Cases with three children
            BooleanOp::If(a, b, c) => Box::new(vec![a.clone(), b.clone(), c.clone()].into_iter()),
        }
    }

    fn is_true(&self) -> bool {
        matches!(self, BooleanOp::BoolV(true))
    }

    fn is_false(&self) -> bool {
        matches!(self, BooleanOp::BoolV(false))
    }
}

impl<'c> OpTrait<'c> for FloatOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, FloatOp<'c>>> + 'c> {
        match self {
            FloatOp::FPS(_, _) | FloatOp::FPV(_) => Box::new(std::iter::empty()),

            FloatOp::FpNeg(a, _)
            | FloatOp::FpAbs(a, _)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpToFp(a, _)
            | FloatOp::BvToFpUnsigned(a, _, _)
            | FloatOp::Annotated(a, _) => Box::new(std::iter::once(a.clone())),

            FloatOp::FpAdd(a, b, _)
            | FloatOp::FpSub(a, b, _)
            | FloatOp::FpMul(a, b, _)
            | FloatOp::FpDiv(a, b, _) => Box::new(vec![a.clone(), b.clone()].into_iter()),

            FloatOp::If(a, b, c) => Box::new(vec![a.clone(), b.clone(), c.clone()].into_iter()),
        }
    }
}

impl<'c> OpTrait<'c> for BitVecOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, BitVecOp<'c>>> + 'c> {
        match self {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => {
                Box::new(std::iter::empty())
            }

            BitVecOp::Not(a)
            | BitVecOp::Reverse(a)
            | BitVecOp::ZeroExt(a, _)
            | BitVecOp::SignExt(a, _)
            | BitVecOp::Extract(a, _, _)
            | BitVecOp::FpToIEEEBV(a)
            | BitVecOp::FpToUBV(a, _, _)
            | BitVecOp::FpToSBV(a, _, _)
            | BitVecOp::StrLen(a, _)
            | BitVecOp::StrToBV(a, _)
            | BitVecOp::Annotated(a, _) => Box::new(std::iter::once(a.clone())),

            BitVecOp::And(a, b)
            | BitVecOp::Or(a, b)
            | BitVecOp::Xor(a, b)
            | BitVecOp::Add(a, b)
            | BitVecOp::Sub(a, b)
            | BitVecOp::Mul(a, b)
            | BitVecOp::UDiv(a, b)
            | BitVecOp::SDiv(a, b)
            | BitVecOp::URem(a, b)
            | BitVecOp::SRem(a, b)
            | BitVecOp::Pow(a, b)
            | BitVecOp::LShL(a, b)
            | BitVecOp::LShR(a, b)
            | BitVecOp::AShL(a, b)
            | BitVecOp::AShR(a, b)
            | BitVecOp::RotateLeft(a, b)
            | BitVecOp::RotateRight(a, b)
            | BitVecOp::Concat(a, b)
            | BitVecOp::StrIndexOf(a, b) => Box::new(vec![a.clone(), b.clone()].into_iter()),

            BitVecOp::If(a, b, c) => Box::new(vec![a.clone(), b.clone(), c.clone()].into_iter()),
        }
    }
}

impl<'c> OpTrait<'c> for StringOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, StringOp<'c>>> + 'c> {
        match self {
            StringOp::StringS(..) | StringOp::StringV(..) => Box::new(std::iter::empty()),

            StringOp::BVToStr(a) | StringOp::Annotated(a, _) => {
                Box::new(std::iter::once(a.clone()))
            }

            StringOp::StrConcat(a, b) => Box::new(vec![a.clone(), b.clone()].into_iter()),

            StringOp::StrSubstr(a, b, c)
            | StringOp::StrReplace(a, b, c)
            | StringOp::If(a, b, c) => Box::new(vec![a.clone(), b.clone(), c.clone()].into_iter()),
        }
    }
}
