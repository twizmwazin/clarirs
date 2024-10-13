use serde::{de, Serialize};

use crate::prelude::*;

use crate::ast::node::{OpTrait, AstRef};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BooleanOp<'c> {
    BoolS(String),
    BoolV(bool),
    Not(AstRef<'c>),
    And(AstRef<'c>, AstRef<'c>),
    Or(AstRef<'c>, AstRef<'c>),
    Xor(AstRef<'c>, AstRef<'c>),
    Eq(AstRef<'c>, AstRef<'c>),
    Neq(AstRef<'c>, AstRef<'c>),
    ULT(AstRef<'c>, AstRef<'c>),
    ULE(AstRef<'c>, AstRef<'c>),
    UGT(AstRef<'c>, AstRef<'c>),
    UGE(AstRef<'c>, AstRef<'c>),
    SLT(AstRef<'c>, AstRef<'c>),
    SLE(AstRef<'c>, AstRef<'c>),
    SGT(AstRef<'c>, AstRef<'c>),
    SGE(AstRef<'c>, AstRef<'c>),
    FpEq(AstRef<'c>, AstRef<'c>),
    FpNeq(AstRef<'c>, AstRef<'c>),
    FpLt(AstRef<'c>, AstRef<'c>),
    FpLeq(AstRef<'c>, AstRef<'c>),
    FpGt(AstRef<'c>, AstRef<'c>),
    FpGeq(AstRef<'c>, AstRef<'c>),
    FpIsNan(AstRef<'c>),
    FpIsInf(AstRef<'c>),
    StrContains(AstRef<'c>, AstRef<'c>),
    StrPrefixOf(AstRef<'c>, AstRef<'c>),
    StrSuffixOf(AstRef<'c>, AstRef<'c>),
    StrIsDigit(AstRef<'c>),
    StrEq(AstRef<'c>, AstRef<'c>),
    StrNeq(AstRef<'c>, AstRef<'c>),
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    Annotated(AstRef<'c>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum FloatOp<'c> {
    FPS(String, FSort),
    FPV(Float),
    FpNeg(AstRef<'c>, FPRM),
    FpAbs(AstRef<'c>, FPRM),
    FpAdd(AstRef<'c>, AstRef<'c>, FPRM),
    FpSub(AstRef<'c>, AstRef<'c>, FPRM),
    FpMul(AstRef<'c>, AstRef<'c>, FPRM),
    FpDiv(AstRef<'c>, AstRef<'c>, FPRM),
    FpSqrt(AstRef<'c>, FPRM),
    FpToFp(AstRef<'c>, FSort),
    BvToFpUnsigned(AstRef<'c>, FSort, FPRM),
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    Annotated(AstRef<'c>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BitVecOp<'c> {
    BVS(String, u32),
    BVV(BitVec),
    SI(String, BitVec, BitVec, BitVec, u32),
    Not(AstRef<'c>),
    And(AstRef<'c>, AstRef<'c>),
    Or(AstRef<'c>, AstRef<'c>),
    Xor(AstRef<'c>, AstRef<'c>),
    Add(AstRef<'c>, AstRef<'c>),
    Sub(AstRef<'c>, AstRef<'c>),
    Mul(AstRef<'c>, AstRef<'c>),
    UDiv(AstRef<'c>, AstRef<'c>),
    SDiv(AstRef<'c>, AstRef<'c>),
    URem(AstRef<'c>, AstRef<'c>),
    SRem(AstRef<'c>, AstRef<'c>),
    Pow(AstRef<'c>, AstRef<'c>),
    LShL(AstRef<'c>, AstRef<'c>),
    LShR(AstRef<'c>, AstRef<'c>),
    AShL(AstRef<'c>, AstRef<'c>),
    AShR(AstRef<'c>, AstRef<'c>),
    RotateLeft(AstRef<'c>, AstRef<'c>),
    RotateRight(AstRef<'c>, AstRef<'c>),
    ZeroExt(AstRef<'c>, u32),
    SignExt(AstRef<'c>, u32),
    Extract(AstRef<'c>, u32, u32),
    Concat(AstRef<'c>, AstRef<'c>),
    Reverse(AstRef<'c>),
    FpToIEEEBV(AstRef<'c>),
    FpToUBV(AstRef<'c>, u32, FPRM),
    FpToSBV(AstRef<'c>, u32, FPRM),
    StrLen(AstRef<'c>, AstRef<'c>), // or StrLen(AstRef<'c>, u32),
    StrIndexOf(AstRef<'c>, AstRef<'c>),
    StrToBV(AstRef<'c>, AstRef<'c>), // StrToBV
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    Annotated(AstRef<'c>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum StringOp<'c> {
    StringS(String, u32),
    StringV(String),
    StrConcat(AstRef<'c>, AstRef<'c>), // StrConcat (Vec<AstRef<'c>>) To allow for any number of args,
    StrSubstr(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrReplace(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BVToStr(AstRef<'c>),
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    Annotated(AstRef<'c>, Annotation<'c>),
}

impl<'c> OpTrait<'c> for BooleanOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
        match self {
            // Cases with no children
            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Box::new(std::iter::empty()),

            // Cases with one child
            BooleanOp::Not(a)
            | BooleanOp::FpIsNan(a)
            | BooleanOp::FpIsInf(a)
            | BooleanOp::StrIsDigit(a)
            | BooleanOp::Annotated(a, _) => Box::new(std::iter::once(a)),

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
            | BooleanOp::StrNeq(a, b) => Box::new(vec![a, b].into_iter()),

            // Cases with three children
            BooleanOp::If(a, b, c) => Box::new(vec![a, b, c].into_iter()),
        }
    }

    fn children(&self) -> Vec<AstRef<'c>> {
        self.child_iter().cloned().collect()
    }

    // Override is_true and is_false
    fn is_true(&self) -> bool {
        matches!(self, BooleanOp::BoolV(true))
    }

    fn is_false(&self) -> bool {
        matches!(self, BooleanOp::BoolV(false))
    }
}

impl<'c> OpTrait<'c> for FloatOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
        match self {
            FloatOp::FPS(_, _) | FloatOp::FPV(_) => Box::new(std::iter::empty()),

            FloatOp::FpNeg(a, _)
            | FloatOp::FpAbs(a, _)
            | FloatOp::FpSqrt(a, _)
            | FloatOp::FpToFp(a, _)
            | FloatOp::BvToFpUnsigned(a, _, _)
            | FloatOp::Annotated(a, _) => Box::new(std::iter::once(a)),

            FloatOp::FpAdd(a, b, _)
            | FloatOp::FpSub(a, b, _)
            | FloatOp::FpMul(a, b, _)
            | FloatOp::FpDiv(a, b, _) => Box::new(vec![a, b].into_iter()),

            FloatOp::If(a, b, c) => Box::new(vec![a, b, c].into_iter()),
        }
    }

    fn children(&self) -> Vec<AstRef<'c>> {
        self.child_iter().cloned().collect()
    }
}

impl<'c> OpTrait<'c> for BitVecOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
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
            | BitVecOp::Annotated(a, _) => Box::new(std::iter::once(a)),

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
            | BitVecOp::StrIndexOf(a, b) => Box::new(vec![a, b].into_iter()),

            BitVecOp::If(a, b, c) => Box::new(vec![a, b, c].into_iter()),
        }
    }

    fn children(&self) -> Vec<AstRef<'c>> {
        self.child_iter().cloned().collect()
    }
}

impl<'c> OpTrait<'c> for StringOp<'c> {
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
        match self {
            StringOp::StringS(..) | StringOp::StringV(..) => Box::new(std::iter::empty()),

            StringOp::BVToStr(a) | StringOp::Annotated(a, _) => Box::new(std::iter::once(a)),

            StringOp::StrConcat(a, b) => Box::new(vec![a, b].into_iter()),

            StringOp::StrSubstr(a, b, c)
            | StringOp::StrReplace(a, b, c)
            | StringOp::If(a, b, c) => Box::new(vec![a, b, c].into_iter()),
        }
    }

    fn children(&self) -> Vec<AstRef<'c>> {
        self.child_iter().cloned().collect()
    }
}


// impl<'c> AstOp<'c> {
//     pub fn child_iter(&self) -> impl Iterator<Item = &AstRef<'c>> {
//         match self {
//             // Cases with no children
//             BooleanOp::BoolS(..)
//             | BooleanOp::BoolV(..)
//             | FloatOp::FPS(..)
//             | FloatOp::FPV(..)
//             | BitVecOp::BVS(..)
//             | BitVecOp::BVV(..)
//             | BitVecOp::SI(..)
//             | StringOp::StringS(..)
//             | StringOp::StringV(..) => Vec::new().into_iter(),

//             // Cases with one child
//             BooleanOp::Not(a)
//             | BooleanOp::FpIsNan(a)
//             | BooleanOp::FpIsInf(a)
//             | BooleanOp::StrIsDigit(a)
//             | FloatOp::FpToFp(a, ..)
//             | FloatOp::BvToFpUnsigned(a, ..)
//             | FloatOp::FpNeg(a, ..)
//             | FloatOp::FpAbs(a, ..)
//             | FloatOp::FpSqrt(a, ..)
//             | BitVecOp::Not(a)
//             | BitVecOp::Reverse(a)
//             | BitVecOp::ZeroExt(a, ..)
//             | BitVecOp::SignExt(a, ..)
//             | BitVecOp::Extract(a, ..)
//             | BitVecOp::FpToIEEEBV(a)
//             | BitVecOp::FpToUBV(a, ..)
//             | BitVecOp::FpToSBV(a, ..)
//             | BitVecOp::StrLen(a, ..)
//             | BitVecOp::StrToBV(a, ..)
//             | StringOp::BVToStr(a)
//             | BooleanOp::Annotated(a, ..)
//             | FloatOp::Annotated(a, ..)
//             | BitVecOp::Annotated(a, ..)
//             | StringOp::Annotated(a, ..) => vec![a].into_iter(),

//             // Cases with two children
//             BooleanOp::StrContains(a, b)
//             | BooleanOp::StrPrefixOf(a, b)
//             | BooleanOp::StrSuffixOf(a, b)
//             | BooleanOp::StrEq(a, b)
//             | BooleanOp::StrNeq(a, b)
//             | BooleanOp::And(a, b)
//             | BooleanOp::Or(a, b)
//             | BooleanOp::Xor(a, b)
//             | BooleanOp::Eq(a, b)
//             | BooleanOp::Neq(a, b)
//             | BooleanOp::ULT(a, b)
//             | BooleanOp::ULE(a, b)
//             | BooleanOp::UGT(a, b)
//             | BooleanOp::UGE(a, b)
//             | BooleanOp::SLT(a, b)
//             | BooleanOp::SLE(a, b)
//             | BooleanOp::SGT(a, b)
//             | BooleanOp::SGE(a, b)
//             | BooleanOp::FpEq(a, b)
//             | BooleanOp::FpNeq(a, b)
//             | BooleanOp::FpLt(a, b)
//             | BooleanOp::FpLeq(a, b)
//             | BooleanOp::FpGt(a, b)
//             | BooleanOp::FpGeq(a, b)
//             | FloatOp::FpAdd(a, b, ..)
//             | FloatOp::FpSub(a, b, ..)
//             | FloatOp::FpMul(a, b, ..)
//             | FloatOp::FpDiv(a, b, ..)
//             | BitVecOp::And(a, b)
//             | BitVecOp::Or(a, b)
//             | BitVecOp::Xor(a, b)
//             | BitVecOp::Add(a, b)
//             | BitVecOp::Sub(a, b)
//             | BitVecOp::Mul(a, b)
//             | BitVecOp::UDiv(a, b)
//             | BitVecOp::SDiv(a, b)
//             | BitVecOp::URem(a, b)
//             | BitVecOp::SRem(a, b)
//             | BitVecOp::Pow(a, b)
//             | BitVecOp::LShL(a, b)
//             | BitVecOp::LShR(a, b)
//             | BitVecOp::AShL(a, b)
//             | BitVecOp::AShR(a, b)
//             | BitVecOp::RotateLeft(a, b)
//             | BitVecOp::RotateRight(a, b)
//             | BitVecOp::Concat(a, b)
//             | BitVecOp::StrIndexOf(a, b)
//             | AstOp::StringOp(StringOp::StrConcat(a, b)) => vec![a, b].into_iter(),

//             // Cases with three children
//             BooleanOp::If(a, b, c)
//             | FloatOp::If(a, b, c)
//             | BitVecOp::If(a, b, c)
//             | StringOp::StrSubstr(a, b, c)
//             | StringOp::StrReplace(a, b, c)
//             | StringOp::If(a, b, c) => vec![a, b, c].into_iter(),
//         }
//     }

//     pub fn children(&self) -> Vec<&AstRef<'c>> {
//         self.child_iter().collect()
//     }
// }
