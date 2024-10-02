use serde::{de, Serialize};

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum AstOp<'c> {
    LogicalOp(LogicalOp<'c>),
    FloatOp(FloatOp<'c>),
    BooleanOp(BooleanOp<'c>),
    BitVecOp(BitVecOp<'c>),
    StringOp(StringOp<'c>),

    // Function ops
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // Annotation ops
    Annotated(AstRef<'c>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum LogicalOp<'c> {
    Not(AstRef<'c>),
    And(AstRef<'c>, AstRef<'c>),
    Or(AstRef<'c>, AstRef<'c>),
    Xor(AstRef<'c>, AstRef<'c>),
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BooleanOp<'c> {
    BoolS(String),
    BoolV(bool),
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BitVecOp<'c> {
    BVS(String, u32),
    BVV(BitVec),
    SI(String, BitVec, BitVec, BitVec, u32),
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum StringOp<'c> {
    StringS(String, u32),
    StringV(String),
    StrConcat(AstRef<'c>, AstRef<'c>), // StrConcat (Vec<AstRef<'c>>) To allow for any number of args,
    StrSubstr(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrReplace(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BVToStr(AstRef<'c>),
}

impl<'c> AstOp<'c> {
    // pub fn valid_args(&self) -> bool {
    //     match self {
    //         AstOp::BoolS(name)
    //         | AstOp::BVS(name, ..)
    //         | AstOp::SI(name, ..)
    //         | AstOp::FPS(name, ..)
    //         | AstOp::StringS(name, ..) => !name.is_empty(),
    //         AstOp::BoolV(..) | AstOp::BVV(..) | AstOp::FPV(..) | AstOp::StringV(..) => true,
    //         AstOp::Not(ast) => ast.kind().is_bool() || ast.kind().is_bitvec(),
    //         AstOp::And(lhs, rhs) | AstOp::Or(lhs, rhs) | AstOp::Xor(lhs, rhs) => {
    //             (lhs.kind().is_bool() || lhs.kind().is_bitvec()) && lhs.kind() == rhs.kind()
    //         }
    //         AstOp::Add(lhs, rhs)
    //         | AstOp::Sub(lhs, rhs)
    //         | AstOp::Mul(lhs, rhs)
    //         | AstOp::UDiv(lhs, rhs)
    //         | AstOp::SDiv(lhs, rhs)
    //         | AstOp::URem(lhs, rhs)
    //         | AstOp::SRem(lhs, rhs)
    //         | AstOp::Pow(lhs, rhs)
    //         | AstOp::LShL(lhs, rhs)
    //         | AstOp::LShR(lhs, rhs)
    //         | AstOp::AShL(lhs, rhs)
    //         | AstOp::AShR(lhs, rhs)
    //         | AstOp::RotateLeft(lhs, rhs)
    //         | AstOp::RotateRight(lhs, rhs)
    //         | AstOp::Concat(lhs, rhs)
    //         | AstOp::Eq(lhs, rhs)
    //         | AstOp::Neq(lhs, rhs)
    //         | AstOp::ULT(lhs, rhs)
    //         | AstOp::ULE(lhs, rhs)
    //         | AstOp::UGT(lhs, rhs)
    //         | AstOp::UGE(lhs, rhs)
    //         | AstOp::SLT(lhs, rhs)
    //         | AstOp::SLE(lhs, rhs)
    //         | AstOp::SGT(lhs, rhs)
    //         | AstOp::SGE(lhs, rhs) => lhs.kind().is_bitvec() && rhs.kind().is_bitvec(),
    //         AstOp::ZeroExt(_, _) => todo!(),
    //         AstOp::SignExt(_, _) => todo!(),
    //         AstOp::Extract(_, _, _) => todo!(),
    //         AstOp::Reverse(_) => todo!(),
    //         AstOp::FpToFp(_, _) => todo!(),
    //         AstOp::BvToFpUnsigned(_, _, _) => todo!(),
    //         AstOp::FpToIEEEBV(_) => todo!(),
    //         AstOp::FpToUBV(_, _, _) => todo!(),
    //         AstOp::FpToSBV(_, _, _) => todo!(),
    //         AstOp::FpNeg(ast, _) | AstOp::FpAbs(ast, _) => ast.kind().is_float(),
    //         AstOp::FpAdd(lhs, rhs, _)
    //         | AstOp::FpSub(lhs, rhs, _)
    //         | AstOp::FpMul(lhs, rhs, _)
    //         | AstOp::FpDiv(lhs, rhs, _) => lhs.kind().is_float() && rhs.kind().is_float(),
    //         AstOp::FpSqrt(_, _) => todo!(),
    //         AstOp::FpEq(_, _) => todo!(),
    //         AstOp::FpNeq(_, _) => todo!(),
    //         AstOp::FpLt(_, _) => todo!(),
    //         AstOp::FpLeq(_, _) => todo!(),
    //         AstOp::FpGt(_, _) => todo!(),
    //         AstOp::FpGeq(_, _) => todo!(),
    //         AstOp::FpIsNan(_) => todo!(),
    //         AstOp::FpIsInf(_) => todo!(),
    //         AstOp::StrLen(_) => todo!(),
    //         AstOp::StrConcat(_, _) => todo!(),
    //         AstOp::StrSubstr(_, _, _) => todo!(),
    //         AstOp::StrContains(_, _) => todo!(),
    //         AstOp::StrIndexOf(_, _) => todo!(),
    //         AstOp::StrReplace(_, _, _) => todo!(),
    //         AstOp::StrPrefixOf(_, _) => todo!(),
    //         AstOp::StrSuffixOf(_, _) => todo!(),
    //         AstOp::StrToBV(_, _) => todo!(),
    //         AstOp::BVToStr(_) => todo!(),
    //         AstOp::StrIsDigit(_) => todo!(),
    //         AstOp::StrEq(_, _) => todo!(),
    //         AstOp::StrNeq(_, _) => todo!(),
    //         AstOp::If(_, _, _) => todo!(),
    //         AstOp::Annotated(_, _) => todo!(),
    //     }
    // }

    pub fn kind(&self) -> AstKind {
        match self {
            AstOp::LogicalOp(op) => match op {
                LogicalOp::Not(..)
                | LogicalOp::And(..)
                | LogicalOp::Or(..)
                | LogicalOp::Xor(..) => AstKind::Bool,
            },

            AstOp::FloatOp(op) => match op {
                FloatOp::FPS(..)
                | FloatOp::FPV(..)
                | FloatOp::FpNeg(..)
                | FloatOp::FpAbs(..)
                | FloatOp::FpAdd(..)
                | FloatOp::FpSub(..)
                | FloatOp::FpMul(..)
                | FloatOp::FpDiv(..)
                | FloatOp::FpSqrt(..)
                | FloatOp::FpToFp(..)
                | FloatOp::BvToFpUnsigned(..) => AstKind::Float,
            },

            AstOp::BooleanOp(op) => match op {
                BooleanOp::BoolS(..)
                | BooleanOp::BoolV(..)
                | BooleanOp::Eq(..)
                | BooleanOp::Neq(..)
                | BooleanOp::ULT(..)
                | BooleanOp::ULE(..)
                | BooleanOp::UGT(..)
                | BooleanOp::UGE(..)
                | BooleanOp::SLT(..)
                | BooleanOp::SLE(..)
                | BooleanOp::SGT(..)
                | BooleanOp::SGE(..)
                | BooleanOp::FpEq(..)
                | BooleanOp::FpNeq(..)
                | BooleanOp::FpLt(..)
                | BooleanOp::FpLeq(..)
                | BooleanOp::FpGt(..)
                | BooleanOp::FpGeq(..)
                | BooleanOp::FpIsNan(..)
                | BooleanOp::FpIsInf(..)
                | BooleanOp::StrContains(..)
                | BooleanOp::StrIsDigit(..)
                | BooleanOp::StrPrefixOf(..)
                | BooleanOp::StrSuffixOf(..)
                | BooleanOp::StrEq(..)
                | BooleanOp::StrNeq(..) => AstKind::Bool,
            },

            AstOp::BitVecOp(op) => match op {
                BitVecOp::BVS(..)
                | BitVecOp::BVV(..)
                | BitVecOp::SI(..)
                | BitVecOp::Add(..)
                | BitVecOp::Sub(..)
                | BitVecOp::Mul(..)
                | BitVecOp::UDiv(..)
                | BitVecOp::SDiv(..)
                | BitVecOp::URem(..)
                | BitVecOp::SRem(..)
                | BitVecOp::Pow(..)
                | BitVecOp::LShL(..)
                | BitVecOp::LShR(..)
                | BitVecOp::AShL(..)
                | BitVecOp::AShR(..)
                | BitVecOp::RotateLeft(..)
                | BitVecOp::RotateRight(..)
                | BitVecOp::ZeroExt(..)
                | BitVecOp::SignExt(..)
                | BitVecOp::Extract(..)
                | BitVecOp::Concat(..)
                | BitVecOp::Reverse(..)
                | BitVecOp::FpToIEEEBV(..)
                | BitVecOp::FpToUBV(..)
                | BitVecOp::FpToSBV(..)
                | BitVecOp::StrLen(..)
                | BitVecOp::StrIndexOf(..)
                | BitVecOp::StrToBV(..) => AstKind::BitVec,
            },

            AstOp::StringOp(op) => match op {
                StringOp::StringS(..)
                | StringOp::StringV(..)
                | StringOp::StrConcat(..)
                | StringOp::StrSubstr(..)
                | StringOp::StrReplace(..)
                | StringOp::BVToStr(..) => AstKind::String,
            },

            AstOp::If(.., ast) | AstOp::Annotated(ast, ..) => ast.kind(),
        }
    }

    pub fn child_iter(&self) -> impl Iterator<Item = &AstRef<'c>> {
        match self {
            // Cases with no children
            AstOp::BooleanOp(BooleanOp::BoolS(..))
            | AstOp::BooleanOp(BooleanOp::BoolV(..))
            | AstOp::BitVecOp(BitVecOp::BVS(..))
            | AstOp::BitVecOp(BitVecOp::BVV(..))
            | AstOp::BitVecOp(BitVecOp::SI(..))
            | AstOp::FloatOp(FloatOp::FPS(..))
            | AstOp::FloatOp(FloatOp::FPV(..))
            | AstOp::StringOp(StringOp::StringS(..))
            | AstOp::StringOp(StringOp::StringV(..)) => Vec::new().into_iter(),

            // Cases with one child
            AstOp::LogicalOp(LogicalOp::Not(a))
            | AstOp::BitVecOp(BitVecOp::Reverse(a))
            | AstOp::BitVecOp(BitVecOp::ZeroExt(a, ..))
            | AstOp::BitVecOp(BitVecOp::SignExt(a, ..))
            | AstOp::BitVecOp(BitVecOp::Extract(a, ..))
            | AstOp::FloatOp(FloatOp::FpToFp(a, ..))
            | AstOp::FloatOp(FloatOp::BvToFpUnsigned(a, ..))
            | AstOp::BitVecOp(BitVecOp::FpToIEEEBV(a))
            | AstOp::BitVecOp(BitVecOp::FpToUBV(a, ..))
            | AstOp::BitVecOp(BitVecOp::FpToSBV(a, ..))
            | AstOp::FloatOp(FloatOp::FpNeg(a, ..))
            | AstOp::FloatOp(FloatOp::FpAbs(a, ..))
            | AstOp::FloatOp(FloatOp::FpSqrt(a, ..))
            | AstOp::BooleanOp(BooleanOp::FpIsNan(a))
            | AstOp::BooleanOp(BooleanOp::FpIsInf(a))
            | AstOp::BitVecOp(BitVecOp::StrLen(a, ..))
            | AstOp::BitVecOp(BitVecOp::StrToBV(a, ..))
            | AstOp::StringOp(StringOp::BVToStr(a))
            | AstOp::BooleanOp(BooleanOp::StrIsDigit(a))
            | AstOp::Annotated(a, ..) => vec![a].into_iter(),

            // Cases with two children
            AstOp::LogicalOp(LogicalOp::And(a, b))
            | AstOp::LogicalOp(LogicalOp::Or(a, b))
            | AstOp::LogicalOp(LogicalOp::Xor(a, b))
            | AstOp::BitVecOp(BitVecOp::Add(a, b))
            | AstOp::BitVecOp(BitVecOp::Sub(a, b))
            | AstOp::BitVecOp(BitVecOp::Mul(a, b))
            | AstOp::BitVecOp(BitVecOp::UDiv(a, b))
            | AstOp::BitVecOp(BitVecOp::SDiv(a, b))
            | AstOp::BitVecOp(BitVecOp::URem(a, b))
            | AstOp::BitVecOp(BitVecOp::SRem(a, b))
            | AstOp::BitVecOp(BitVecOp::Pow(a, b))
            | AstOp::BitVecOp(BitVecOp::LShL(a, b))
            | AstOp::BitVecOp(BitVecOp::LShR(a, b))
            | AstOp::BitVecOp(BitVecOp::AShL(a, b))
            | AstOp::BitVecOp(BitVecOp::AShR(a, b))
            | AstOp::BitVecOp(BitVecOp::RotateLeft(a, b))
            | AstOp::BitVecOp(BitVecOp::RotateRight(a, b))
            | AstOp::BitVecOp(BitVecOp::Concat(a, b))
            | AstOp::BooleanOp(BooleanOp::Eq(a, b))
            | AstOp::BooleanOp(BooleanOp::Neq(a, b))
            | AstOp::BooleanOp(BooleanOp::ULT(a, b))
            | AstOp::BooleanOp(BooleanOp::ULE(a, b))
            | AstOp::BooleanOp(BooleanOp::UGT(a, b))
            | AstOp::BooleanOp(BooleanOp::UGE(a, b))
            | AstOp::BooleanOp(BooleanOp::SLT(a, b))
            | AstOp::BooleanOp(BooleanOp::SLE(a, b))
            | AstOp::BooleanOp(BooleanOp::SGT(a, b))
            | AstOp::BooleanOp(BooleanOp::SGE(a, b))
            | AstOp::FloatOp(FloatOp::FpAdd(a, b, ..))
            | AstOp::FloatOp(FloatOp::FpSub(a, b, ..))
            | AstOp::FloatOp(FloatOp::FpMul(a, b, ..))
            | AstOp::FloatOp(FloatOp::FpDiv(a, b, ..))
            | AstOp::BooleanOp(BooleanOp::FpEq(a, b))
            | AstOp::BooleanOp(BooleanOp::FpNeq(a, b))
            | AstOp::BooleanOp(BooleanOp::FpLt(a, b))
            | AstOp::BooleanOp(BooleanOp::FpLeq(a, b))
            | AstOp::BooleanOp(BooleanOp::FpGt(a, b))
            | AstOp::BooleanOp(BooleanOp::FpGeq(a, b))
            | AstOp::StringOp(StringOp::StrConcat(a, b))
            | AstOp::BooleanOp(BooleanOp::StrContains(a, b))
            | AstOp::BitVecOp(BitVecOp::StrIndexOf(a, b))
            | AstOp::BooleanOp(BooleanOp::StrPrefixOf(a, b))
            | AstOp::BooleanOp(BooleanOp::StrSuffixOf(a, b))
            | AstOp::BooleanOp(BooleanOp::StrEq(a, b))
            | AstOp::BooleanOp(BooleanOp::StrNeq(a, b)) => vec![a, b].into_iter(),

            // Cases with three children
            AstOp::StringOp(StringOp::StrSubstr(a, b, c))
            | AstOp::StringOp(StringOp::StrReplace(a, b, c))
            | AstOp::If(a, b, c) => vec![a, b, c].into_iter(),
        }
    }

    pub fn children(&self) -> Vec<&AstRef<'c>> {
        self.child_iter().collect()
    }
}
