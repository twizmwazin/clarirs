use serde::Serialize;

use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum AstOp<'c> {
    PrimitiveOp(PrimitiveOp),
    BitOp(BitOp<'c>),
    ArithmeticOp(ArithmeticOp<'c>),
    BitVectorOp(BitVectorOp<'c>),
    FloatingPointOp(FloatingPointOp<'c>),
    StringOp(StringOp<'c>),

    // Function ops
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // Annotation ops
    Annotated(AstRef<'c>, Annotation<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum PrimitiveOp {
    BoolS(String),
    BoolV(bool),
    BVS(String, u32),
    BVV(BitVec),
    SI(String, BitVec, BitVec, BitVec, u32),
    FPS(String, FSort),
    FPV(Float),
    StringS(String, u32),
    StringV(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BitOp<'c> {
    Not(AstRef<'c>),
    And(AstRef<'c>, AstRef<'c>),
    Or(AstRef<'c>, AstRef<'c>),
    Xor(AstRef<'c>, AstRef<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum ArithmeticOp<'c> {
    Add(AstRef<'c>, AstRef<'c>),
    Sub(AstRef<'c>, AstRef<'c>),
    Mul(AstRef<'c>, AstRef<'c>),
    UDiv(AstRef<'c>, AstRef<'c>),
    SDiv(AstRef<'c>, AstRef<'c>),
    URem(AstRef<'c>, AstRef<'c>),
    SRem(AstRef<'c>, AstRef<'c>),
    Pow(AstRef<'c>, AstRef<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum BitVectorOp<'c> {
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

    // Bitvector comparison ops
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum FloatingPointOp<'c> {
    // Floating point ops
    FpToFp(AstRef<'c>, FSort),
    BvToFpUnsigned(AstRef<'c>, FSort, FPRM),
    FpToIEEEBV(AstRef<'c>),
    FpToUBV(AstRef<'c>, u32, FPRM),
    FpToSBV(AstRef<'c>, u32, FPRM),

    // Floating point arithmetic ops
    FpNeg(AstRef<'c>, FPRM),
    FpAbs(AstRef<'c>, FPRM),
    FpAdd(AstRef<'c>, AstRef<'c>, FPRM),
    FpSub(AstRef<'c>, AstRef<'c>, FPRM),
    FpMul(AstRef<'c>, AstRef<'c>, FPRM),
    FpDiv(AstRef<'c>, AstRef<'c>, FPRM),
    FpSqrt(AstRef<'c>, FPRM),

    // Floating point comparison ops
    FpEq(AstRef<'c>, AstRef<'c>),
    FpNeq(AstRef<'c>, AstRef<'c>),
    FpLt(AstRef<'c>, AstRef<'c>),
    FpLeq(AstRef<'c>, AstRef<'c>),
    FpGt(AstRef<'c>, AstRef<'c>),
    FpGeq(AstRef<'c>, AstRef<'c>),
    FpIsNan(AstRef<'c>),
    FpIsInf(AstRef<'c>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum StringOp<'c> {
    StrLen(AstRef<'c>, AstRef<'c>),    // or StrLen(AstRef<'c>, u32),
    StrConcat(AstRef<'c>, AstRef<'c>), // StrConcat(Vec<AstRef<'c>>) To allow for any number of args,
    StrSubstr(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrContains(AstRef<'c>, AstRef<'c>),
    StrIndexOf(AstRef<'c>, AstRef<'c>),
    StrReplace(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrPrefixOf(AstRef<'c>, AstRef<'c>),
    StrSuffixOf(AstRef<'c>, AstRef<'c>),
    StrToBV(AstRef<'c>, AstRef<'c>), // StrToBV(AstRef<'c>, u32)
    BVToStr(AstRef<'c>),
    StrIsDigit(AstRef<'c>),

    // String comparison ops
    StrEq(AstRef<'c>, AstRef<'c>),
    StrNeq(AstRef<'c>, AstRef<'c>),
}

impl<'c> AstOp<'c> {
    pub fn valid_args(&self) -> bool {
        match self {
            AstOp::PrimitiveOp(op) => match op {
                PrimitiveOp::BoolS(name)
                | PrimitiveOp::BVS(name, ..)
                | PrimitiveOp::SI(name, ..)
                | PrimitiveOp::FPS(name, ..)
                | PrimitiveOp::StringS(name, ..) => !name.is_empty(),
                PrimitiveOp::BoolV(..)
                | PrimitiveOp::BVV(..)
                | PrimitiveOp::FPV(..)
                | PrimitiveOp::StringV(..) => true,
            },

            AstOp::BitOp(op) => match op {
                BitOp::Not(ast) => ast.kind().is_bool() || ast.kind().is_bitvec(),
                BitOp::And(lhs, rhs) | BitOp::Or(lhs, rhs) | BitOp::Xor(lhs, rhs) => {
                    (lhs.kind().is_bool() || lhs.kind().is_bitvec()) && lhs.kind() == rhs.kind()
                }
            },

            AstOp::ArithmeticOp(op) => match op {
                ArithmeticOp::Add(lhs, rhs)
                | ArithmeticOp::Sub(lhs, rhs)
                | ArithmeticOp::Mul(lhs, rhs)
                | ArithmeticOp::UDiv(lhs, rhs)
                | ArithmeticOp::SDiv(lhs, rhs)
                | ArithmeticOp::URem(lhs, rhs)
                | ArithmeticOp::SRem(lhs, rhs)
                | ArithmeticOp::Pow(lhs, rhs) => lhs.kind() == rhs.kind(),
            },

            AstOp::BitVectorOp(op) => match op {
                BitVectorOp::LShL(lhs, rhs)
                | BitVectorOp::LShR(lhs, rhs)
                | BitVectorOp::AShL(lhs, rhs)
                | BitVectorOp::AShR(lhs, rhs)
                | BitVectorOp::RotateLeft(lhs, rhs)
                | BitVectorOp::RotateRight(lhs, rhs) => {
                    lhs.kind().is_bitvec() && lhs.kind() == rhs.kind()
                }
                BitVectorOp::ZeroExt(ast, _) | BitVectorOp::SignExt(ast, _) => {
                    ast.kind().is_bitvec()
                }
                BitVectorOp::Extract(ast, _, _)
                | BitVectorOp::Concat(ast, _)
                | BitVectorOp::Reverse(ast) => ast.kind().is_bitvec(),

                // BitVector comparisons
                BitVectorOp::Eq(lhs, rhs)
                | BitVectorOp::Neq(lhs, rhs)
                | BitVectorOp::ULT(lhs, rhs)
                | BitVectorOp::ULE(lhs, rhs)
                | BitVectorOp::UGT(lhs, rhs)
                | BitVectorOp::UGE(lhs, rhs)
                | BitVectorOp::SLT(lhs, rhs)
                | BitVectorOp::SLE(lhs, rhs)
                | BitVectorOp::SGT(lhs, rhs)
                | BitVectorOp::SGE(lhs, rhs) => lhs.kind().is_bitvec() && lhs.kind() == rhs.kind(),
            },

            AstOp::FloatingPointOp(op) => match op {
                FloatingPointOp::FpToFp(ast, _)
                | FloatingPointOp::BvToFpUnsigned(ast, _, _)
                | FloatingPointOp::FpToIEEEBV(ast)
                | FloatingPointOp::FpToUBV(ast, _, _)
                | FloatingPointOp::FpToSBV(ast, _, _) => ast.kind().is_float(),
                FloatingPointOp::FpNeg(ast, _)
                | FloatingPointOp::FpAbs(ast, _)
                | FloatingPointOp::FpSqrt(ast, _) => ast.kind().is_float(),
                FloatingPointOp::FpAdd(lhs, rhs, _)
                | FloatingPointOp::FpSub(lhs, rhs, _)
                | FloatingPointOp::FpMul(lhs, rhs, _)
                | FloatingPointOp::FpDiv(lhs, rhs, _) => {
                    lhs.kind().is_float() && lhs.kind() == rhs.kind()
                }

                // Floating-point comparisons
                FloatingPointOp::FpEq(lhs, rhs)
                | FloatingPointOp::FpNeq(lhs, rhs)
                | FloatingPointOp::FpLt(lhs, rhs)
                | FloatingPointOp::FpLeq(lhs, rhs)
                | FloatingPointOp::FpGt(lhs, rhs)
                | FloatingPointOp::FpGeq(lhs, rhs) => {
                    lhs.kind().is_float() && lhs.kind() == rhs.kind()
                }
                FloatingPointOp::FpIsNan(ast) | FloatingPointOp::FpIsInf(ast) => {
                    ast.kind().is_float()
                }
            },

            AstOp::StringOp(op) => match op {
                StringOp::StrLen(ast, _)
                | StringOp::StrConcat(ast, _)
                | StringOp::StrSubstr(ast, _, _)
                | StringOp::StrContains(ast, _)
                | StringOp::StrIndexOf(ast, _)
                | StringOp::StrReplace(ast, _, _)
                | StringOp::StrPrefixOf(ast, _)
                | StringOp::StrSuffixOf(ast, _) => ast.kind().is_string(),
                StringOp::StrToBV(ast, _) | StringOp::BVToStr(ast) => ast.kind().is_string(),
                StringOp::StrIsDigit(ast) => ast.kind().is_string(),

                // String comparisons
                StringOp::StrEq(lhs, rhs) | StringOp::StrNeq(lhs, rhs) => {
                    lhs.kind().is_string() && lhs.kind() == rhs.kind()
                }
            },

            AstOp::If(_, _, _) => todo!(),
            AstOp::Annotated(_, _) => todo!(),
        }
    }

    pub fn kind(&self) -> AstKind {
        match self {
            AstOp::PrimitiveOp(op) => match op {
                PrimitiveOp::BoolS(..) | PrimitiveOp::BoolV(..) => AstKind::Bool,
                PrimitiveOp::BVS(..) | PrimitiveOp::BVV(..) | PrimitiveOp::SI(..) => {
                    AstKind::BitVec
                }
                PrimitiveOp::FPS(..) | PrimitiveOp::FPV(..) => AstKind::Float,
                PrimitiveOp::StringS(..) | PrimitiveOp::StringV(..) => AstKind::String,
            },

            AstOp::BitOp(op) => match op {
                BitOp::Not(ast)
                | BitOp::And(ast, ..)
                | BitOp::Or(ast, ..)
                | BitOp::Xor(ast, ..) => ast.kind(),
            },

            AstOp::ArithmeticOp(op) => match op {
                ArithmeticOp::Add(..)
                | ArithmeticOp::Sub(..)
                | ArithmeticOp::Mul(..)
                | ArithmeticOp::UDiv(..)
                | ArithmeticOp::SDiv(..)
                | ArithmeticOp::URem(..)
                | ArithmeticOp::SRem(..)
                | ArithmeticOp::Pow(..) => AstKind::BitVec,
            },

            AstOp::BitVectorOp(op) => match op {
                BitVectorOp::LShL(..)
                | BitVectorOp::LShR(..)
                | BitVectorOp::AShL(..)
                | BitVectorOp::AShR(..)
                | BitVectorOp::RotateLeft(..)
                | BitVectorOp::RotateRight(..)
                | BitVectorOp::ZeroExt(..)
                | BitVectorOp::SignExt(..)
                | BitVectorOp::Extract(..)
                | BitVectorOp::Concat(..)
                | BitVectorOp::Reverse(..) => AstKind::BitVec,
                BitVectorOp::Eq(..)
                | BitVectorOp::Neq(..)
                | BitVectorOp::ULT(..)
                | BitVectorOp::ULE(..)
                | BitVectorOp::UGT(..)
                | BitVectorOp::UGE(..)
                | BitVectorOp::SLT(..)
                | BitVectorOp::SLE(..)
                | BitVectorOp::SGT(..)
                | BitVectorOp::SGE(..) => AstKind::Bool,
            },

            AstOp::FloatingPointOp(op) => match op {
                FloatingPointOp::FpToFp(..) | FloatingPointOp::BvToFpUnsigned(..) => AstKind::Float,
                FloatingPointOp::FpToIEEEBV(..)
                | FloatingPointOp::FpToUBV(..)
                | FloatingPointOp::FpToSBV(..) => AstKind::BitVec,
                FloatingPointOp::FpNeg(..)
                | FloatingPointOp::FpAbs(..)
                | FloatingPointOp::FpAdd(..)
                | FloatingPointOp::FpSub(..)
                | FloatingPointOp::FpMul(..)
                | FloatingPointOp::FpDiv(..)
                | FloatingPointOp::FpSqrt(..) => AstKind::Float,
                FloatingPointOp::FpEq(..)
                | FloatingPointOp::FpNeq(..)
                | FloatingPointOp::FpLt(..)
                | FloatingPointOp::FpLeq(..)
                | FloatingPointOp::FpGt(..)
                | FloatingPointOp::FpGeq(..)
                | FloatingPointOp::FpIsNan(..)
                | FloatingPointOp::FpIsInf(..) => AstKind::Bool,
            },

            AstOp::StringOp(op) => match op {
                StringOp::StrLen(..) => AstKind::BitVec,
                StringOp::StrConcat(..) | StringOp::StrSubstr(..) => AstKind::String,
                StringOp::StrContains(..) => AstKind::Bool,
                StringOp::StrIndexOf(..) => AstKind::BitVec,
                StringOp::StrReplace(..) => AstKind::String,
                StringOp::StrPrefixOf(..) | StringOp::StrSuffixOf(..) => AstKind::Bool,
                StringOp::StrToBV(..) => AstKind::BitVec,
                StringOp::BVToStr(..) => AstKind::String,
                StringOp::StrIsDigit(..) | StringOp::StrEq(..) | StringOp::StrNeq(..) => {
                    AstKind::Bool
                }
            },

            AstOp::If(.., ast) => ast.kind(),
            AstOp::Annotated(ast, ..) => ast.kind(),
        }
    }

    pub fn child_iter(&self) -> impl Iterator<Item = &AstRef<'c>> {
        match self {
            // Cases with no children
            AstOp::PrimitiveOp(PrimitiveOp::BoolS(..))
            | AstOp::PrimitiveOp(PrimitiveOp::BoolV(..))
            | AstOp::PrimitiveOp(PrimitiveOp::BVS(..))
            | AstOp::PrimitiveOp(PrimitiveOp::BVV(..))
            | AstOp::PrimitiveOp(PrimitiveOp::SI(..))
            | AstOp::PrimitiveOp(PrimitiveOp::FPS(..))
            | AstOp::PrimitiveOp(PrimitiveOp::FPV(..))
            | AstOp::PrimitiveOp(PrimitiveOp::StringS(..))
            | AstOp::PrimitiveOp(PrimitiveOp::StringV(..)) => Vec::new().into_iter(),

            // Cases with one child
            AstOp::BitOp(BitOp::Not(a))
            | AstOp::BitVectorOp(BitVectorOp::Reverse(a))
            | AstOp::BitVectorOp(BitVectorOp::ZeroExt(a, ..))
            | AstOp::BitVectorOp(BitVectorOp::SignExt(a, ..))
            | AstOp::BitVectorOp(BitVectorOp::Extract(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpToFp(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::BvToFpUnsigned(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpToIEEEBV(a))
            | AstOp::FloatingPointOp(FloatingPointOp::FpToUBV(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpToSBV(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpNeg(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpAbs(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpSqrt(a, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpIsNan(a))
            | AstOp::FloatingPointOp(FloatingPointOp::FpIsInf(a))
            | AstOp::StringOp(StringOp::StrLen(a, ..))
            | AstOp::StringOp(StringOp::StrToBV(a, ..))
            | AstOp::StringOp(StringOp::BVToStr(a))
            | AstOp::StringOp(StringOp::StrIsDigit(a))
            | AstOp::Annotated(a, ..) => vec![a].into_iter(),

            // Cases with two children
            AstOp::BitOp(BitOp::And(a, b))
            | AstOp::BitOp(BitOp::Or(a, b))
            | AstOp::BitOp(BitOp::Xor(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::Add(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::Sub(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::Mul(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::UDiv(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::SDiv(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::URem(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::SRem(a, b))
            | AstOp::ArithmeticOp(ArithmeticOp::Pow(a, b))
            | AstOp::BitVectorOp(BitVectorOp::LShL(a, b))
            | AstOp::BitVectorOp(BitVectorOp::LShR(a, b))
            | AstOp::BitVectorOp(BitVectorOp::AShL(a, b))
            | AstOp::BitVectorOp(BitVectorOp::AShR(a, b))
            | AstOp::BitVectorOp(BitVectorOp::RotateLeft(a, b))
            | AstOp::BitVectorOp(BitVectorOp::RotateRight(a, b))
            | AstOp::BitVectorOp(BitVectorOp::Concat(a, b))
            | AstOp::BitVectorOp(BitVectorOp::Eq(a, b))
            | AstOp::BitVectorOp(BitVectorOp::Neq(a, b))
            | AstOp::BitVectorOp(BitVectorOp::ULT(a, b))
            | AstOp::BitVectorOp(BitVectorOp::ULE(a, b))
            | AstOp::BitVectorOp(BitVectorOp::UGT(a, b))
            | AstOp::BitVectorOp(BitVectorOp::UGE(a, b))
            | AstOp::BitVectorOp(BitVectorOp::SLT(a, b))
            | AstOp::BitVectorOp(BitVectorOp::SLE(a, b))
            | AstOp::BitVectorOp(BitVectorOp::SGT(a, b))
            | AstOp::BitVectorOp(BitVectorOp::SGE(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpAdd(a, b, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpSub(a, b, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpMul(a, b, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpDiv(a, b, ..))
            | AstOp::FloatingPointOp(FloatingPointOp::FpEq(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpNeq(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpLt(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpLeq(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpGt(a, b))
            | AstOp::FloatingPointOp(FloatingPointOp::FpGeq(a, b))
            | AstOp::StringOp(StringOp::StrConcat(a, b))
            | AstOp::StringOp(StringOp::StrContains(a, b))
            | AstOp::StringOp(StringOp::StrIndexOf(a, b))
            | AstOp::StringOp(StringOp::StrPrefixOf(a, b))
            | AstOp::StringOp(StringOp::StrSuffixOf(a, b))
            | AstOp::StringOp(StringOp::StrEq(a, b))
            | AstOp::StringOp(StringOp::StrNeq(a, b)) => vec![a, b].into_iter(),

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
