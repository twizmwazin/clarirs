use std::collections::BTreeSet;
use std::sync::Arc;

use serde::Serialize;

use crate::ast::theory::Theories;
use crate::context::InternedString;
use clarirs_num::{BitVec, FPRM, FSort, Float};

/// A reference-counted AST node.
pub type AstRef<'c> = Arc<super::node::AstNode<'c>>;

/// Helper trait to accept both owned and borrowed AstRef values.
pub trait IntoAstRef<'c> {
    fn into_ast_ref(self) -> AstRef<'c>;
}

impl<'c> IntoAstRef<'c> for AstRef<'c> {
    fn into_ast_ref(self) -> AstRef<'c> {
        self
    }
}

impl<'c> IntoAstRef<'c> for &AstRef<'c> {
    fn into_ast_ref(self) -> AstRef<'c> {
        self.clone()
    }
}

/// Type aliases for sort-specific AST references.
/// These are all the same type but kept for readability at call sites.
pub type BoolAst<'c> = AstRef<'c>;
pub type BitVecAst<'c> = AstRef<'c>;
pub type FloatAst<'c> = AstRef<'c>;
pub type StringAst<'c> = AstRef<'c>;

/// Unified AST operation enum. Following Z3's approach, operations that are
/// semantically equivalent across sorts (Not, And, Or, Xor, Eq, Neq, If)
/// are represented as single variants.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum AstOp<'c> {
    // === Leaf nodes ===
    BoolS(InternedString),
    BoolV(bool),
    BVS(InternedString, u32),
    BVV(BitVec),
    FPS(InternedString, FSort),
    FPV(Float),
    StringS(InternedString),
    StringV(String),

    // === Cross-sort operations (Z3-style) ===
    Not(AstRef<'c>),
    And(Vec<AstRef<'c>>),
    Or(Vec<AstRef<'c>>),
    Xor(Vec<AstRef<'c>>),
    Eq(AstRef<'c>, AstRef<'c>),
    Neq(AstRef<'c>, AstRef<'c>),
    If(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // === BV arithmetic ===
    Neg(AstRef<'c>),
    Add(Vec<AstRef<'c>>),
    Sub(AstRef<'c>, AstRef<'c>),
    Mul(Vec<AstRef<'c>>),
    UDiv(AstRef<'c>, AstRef<'c>),
    SDiv(AstRef<'c>, AstRef<'c>),
    URem(AstRef<'c>, AstRef<'c>),
    SRem(AstRef<'c>, AstRef<'c>),

    // === BV shifts/rotates ===
    ShL(AstRef<'c>, AstRef<'c>),
    LShR(AstRef<'c>, AstRef<'c>),
    AShR(AstRef<'c>, AstRef<'c>),
    RotateLeft(AstRef<'c>, AstRef<'c>),
    RotateRight(AstRef<'c>, AstRef<'c>),

    // === BV extraction/extension ===
    Extract(AstRef<'c>, u32, u32),
    ZeroExt(AstRef<'c>, u32),
    SignExt(AstRef<'c>, u32),
    Concat(Vec<AstRef<'c>>),
    ByteReverse(AstRef<'c>),

    // === BV comparisons ===
    ULT(AstRef<'c>, AstRef<'c>),
    ULE(AstRef<'c>, AstRef<'c>),
    UGT(AstRef<'c>, AstRef<'c>),
    UGE(AstRef<'c>, AstRef<'c>),
    SLT(AstRef<'c>, AstRef<'c>),
    SLE(AstRef<'c>, AstRef<'c>),
    SGT(AstRef<'c>, AstRef<'c>),
    SGE(AstRef<'c>, AstRef<'c>),

    // === Float operations ===
    FpNeg(AstRef<'c>),
    FpAbs(AstRef<'c>),
    FpAdd(AstRef<'c>, AstRef<'c>, FPRM),
    FpSub(AstRef<'c>, AstRef<'c>, FPRM),
    FpMul(AstRef<'c>, AstRef<'c>, FPRM),
    FpDiv(AstRef<'c>, AstRef<'c>, FPRM),
    FpSqrt(AstRef<'c>, FPRM),
    FpToFp(AstRef<'c>, FSort, FPRM),
    FpFP(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BvToFp(AstRef<'c>, FSort),
    BvToFpSigned(AstRef<'c>, FSort, FPRM),
    BvToFpUnsigned(AstRef<'c>, FSort, FPRM),

    // === Float comparisons ===
    FpLt(AstRef<'c>, AstRef<'c>),
    FpLeq(AstRef<'c>, AstRef<'c>),
    FpGt(AstRef<'c>, AstRef<'c>),
    FpGeq(AstRef<'c>, AstRef<'c>),
    FpIsNan(AstRef<'c>),
    FpIsInf(AstRef<'c>),

    // === Float-BV conversions ===
    FpToIEEEBV(AstRef<'c>),
    FpToUBV(AstRef<'c>, u32, FPRM),
    FpToSBV(AstRef<'c>, u32, FPRM),

    // === String operations ===
    StrConcat(AstRef<'c>, AstRef<'c>),
    StrSubstr(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrReplace(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BVToStr(AstRef<'c>),
    StrLen(AstRef<'c>),
    StrIndexOf(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrToBV(AstRef<'c>),

    // === String comparisons ===
    StrContains(AstRef<'c>, AstRef<'c>),
    StrPrefixOf(AstRef<'c>, AstRef<'c>),
    StrSuffixOf(AstRef<'c>, AstRef<'c>),
    StrIsDigit(AstRef<'c>),

    // === VSA operations ===
    Union(AstRef<'c>, AstRef<'c>),
    Intersection(AstRef<'c>, AstRef<'c>),
    Widen(AstRef<'c>, AstRef<'c>),
}

impl std::hash::Hash for AstOp<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            AstOp::BoolS(s) => s.hash(state),
            AstOp::BoolV(b) => b.hash(state),
            AstOp::BVS(s, size) => {
                s.hash(state);
                size.hash(state);
            }
            AstOp::BVV(bv) => bv.hash(state),
            AstOp::FPS(s, sort) => {
                s.hash(state);
                sort.hash(state);
            }
            AstOp::FPV(f) => f.hash(state),
            AstOp::StringS(s) => s.hash(state),
            AstOp::StringV(s) => s.hash(state),
            AstOp::Not(a)
            | AstOp::Neg(a)
            | AstOp::ByteReverse(a)
            | AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpIsNan(a)
            | AstOp::FpIsInf(a)
            | AstOp::FpToIEEEBV(a)
            | AstOp::BVToStr(a)
            | AstOp::StrLen(a)
            | AstOp::StrToBV(a)
            | AstOp::StrIsDigit(a) => a.hash(state),
            AstOp::Extract(a, hi, lo) => {
                a.hash(state);
                hi.hash(state);
                lo.hash(state);
            }
            AstOp::ZeroExt(a, ext) | AstOp::SignExt(a, ext) => {
                a.hash(state);
                ext.hash(state);
            }
            AstOp::FpSqrt(a, rm) => {
                a.hash(state);
                rm.hash(state);
            }
            AstOp::FpToFp(a, sort, rm) => {
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            AstOp::BvToFp(a, sort) => {
                a.hash(state);
                sort.hash(state);
            }
            AstOp::BvToFpSigned(a, sort, rm) | AstOp::BvToFpUnsigned(a, sort, rm) => {
                a.hash(state);
                sort.hash(state);
                rm.hash(state);
            }
            AstOp::FpToUBV(a, size, rm) | AstOp::FpToSBV(a, size, rm) => {
                a.hash(state);
                size.hash(state);
                rm.hash(state);
            }
            AstOp::And(args)
            | AstOp::Or(args)
            | AstOp::Xor(args)
            | AstOp::Add(args)
            | AstOp::Mul(args)
            | AstOp::Concat(args) => args.hash(state),
            AstOp::Eq(a, b)
            | AstOp::Neq(a, b)
            | AstOp::Sub(a, b)
            | AstOp::UDiv(a, b)
            | AstOp::SDiv(a, b)
            | AstOp::URem(a, b)
            | AstOp::SRem(a, b)
            | AstOp::ShL(a, b)
            | AstOp::LShR(a, b)
            | AstOp::AShR(a, b)
            | AstOp::RotateLeft(a, b)
            | AstOp::RotateRight(a, b)
            | AstOp::ULT(a, b)
            | AstOp::ULE(a, b)
            | AstOp::UGT(a, b)
            | AstOp::UGE(a, b)
            | AstOp::SLT(a, b)
            | AstOp::SLE(a, b)
            | AstOp::SGT(a, b)
            | AstOp::SGE(a, b)
            | AstOp::FpLt(a, b)
            | AstOp::FpLeq(a, b)
            | AstOp::FpGt(a, b)
            | AstOp::FpGeq(a, b)
            | AstOp::StrConcat(a, b)
            | AstOp::StrContains(a, b)
            | AstOp::StrPrefixOf(a, b)
            | AstOp::StrSuffixOf(a, b)
            | AstOp::Union(a, b)
            | AstOp::Intersection(a, b)
            | AstOp::Widen(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            AstOp::FpAdd(a, b, rm)
            | AstOp::FpSub(a, b, rm)
            | AstOp::FpMul(a, b, rm)
            | AstOp::FpDiv(a, b, rm) => {
                a.hash(state);
                b.hash(state);
                rm.hash(state);
            }
            AstOp::If(a, b, c)
            | AstOp::FpFP(a, b, c)
            | AstOp::StrSubstr(a, b, c)
            | AstOp::StrReplace(a, b, c)
            | AstOp::StrIndexOf(a, b, c) => {
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}

impl<'c> AstOp<'c> {
    /// Returns the number of children this op has.
    pub fn num_children(&self) -> usize {
        match self {
            AstOp::BoolS(_)
            | AstOp::BoolV(_)
            | AstOp::BVS(..)
            | AstOp::BVV(_)
            | AstOp::FPS(..)
            | AstOp::FPV(_)
            | AstOp::StringS(_)
            | AstOp::StringV(_) => 0,

            AstOp::Not(_)
            | AstOp::Neg(_)
            | AstOp::ByteReverse(_)
            | AstOp::FpNeg(_)
            | AstOp::FpAbs(_)
            | AstOp::FpSqrt(..)
            | AstOp::FpToFp(..)
            | AstOp::BvToFp(..)
            | AstOp::BvToFpSigned(..)
            | AstOp::BvToFpUnsigned(..)
            | AstOp::FpIsNan(_)
            | AstOp::FpIsInf(_)
            | AstOp::FpToIEEEBV(_)
            | AstOp::FpToUBV(..)
            | AstOp::FpToSBV(..)
            | AstOp::BVToStr(_)
            | AstOp::StrLen(_)
            | AstOp::StrToBV(_)
            | AstOp::StrIsDigit(_)
            | AstOp::Extract(..)
            | AstOp::ZeroExt(..)
            | AstOp::SignExt(..) => 1,

            AstOp::Eq(..)
            | AstOp::Neq(..)
            | AstOp::Sub(..)
            | AstOp::UDiv(..)
            | AstOp::SDiv(..)
            | AstOp::URem(..)
            | AstOp::SRem(..)
            | AstOp::ShL(..)
            | AstOp::LShR(..)
            | AstOp::AShR(..)
            | AstOp::RotateLeft(..)
            | AstOp::RotateRight(..)
            | AstOp::ULT(..)
            | AstOp::ULE(..)
            | AstOp::UGT(..)
            | AstOp::UGE(..)
            | AstOp::SLT(..)
            | AstOp::SLE(..)
            | AstOp::SGT(..)
            | AstOp::SGE(..)
            | AstOp::FpAdd(..)
            | AstOp::FpSub(..)
            | AstOp::FpMul(..)
            | AstOp::FpDiv(..)
            | AstOp::FpLt(..)
            | AstOp::FpLeq(..)
            | AstOp::FpGt(..)
            | AstOp::FpGeq(..)
            | AstOp::StrConcat(..)
            | AstOp::StrContains(..)
            | AstOp::StrPrefixOf(..)
            | AstOp::StrSuffixOf(..)
            | AstOp::Union(..)
            | AstOp::Intersection(..)
            | AstOp::Widen(..) => 2,

            AstOp::If(..)
            | AstOp::FpFP(..)
            | AstOp::StrSubstr(..)
            | AstOp::StrReplace(..)
            | AstOp::StrIndexOf(..) => 3,

            AstOp::And(args)
            | AstOp::Or(args)
            | AstOp::Xor(args)
            | AstOp::Add(args)
            | AstOp::Mul(args)
            | AstOp::Concat(args) => args.len(),
        }
    }

    /// Returns the child at the given index.
    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        match self {
            // 0 children
            AstOp::BoolS(_)
            | AstOp::BoolV(_)
            | AstOp::BVS(..)
            | AstOp::BVV(_)
            | AstOp::FPS(..)
            | AstOp::FPV(_)
            | AstOp::StringS(_)
            | AstOp::StringV(_) => None,

            // 1 child
            AstOp::Not(a)
            | AstOp::Neg(a)
            | AstOp::ByteReverse(a)
            | AstOp::Extract(a, _, _)
            | AstOp::ZeroExt(a, _)
            | AstOp::SignExt(a, _)
            | AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpSqrt(a, _)
            | AstOp::FpToFp(a, _, _)
            | AstOp::BvToFp(a, _)
            | AstOp::BvToFpSigned(a, _, _)
            | AstOp::BvToFpUnsigned(a, _, _)
            | AstOp::FpIsNan(a)
            | AstOp::FpIsInf(a)
            | AstOp::FpToIEEEBV(a)
            | AstOp::FpToUBV(a, _, _)
            | AstOp::FpToSBV(a, _, _)
            | AstOp::BVToStr(a)
            | AstOp::StrLen(a)
            | AstOp::StrToBV(a)
            | AstOp::StrIsDigit(a) => {
                if index == 0 {
                    Some(a.clone())
                } else {
                    None
                }
            }

            // 2 children
            AstOp::Eq(a, b)
            | AstOp::Neq(a, b)
            | AstOp::Sub(a, b)
            | AstOp::UDiv(a, b)
            | AstOp::SDiv(a, b)
            | AstOp::URem(a, b)
            | AstOp::SRem(a, b)
            | AstOp::ShL(a, b)
            | AstOp::LShR(a, b)
            | AstOp::AShR(a, b)
            | AstOp::RotateLeft(a, b)
            | AstOp::RotateRight(a, b)
            | AstOp::ULT(a, b)
            | AstOp::ULE(a, b)
            | AstOp::UGT(a, b)
            | AstOp::UGE(a, b)
            | AstOp::SLT(a, b)
            | AstOp::SLE(a, b)
            | AstOp::SGT(a, b)
            | AstOp::SGE(a, b)
            | AstOp::FpLt(a, b)
            | AstOp::FpLeq(a, b)
            | AstOp::FpGt(a, b)
            | AstOp::FpGeq(a, b)
            | AstOp::StrConcat(a, b)
            | AstOp::StrContains(a, b)
            | AstOp::StrPrefixOf(a, b)
            | AstOp::StrSuffixOf(a, b)
            | AstOp::Union(a, b)
            | AstOp::Intersection(a, b)
            | AstOp::Widen(a, b) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                _ => None,
            },

            // 2 children + extra params (still 2 AST children)
            AstOp::FpAdd(a, b, _)
            | AstOp::FpSub(a, b, _)
            | AstOp::FpMul(a, b, _)
            | AstOp::FpDiv(a, b, _) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                _ => None,
            },

            // 3 children
            AstOp::If(a, b, c)
            | AstOp::FpFP(a, b, c)
            | AstOp::StrSubstr(a, b, c)
            | AstOp::StrReplace(a, b, c)
            | AstOp::StrIndexOf(a, b, c) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                2 => Some(c.clone()),
                _ => None,
            },

            // N-ary
            AstOp::And(args)
            | AstOp::Or(args)
            | AstOp::Xor(args)
            | AstOp::Add(args)
            | AstOp::Mul(args)
            | AstOp::Concat(args) => args.get(index).cloned(),
        }
    }

    /// Returns an iterator over child AST nodes.
    pub fn children(&self) -> AstOpChildIter<'_, 'c> {
        AstOpChildIter { op: self, index: 0 }
    }

    pub fn depth(&self) -> u32 {
        1 + self.children().map(|c| c.depth()).max().unwrap_or(0)
    }

    pub fn is_leaf(&self) -> bool {
        self.num_children() == 0
    }

    pub fn is_true(&self) -> bool {
        matches!(self, AstOp::BoolV(true))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, AstOp::BoolV(false))
    }

    pub fn variables(&self) -> BTreeSet<InternedString> {
        match self {
            AstOp::BoolS(s) | AstOp::StringS(s) => {
                let mut set = BTreeSet::new();
                set.insert(s.clone());
                set
            }
            AstOp::BVS(s, _) => {
                let mut set = BTreeSet::new();
                set.insert(s.clone());
                set
            }
            AstOp::FPS(s, _) => {
                let mut set = BTreeSet::new();
                set.insert(s.clone());
                set
            }
            _ => {
                let mut set = BTreeSet::new();
                for child in self.children() {
                    set.extend(child.variables().iter().cloned());
                }
                set
            }
        }
    }

    pub fn is_inherently_symbolic(&self) -> bool {
        matches!(
            self,
            AstOp::Union(..) | AstOp::Intersection(..) | AstOp::Widen(..)
        )
    }

    pub fn symbolic(&self) -> bool {
        self.is_inherently_symbolic() || !self.variables().is_empty()
    }

    pub fn concrete(&self) -> bool {
        !self.symbolic()
    }

    /// Returns the base theory of this operation.
    pub fn base_theories(&self) -> Theories {
        match self {
            // Cross-sort ops: derive theory from children
            AstOp::Not(child) => {
                let t = child.op().base_theories();
                if t.contains(Theories::BITVEC) {
                    Theories::BITVEC
                } else {
                    Theories::BOOLEAN
                }
            }
            AstOp::And(args) | AstOp::Or(args) | AstOp::Xor(args) => {
                if let Some(first) = args.first() {
                    let t = first.op().base_theories();
                    if t.contains(Theories::BITVEC) {
                        return Theories::BITVEC;
                    }
                }
                Theories::BOOLEAN
            }

            AstOp::BoolS(_)
            | AstOp::BoolV(_)
            | AstOp::Eq(..)
            | AstOp::Neq(..)
            | AstOp::ULT(..)
            | AstOp::ULE(..)
            | AstOp::UGT(..)
            | AstOp::UGE(..)
            | AstOp::SLT(..)
            | AstOp::SLE(..)
            | AstOp::SGT(..)
            | AstOp::SGE(..)
            | AstOp::FpLt(..)
            | AstOp::FpLeq(..)
            | AstOp::FpGt(..)
            | AstOp::FpGeq(..)
            | AstOp::FpIsNan(_)
            | AstOp::FpIsInf(_)
            | AstOp::StrContains(..)
            | AstOp::StrPrefixOf(..)
            | AstOp::StrSuffixOf(..)
            | AstOp::StrIsDigit(_) => Theories::BOOLEAN,

            AstOp::BVS(..)
            | AstOp::BVV(_)
            | AstOp::Neg(_)
            | AstOp::Add(_)
            | AstOp::Sub(..)
            | AstOp::Mul(_)
            | AstOp::UDiv(..)
            | AstOp::SDiv(..)
            | AstOp::URem(..)
            | AstOp::SRem(..)
            | AstOp::ShL(..)
            | AstOp::LShR(..)
            | AstOp::AShR(..)
            | AstOp::RotateLeft(..)
            | AstOp::RotateRight(..)
            | AstOp::Extract(..)
            | AstOp::ZeroExt(..)
            | AstOp::SignExt(..)
            | AstOp::Concat(_)
            | AstOp::ByteReverse(_)
            | AstOp::FpToIEEEBV(_)
            | AstOp::FpToUBV(..)
            | AstOp::FpToSBV(..)
            | AstOp::StrLen(_)
            | AstOp::StrIndexOf(..)
            | AstOp::StrToBV(_)
            | AstOp::Union(..)
            | AstOp::Intersection(..)
            | AstOp::Widen(..) => Theories::BITVEC,

            AstOp::FPS(..)
            | AstOp::FPV(_)
            | AstOp::FpNeg(_)
            | AstOp::FpAbs(_)
            | AstOp::FpAdd(..)
            | AstOp::FpSub(..)
            | AstOp::FpMul(..)
            | AstOp::FpDiv(..)
            | AstOp::FpSqrt(..)
            | AstOp::FpToFp(..)
            | AstOp::FpFP(..)
            | AstOp::BvToFp(..)
            | AstOp::BvToFpSigned(..)
            | AstOp::BvToFpUnsigned(..) => Theories::FLOAT,

            AstOp::StringS(_)
            | AstOp::StringV(_)
            | AstOp::StrConcat(..)
            | AstOp::StrSubstr(..)
            | AstOp::StrReplace(..)
            | AstOp::BVToStr(_) => Theories::STRING,

            AstOp::If(_, t, _) => t.op().base_theories(),
        }
    }

    /// Compute the bitvec size for BV operations.
    pub fn size(&self) -> u32 {
        match self {
            AstOp::BVS(_, size) => *size,
            AstOp::BVV(bv) => bv.len(),
            AstOp::Not(a) | AstOp::Neg(a) | AstOp::ByteReverse(a) => a.size(),
            AstOp::And(args)
            | AstOp::Or(args)
            | AstOp::Xor(args)
            | AstOp::Add(args)
            | AstOp::Mul(args) => args.first().map_or(0, |a| a.size()),
            AstOp::Sub(a, _)
            | AstOp::UDiv(a, _)
            | AstOp::SDiv(a, _)
            | AstOp::URem(a, _)
            | AstOp::SRem(a, _)
            | AstOp::ShL(a, _)
            | AstOp::LShR(a, _)
            | AstOp::AShR(a, _)
            | AstOp::RotateLeft(a, _)
            | AstOp::RotateRight(a, _)
            | AstOp::Union(a, _)
            | AstOp::Intersection(a, _)
            | AstOp::Widen(a, _) => a.size(),
            AstOp::Extract(_, high, low) => high - low + 1,
            AstOp::Concat(args) => args.iter().map(|a| a.size()).sum(),
            AstOp::ZeroExt(a, ext) | AstOp::SignExt(a, ext) => a.size() + ext,
            AstOp::FpToIEEEBV(fp) => fp.size(),
            AstOp::FpToUBV(_, size, _) | AstOp::FpToSBV(_, size, _) => *size,
            AstOp::StrLen(_) | AstOp::StrToBV(_) | AstOp::StrIndexOf(..) => 64,
            AstOp::If(_, t, _) => t.size(),
            // For non-BV ops, size is 0
            _ => 0,
        }
    }

    /// Compute the float sort for float operations.
    pub fn sort(&self) -> FSort {
        match self {
            AstOp::FPS(_, sort) => *sort,
            AstOp::FPV(value) => value.fsort(),
            AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpSqrt(a, _)
            | AstOp::FpAdd(a, _, _)
            | AstOp::FpSub(a, _, _)
            | AstOp::FpMul(a, _, _)
            | AstOp::FpDiv(a, _, _) => a.op().sort(),
            AstOp::FpToFp(_, sort, _)
            | AstOp::BvToFp(_, sort)
            | AstOp::BvToFpSigned(_, sort, _)
            | AstOp::BvToFpUnsigned(_, sort, _) => *sort,
            AstOp::FpFP(_sign, exp, sig) => {
                FSort::new(exp.op().size(), sig.op().size().saturating_sub(1))
            }
            AstOp::If(_, t, _) => t.op().sort(),
            _ => FSort::new(0, 0),
        }
    }

    /// Check if two ops have the same sort (for same-sort validation).
    pub fn check_same_sort(&self, other: &Self) -> bool {
        let t1 = self.base_theories();
        let t2 = other.base_theories();
        if t1 != t2 {
            return false;
        }
        if t1 == Theories::BITVEC {
            self.size() == other.size()
        } else if t1 == Theories::FLOAT {
            self.sort() == other.sort()
        } else {
            true
        }
    }
}

pub struct AstOpChildIter<'a, 'c> {
    op: &'a AstOp<'c>,
    index: usize,
}

impl<'a, 'c> Iterator for AstOpChildIter<'a, 'c> {
    type Item = AstRef<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.op.get_child(self.index);
        if result.is_some() {
            self.index += 1;
        }
        result
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.op.num_children().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, 'c> ExactSizeIterator for AstOpChildIter<'a, 'c> {
    fn len(&self) -> usize {
        self.op.num_children().saturating_sub(self.index)
    }
}
