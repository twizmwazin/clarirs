use std::collections::BTreeSet;

use serde::Serialize;

use crate::prelude::*;

/// The type of an AST node, determined by its operation.
/// BVs carry their bit-width, Floats carry their FSort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum AstType {
    Bool,
    BitVec(u32),
    Float(FSort),
    String,
}

impl AstType {
    pub fn size(&self) -> u32 {
        match self {
            AstType::Bool => 0,
            AstType::BitVec(w) => *w,
            AstType::Float(sort) => sort.size(),
            AstType::String => 0,
        }
    }

    pub fn sort(&self) -> Option<FSort> {
        match self {
            AstType::Float(sort) => Some(*sort),
            _ => None,
        }
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, AstType::Bool)
    }

    pub fn is_bitvec(&self) -> bool {
        matches!(self, AstType::BitVec(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, AstType::Float(_))
    }

    pub fn is_string(&self) -> bool {
        matches!(self, AstType::String)
    }
}

/// A single unified enum of all AST operations across all theories.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum Op<'c> {
    // ── Boolean leaf / value ─────────────────────────────────────────
    BoolS(InternedString),
    BoolV(bool),

    // ── Boolean logic ────────────────────────────────────────────────
    Not(AstRef<'c>),
    And(Vec<AstRef<'c>>),
    Or(Vec<AstRef<'c>>),
    Xor(AstRef<'c>, AstRef<'c>),

    // ── Boolean equality ─────────────────────────────────────────────
    BoolEq(AstRef<'c>, AstRef<'c>),
    BoolNeq(AstRef<'c>, AstRef<'c>),

    // ── BV comparisons (return Bool) ─────────────────────────────────
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

    // ── Float comparisons (return Bool) ──────────────────────────────
    FpEq(AstRef<'c>, AstRef<'c>),
    FpNeq(AstRef<'c>, AstRef<'c>),
    FpLt(AstRef<'c>, AstRef<'c>),
    FpLeq(AstRef<'c>, AstRef<'c>),
    FpGt(AstRef<'c>, AstRef<'c>),
    FpGeq(AstRef<'c>, AstRef<'c>),
    FpIsNan(AstRef<'c>),
    FpIsInf(AstRef<'c>),

    // ── String comparisons (return Bool) ─────────────────────────────
    StrContains(AstRef<'c>, AstRef<'c>),
    StrPrefixOf(AstRef<'c>, AstRef<'c>),
    StrSuffixOf(AstRef<'c>, AstRef<'c>),
    StrIsDigit(AstRef<'c>),
    StrEq(AstRef<'c>, AstRef<'c>),
    StrNeq(AstRef<'c>, AstRef<'c>),

    // ── Boolean ITE ──────────────────────────────────────────────────
    BoolITE(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // ── BitVec leaf / value ──────────────────────────────────────────
    BVS(InternedString, u32),
    BVV(BitVec),

    // ── BitVec bitwise ───────────────────────────────────────────────
    BVNot(AstRef<'c>),
    BVAnd(Vec<AstRef<'c>>),
    BVOr(Vec<AstRef<'c>>),
    BVXor(Vec<AstRef<'c>>),

    // ── BitVec arithmetic ────────────────────────────────────────────
    Neg(AstRef<'c>),
    Add(Vec<AstRef<'c>>),
    Sub(AstRef<'c>, AstRef<'c>),
    Mul(Vec<AstRef<'c>>),
    UDiv(AstRef<'c>, AstRef<'c>),
    SDiv(AstRef<'c>, AstRef<'c>),
    URem(AstRef<'c>, AstRef<'c>),
    SRem(AstRef<'c>, AstRef<'c>),

    // ── BitVec shifts / rotates ──────────────────────────────────────
    ShL(AstRef<'c>, AstRef<'c>),
    LShR(AstRef<'c>, AstRef<'c>),
    AShR(AstRef<'c>, AstRef<'c>),
    RotateLeft(AstRef<'c>, AstRef<'c>),
    RotateRight(AstRef<'c>, AstRef<'c>),

    // ── BitVec bit manipulation ──────────────────────────────────────
    ZeroExt(AstRef<'c>, u32),
    SignExt(AstRef<'c>, u32),
    Extract(AstRef<'c>, u32, u32),
    Concat(Vec<AstRef<'c>>),
    ByteReverse(AstRef<'c>),

    // ── BitVec cross-type conversions ────────────────────────────────
    FpToIEEEBV(AstRef<'c>),
    FpToUBV(AstRef<'c>, u32, FPRM),
    FpToSBV(AstRef<'c>, u32, FPRM),
    StrLen(AstRef<'c>),
    StrIndexOf(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrToBV(AstRef<'c>),

    // ── BitVec ITE ───────────────────────────────────────────────────
    BVITE(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // ── BitVec VSA ops ───────────────────────────────────────────────
    Union(AstRef<'c>, AstRef<'c>),
    Intersection(AstRef<'c>, AstRef<'c>),
    Widen(AstRef<'c>, AstRef<'c>),

    // ── Float leaf / value ───────────────────────────────────────────
    FPS(InternedString, FSort),
    FPV(Float),

    // ── Float arithmetic ─────────────────────────────────────────────
    FpNeg(AstRef<'c>),
    FpAbs(AstRef<'c>),
    FpAdd(AstRef<'c>, AstRef<'c>, FPRM),
    FpSub(AstRef<'c>, AstRef<'c>, FPRM),
    FpMul(AstRef<'c>, AstRef<'c>, FPRM),
    FpDiv(AstRef<'c>, AstRef<'c>, FPRM),
    FpSqrt(AstRef<'c>, FPRM),

    // ── Float conversions ────────────────────────────────────────────
    FpToFp(AstRef<'c>, FSort, FPRM),
    FpFP(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BvToFp(AstRef<'c>, FSort),
    BvToFpSigned(AstRef<'c>, FSort, FPRM),
    BvToFpUnsigned(AstRef<'c>, FSort, FPRM),

    // ── Float ITE ────────────────────────────────────────────────────
    FpITE(AstRef<'c>, AstRef<'c>, AstRef<'c>),

    // ── String leaf / value ──────────────────────────────────────────
    StringS(InternedString),
    StringV(String),

    // ── String operations ────────────────────────────────────────────
    StrConcat(AstRef<'c>, AstRef<'c>),
    StrSubstr(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    StrReplace(AstRef<'c>, AstRef<'c>, AstRef<'c>),
    BVToStr(AstRef<'c>),

    // ── String ITE ───────────────────────────────────────────────────
    StrITE(AstRef<'c>, AstRef<'c>, AstRef<'c>),
}

impl<'c> Op<'c> {
    /// Returns the return type of this operation.
    pub fn return_type(&self) -> AstType {
        match self {
            // ── Bool return ──────────────────────────────────────────
            Op::BoolS(_) | Op::BoolV(_) => AstType::Bool,
            Op::Not(_) | Op::And(_) | Op::Or(_) | Op::Xor(..) => AstType::Bool,
            Op::BoolEq(..) | Op::BoolNeq(..) => AstType::Bool,
            Op::Eq(..) | Op::Neq(..) => AstType::Bool,
            Op::ULT(..) | Op::ULE(..) | Op::UGT(..) | Op::UGE(..) => AstType::Bool,
            Op::SLT(..) | Op::SLE(..) | Op::SGT(..) | Op::SGE(..) => AstType::Bool,
            Op::FpEq(..) | Op::FpNeq(..) | Op::FpLt(..) | Op::FpLeq(..) => AstType::Bool,
            Op::FpGt(..) | Op::FpGeq(..) | Op::FpIsNan(_) | Op::FpIsInf(_) => AstType::Bool,
            Op::StrContains(..) | Op::StrPrefixOf(..) | Op::StrSuffixOf(..) => AstType::Bool,
            Op::StrIsDigit(_) | Op::StrEq(..) | Op::StrNeq(..) => AstType::Bool,
            Op::BoolITE(_, t, _) => t.return_type(),

            // ── BitVec return ────────────────────────────────────────
            Op::BVS(_, w) => AstType::BitVec(*w),
            Op::BVV(bv) => AstType::BitVec(bv.len()),
            Op::BVNot(a) | Op::Neg(a) | Op::ByteReverse(a) => a.return_type(),
            Op::BVITE(_, t, _) => t.return_type(),
            Op::BVAnd(args) | Op::BVOr(args) | Op::BVXor(args) => args[0].return_type(),
            Op::Add(args) | Op::Mul(args) => args[0].return_type(),
            Op::Sub(a, _) | Op::UDiv(a, _) | Op::SDiv(a, _) => a.return_type(),
            Op::URem(a, _) | Op::SRem(a, _) => a.return_type(),
            Op::ShL(a, _) | Op::LShR(a, _) | Op::AShR(a, _) => a.return_type(),
            Op::RotateLeft(a, _) | Op::RotateRight(a, _) => a.return_type(),
            Op::Union(a, _) | Op::Intersection(a, _) | Op::Widen(a, _) => a.return_type(),
            Op::Extract(_, high, low) => AstType::BitVec(high - low + 1),
            Op::Concat(args) => {
                AstType::BitVec(args.iter().map(|a| a.return_type().size()).sum())
            }
            Op::ZeroExt(a, ext) | Op::SignExt(a, ext) => {
                AstType::BitVec(a.return_type().size() + ext)
            }
            Op::FpToIEEEBV(a) => AstType::BitVec(a.return_type().size()),
            Op::FpToUBV(_, size, _) | Op::FpToSBV(_, size, _) => AstType::BitVec(*size),
            Op::StrLen(_) | Op::StrToBV(_) | Op::StrIndexOf(..) => AstType::BitVec(64),

            // ── Float return ─────────────────────────────────────────
            Op::FPS(_, sort) => AstType::Float(*sort),
            Op::FPV(f) => AstType::Float(f.fsort()),
            Op::FpNeg(a) | Op::FpAbs(a) => a.return_type(),
            Op::FpAdd(a, _, _) | Op::FpSub(a, _, _) => a.return_type(),
            Op::FpMul(a, _, _) | Op::FpDiv(a, _, _) => a.return_type(),
            Op::FpSqrt(a, _) => a.return_type(),
            Op::FpToFp(_, sort, _) => AstType::Float(*sort),
            Op::BvToFp(_, sort) => AstType::Float(*sort),
            Op::BvToFpSigned(_, sort, _) | Op::BvToFpUnsigned(_, sort, _) => AstType::Float(*sort),
            Op::FpFP(_sign, exp, sig) => {
                let exp_size = exp.return_type().size();
                let sig_size = sig.return_type().size();
                AstType::Float(FSort::new(exp_size, sig_size.saturating_sub(1)))
            }
            Op::FpITE(_, t, _) => t.return_type(),

            // ── String return ────────────────────────────────────────
            Op::StringS(_) | Op::StringV(_) => AstType::String,
            Op::StrConcat(..) | Op::StrSubstr(..) | Op::StrReplace(..) => AstType::String,
            Op::BVToStr(_) => AstType::String,
            Op::StrITE(_, t, _) => t.return_type(),
        }
    }

    /// Number of AST children this op has.
    pub fn num_children(&self) -> usize {
        match self {
            // 0 children (leaves)
            Op::BoolS(_) | Op::BoolV(_) | Op::BVS(..) | Op::BVV(_) | Op::FPS(..) | Op::FPV(_)
            | Op::StringS(_) | Op::StringV(_) => 0,

            // 1 child
            Op::Not(_) | Op::BVNot(_) | Op::Neg(_) | Op::ByteReverse(_)
            | Op::ZeroExt(_, _) | Op::SignExt(_, _) | Op::Extract(_, _, _)
            | Op::FpToIEEEBV(_) | Op::FpToUBV(_, _, _) | Op::FpToSBV(_, _, _)
            | Op::StrLen(_) | Op::StrToBV(_)
            | Op::FpNeg(_) | Op::FpAbs(_) | Op::FpSqrt(_, _)
            | Op::FpToFp(_, _, _) | Op::BvToFp(_, _)
            | Op::BvToFpSigned(_, _, _) | Op::BvToFpUnsigned(_, _, _)
            | Op::BVToStr(_)
            | Op::FpIsNan(_) | Op::FpIsInf(_) | Op::StrIsDigit(_) => 1,

            // 2 children
            Op::Xor(..) | Op::BoolEq(..) | Op::BoolNeq(..)
            | Op::Eq(..) | Op::Neq(..)
            | Op::ULT(..) | Op::ULE(..) | Op::UGT(..) | Op::UGE(..)
            | Op::SLT(..) | Op::SLE(..) | Op::SGT(..) | Op::SGE(..)
            | Op::FpEq(..) | Op::FpNeq(..) | Op::FpLt(..) | Op::FpLeq(..)
            | Op::FpGt(..) | Op::FpGeq(..)
            | Op::StrContains(..) | Op::StrPrefixOf(..) | Op::StrSuffixOf(..)
            | Op::StrEq(..) | Op::StrNeq(..)
            | Op::Sub(..) | Op::UDiv(..) | Op::SDiv(..) | Op::URem(..) | Op::SRem(..)
            | Op::ShL(..) | Op::LShR(..) | Op::AShR(..)
            | Op::RotateLeft(..) | Op::RotateRight(..)
            | Op::Union(..) | Op::Intersection(..) | Op::Widen(..)
            | Op::FpAdd(..) | Op::FpSub(..) | Op::FpMul(..) | Op::FpDiv(..)
            | Op::StrConcat(..) => 2,

            // 3 children
            Op::BoolITE(..) | Op::BVITE(..) | Op::FpITE(..) | Op::StrITE(..)
            | Op::StrIndexOf(..) | Op::FpFP(..)
            | Op::StrSubstr(..) | Op::StrReplace(..) => 3,

            // N-ary
            Op::And(args) | Op::Or(args)
            | Op::BVAnd(args) | Op::BVOr(args) | Op::BVXor(args)
            | Op::Add(args) | Op::Mul(args)
            | Op::Concat(args) => args.len(),
        }
    }

    /// Get the child at the given index, or None if out of bounds.
    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        match self {
            // 0 children
            Op::BoolS(_) | Op::BoolV(_) | Op::BVS(..) | Op::BVV(_) | Op::FPS(..) | Op::FPV(_)
            | Op::StringS(_) | Op::StringV(_) => None,

            // 1 child
            Op::Not(a) | Op::BVNot(a) | Op::Neg(a) | Op::ByteReverse(a)
            | Op::ZeroExt(a, _) | Op::SignExt(a, _) | Op::Extract(a, _, _)
            | Op::FpToIEEEBV(a) | Op::FpToUBV(a, _, _) | Op::FpToSBV(a, _, _)
            | Op::StrLen(a) | Op::StrToBV(a)
            | Op::FpNeg(a) | Op::FpAbs(a) | Op::FpSqrt(a, _)
            | Op::FpToFp(a, _, _) | Op::BvToFp(a, _)
            | Op::BvToFpSigned(a, _, _) | Op::BvToFpUnsigned(a, _, _)
            | Op::BVToStr(a)
            | Op::FpIsNan(a) | Op::FpIsInf(a) | Op::StrIsDigit(a) => {
                if index == 0 { Some(a.clone()) } else { None }
            }

            // 2 children
            Op::Xor(a, b) | Op::BoolEq(a, b) | Op::BoolNeq(a, b)
            | Op::Eq(a, b) | Op::Neq(a, b)
            | Op::ULT(a, b) | Op::ULE(a, b) | Op::UGT(a, b) | Op::UGE(a, b)
            | Op::SLT(a, b) | Op::SLE(a, b) | Op::SGT(a, b) | Op::SGE(a, b)
            | Op::FpEq(a, b) | Op::FpNeq(a, b) | Op::FpLt(a, b) | Op::FpLeq(a, b)
            | Op::FpGt(a, b) | Op::FpGeq(a, b)
            | Op::StrContains(a, b) | Op::StrPrefixOf(a, b) | Op::StrSuffixOf(a, b)
            | Op::StrEq(a, b) | Op::StrNeq(a, b)
            | Op::Sub(a, b) | Op::UDiv(a, b) | Op::SDiv(a, b)
            | Op::URem(a, b) | Op::SRem(a, b)
            | Op::ShL(a, b) | Op::LShR(a, b) | Op::AShR(a, b)
            | Op::RotateLeft(a, b) | Op::RotateRight(a, b)
            | Op::Union(a, b) | Op::Intersection(a, b) | Op::Widen(a, b)
            | Op::StrConcat(a, b) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                _ => None,
            },

            // 2 children (float binary ops have FPRM but only 2 AST children)
            Op::FpAdd(a, b, _) | Op::FpSub(a, b, _)
            | Op::FpMul(a, b, _) | Op::FpDiv(a, b, _) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                _ => None,
            },

            // 3 children
            Op::BoolITE(a, b, c) | Op::BVITE(a, b, c) | Op::FpITE(a, b, c)
            | Op::StrITE(a, b, c)
            | Op::StrIndexOf(a, b, c) | Op::FpFP(a, b, c)
            | Op::StrSubstr(a, b, c) | Op::StrReplace(a, b, c) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                2 => Some(c.clone()),
                _ => None,
            },

            // N-ary
            Op::And(args) | Op::Or(args)
            | Op::BVAnd(args) | Op::BVOr(args) | Op::BVXor(args)
            | Op::Add(args) | Op::Mul(args)
            | Op::Concat(args) => args.get(index).cloned(),
        }
    }

    pub fn child_iter(&self) -> OpChildIter<'_, 'c> {
        OpChildIter { op: self, index: 0 }
    }

    pub fn depth(&self) -> u32 {
        1 + self.child_iter().map(|c| c.depth()).max().unwrap_or(0)
    }

    pub fn is_leaf(&self) -> bool {
        self.num_children() == 0
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Op::BoolV(true))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Op::BoolV(false))
    }

    pub fn variables(&self) -> BTreeSet<InternedString> {
        match self {
            Op::BoolS(s) | Op::BVS(s, _) | Op::FPS(s, _) | Op::StringS(s) => {
                let mut set = BTreeSet::new();
                set.insert(s.clone());
                set
            }
            _ => {
                let mut set = BTreeSet::new();
                for child in self.child_iter() {
                    set.extend(child.variables().iter().cloned());
                }
                set
            }
        }
    }

    pub fn is_inherently_symbolic(&self) -> bool {
        matches!(
            self,
            Op::Union(..) | Op::Intersection(..) | Op::Widen(..)
        )
    }

    pub fn symbolic(&self) -> bool {
        self.is_inherently_symbolic() || !self.variables().is_empty()
    }

    pub fn concrete(&self) -> bool {
        !self.symbolic()
    }

    pub fn check_same_sort(&self, other: &Self) -> bool {
        self.return_type() == other.return_type()
    }
}

pub struct OpChildIter<'a, 'c> {
    op: &'a Op<'c>,
    index: usize,
}

impl<'a, 'c> Iterator for OpChildIter<'a, 'c> {
    type Item = AstRef<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.op.get_child(self.index);
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

impl ExactSizeIterator for OpChildIter<'_, '_> {
    fn len(&self) -> usize {
        self.op.num_children().saturating_sub(self.index)
    }
}
