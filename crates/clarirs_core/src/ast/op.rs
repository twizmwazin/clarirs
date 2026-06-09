use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use serde::Serialize;

use crate::ast::node::{AstRef, BitVecAst, BoolAst, FloatAst, StringAst};
use crate::prelude::*;

/// The runtime type ("sort") of an AST node. Stored on every [`AstNode`] so the
/// type of an expression can be queried without inspecting its operation, and
/// so size/sort information is available in O(1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum AstType {
    Bool,
    BitVec(u32),
    Float(FSort),
    String,
}

impl AstType {
    /// The bit width associated with this type. Bitvectors report their width
    /// and floats their total IEEE width; bools and strings report 0.
    pub fn size(&self) -> u32 {
        match self {
            AstType::Bool => 0,
            AstType::BitVec(width) => *width,
            AstType::Float(sort) => sort.size(),
            AstType::String => 0,
        }
    }

    /// The float sort, if this is a float type.
    pub fn fsort(&self) -> Option<FSort> {
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

/// The single operation enum for all AST nodes. A node's type (bool, bitvec,
/// float, string) is determined by its operation together with the types of its
/// children, and is cached on the [`AstNode`] as an [`AstType`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum AstOp<'c> {
    // Boolean leaves and operations
    BoolS(InternedString),
    BoolV(bool),
    BoolXor(BoolAst<'c>, BoolAst<'c>),
    BoolEq(BoolAst<'c>, BoolAst<'c>),
    BoolNeq(BoolAst<'c>, BoolAst<'c>),

    // Polymorphic boolean/bitvector operations (the child type determines the
    // result type)
    Not(AstRef<'c>),
    And(Vec<AstRef<'c>>),
    Or(Vec<AstRef<'c>>),
    ITE(BoolAst<'c>, AstRef<'c>, AstRef<'c>),

    // Bitvector comparisons (produce a bool)
    Eq(BitVecAst<'c>, BitVecAst<'c>),
    Neq(BitVecAst<'c>, BitVecAst<'c>),
    ULT(BitVecAst<'c>, BitVecAst<'c>),
    ULE(BitVecAst<'c>, BitVecAst<'c>),
    UGT(BitVecAst<'c>, BitVecAst<'c>),
    UGE(BitVecAst<'c>, BitVecAst<'c>),
    SLT(BitVecAst<'c>, BitVecAst<'c>),
    SLE(BitVecAst<'c>, BitVecAst<'c>),
    SGT(BitVecAst<'c>, BitVecAst<'c>),
    SGE(BitVecAst<'c>, BitVecAst<'c>),

    // Float comparisons (produce a bool)
    FpEq(FloatAst<'c>, FloatAst<'c>),
    FpNeq(FloatAst<'c>, FloatAst<'c>),
    FpLt(FloatAst<'c>, FloatAst<'c>),
    FpLeq(FloatAst<'c>, FloatAst<'c>),
    FpGt(FloatAst<'c>, FloatAst<'c>),
    FpGeq(FloatAst<'c>, FloatAst<'c>),
    FpIsNan(FloatAst<'c>),
    FpIsInf(FloatAst<'c>),

    // String predicates (produce a bool)
    StrContains(StringAst<'c>, StringAst<'c>),
    StrPrefixOf(StringAst<'c>, StringAst<'c>),
    StrSuffixOf(StringAst<'c>, StringAst<'c>),
    StrIsDigit(StringAst<'c>),
    StrEq(StringAst<'c>, StringAst<'c>),
    StrNeq(StringAst<'c>, StringAst<'c>),

    // Bitvector leaves and operations
    BVS(InternedString, u32),
    BVV(BitVec),
    Neg(BitVecAst<'c>),
    Xor(Vec<BitVecAst<'c>>),
    Add(Vec<BitVecAst<'c>>),
    Sub(BitVecAst<'c>, BitVecAst<'c>),
    Mul(Vec<BitVecAst<'c>>),
    UDiv(BitVecAst<'c>, BitVecAst<'c>),
    SDiv(BitVecAst<'c>, BitVecAst<'c>),
    URem(BitVecAst<'c>, BitVecAst<'c>),
    SRem(BitVecAst<'c>, BitVecAst<'c>),
    ShL(BitVecAst<'c>, BitVecAst<'c>),
    LShR(BitVecAst<'c>, BitVecAst<'c>),
    AShR(BitVecAst<'c>, BitVecAst<'c>),
    RotateLeft(BitVecAst<'c>, BitVecAst<'c>),
    RotateRight(BitVecAst<'c>, BitVecAst<'c>),
    ZeroExt(BitVecAst<'c>, u32),
    SignExt(BitVecAst<'c>, u32),
    Extract(BitVecAst<'c>, u32, u32),
    Concat(Vec<BitVecAst<'c>>),
    ByteReverse(BitVecAst<'c>),
    FpToIEEEBV(FloatAst<'c>),
    FpToUBV(FloatAst<'c>, u32, FPRM),
    FpToSBV(FloatAst<'c>, u32, FPRM),
    StrLen(StringAst<'c>),
    StrIndexOf(StringAst<'c>, StringAst<'c>, BitVecAst<'c>),
    StrToBV(StringAst<'c>),

    // VSA bitvector operations (always symbolic)
    Union(BitVecAst<'c>, BitVecAst<'c>),
    Intersection(BitVecAst<'c>, BitVecAst<'c>),
    Widen(BitVecAst<'c>, BitVecAst<'c>),

    // Float leaves and operations
    FPS(InternedString, FSort),
    FPV(Float),
    FpNeg(FloatAst<'c>),
    FpAbs(FloatAst<'c>),
    FpAdd(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSub(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpMul(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpDiv(FloatAst<'c>, FloatAst<'c>, FPRM),
    FpSqrt(FloatAst<'c>, FPRM),
    /// Transform a float to another float of a different size, preserving the value.
    FpToFp(FloatAst<'c>, FSort, FPRM),
    /// Construct a float from sign, exponent, and significand bitvectors
    FpFP(BitVecAst<'c>, BitVecAst<'c>, BitVecAst<'c>),
    /// Transform an IEEE 754 bitvector to a float
    BvToFp(BitVecAst<'c>, FSort),
    /// Transform a signed 2's complement bitvector to a float
    BvToFpSigned(BitVecAst<'c>, FSort, FPRM),
    /// Transform an unsigned 2's complement bitvector to a float
    BvToFpUnsigned(BitVecAst<'c>, FSort, FPRM),

    // String leaves and operations
    StringS(InternedString),
    StringV(String),
    StrConcat(StringAst<'c>, StringAst<'c>),
    StrSubstr(StringAst<'c>, BitVecAst<'c>, BitVecAst<'c>),
    StrReplace(StringAst<'c>, StringAst<'c>, StringAst<'c>),
    BVToStr(BitVecAst<'c>),
}

impl<'c> AstOp<'c> {
    /// Returns the child AST at the given index, or `None` if out of range.
    pub fn child_at(&self, index: usize) -> Option<AstRef<'c>> {
        match self {
            // Leaves have no children
            AstOp::BoolS(..)
            | AstOp::BoolV(..)
            | AstOp::BVS(..)
            | AstOp::BVV(..)
            | AstOp::FPS(..)
            | AstOp::FPV(..)
            | AstOp::StringS(..)
            | AstOp::StringV(..) => None,

            // N-ary operations index directly into their Vec (O(1))
            AstOp::And(v)
            | AstOp::Or(v)
            | AstOp::Xor(v)
            | AstOp::Add(v)
            | AstOp::Mul(v)
            | AstOp::Concat(v) => v.get(index).cloned(),

            // Unary operations
            AstOp::Not(a)
            | AstOp::Neg(a)
            | AstOp::ByteReverse(a)
            | AstOp::ZeroExt(a, _)
            | AstOp::SignExt(a, _)
            | AstOp::Extract(a, _, _)
            | AstOp::StrLen(a)
            | AstOp::StrToBV(a)
            | AstOp::FpToIEEEBV(a)
            | AstOp::FpToUBV(a, _, _)
            | AstOp::FpToSBV(a, _, _)
            | AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpSqrt(a, _)
            | AstOp::FpToFp(a, _, _)
            | AstOp::BvToFp(a, _)
            | AstOp::BvToFpSigned(a, _, _)
            | AstOp::BvToFpUnsigned(a, _, _)
            | AstOp::FpIsNan(a)
            | AstOp::FpIsInf(a)
            | AstOp::StrIsDigit(a)
            | AstOp::BVToStr(a) => (index == 0).then(|| a.clone()),

            // Binary operations
            AstOp::BoolXor(a, b)
            | AstOp::BoolEq(a, b)
            | AstOp::BoolNeq(a, b)
            | AstOp::Eq(a, b)
            | AstOp::Neq(a, b)
            | AstOp::ULT(a, b)
            | AstOp::ULE(a, b)
            | AstOp::UGT(a, b)
            | AstOp::UGE(a, b)
            | AstOp::SLT(a, b)
            | AstOp::SLE(a, b)
            | AstOp::SGT(a, b)
            | AstOp::SGE(a, b)
            | AstOp::FpEq(a, b)
            | AstOp::FpNeq(a, b)
            | AstOp::FpLt(a, b)
            | AstOp::FpLeq(a, b)
            | AstOp::FpGt(a, b)
            | AstOp::FpGeq(a, b)
            | AstOp::StrContains(a, b)
            | AstOp::StrPrefixOf(a, b)
            | AstOp::StrSuffixOf(a, b)
            | AstOp::StrEq(a, b)
            | AstOp::StrNeq(a, b)
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
            | AstOp::Union(a, b)
            | AstOp::Intersection(a, b)
            | AstOp::Widen(a, b)
            | AstOp::FpAdd(a, b, _)
            | AstOp::FpSub(a, b, _)
            | AstOp::FpMul(a, b, _)
            | AstOp::FpDiv(a, b, _)
            | AstOp::StrConcat(a, b) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                _ => None,
            },

            // Ternary operations
            AstOp::ITE(a, b, c)
            | AstOp::StrIndexOf(a, b, c)
            | AstOp::FpFP(a, b, c)
            | AstOp::StrSubstr(a, b, c)
            | AstOp::StrReplace(a, b, c) => match index {
                0 => Some(a.clone()),
                1 => Some(b.clone()),
                2 => Some(c.clone()),
                _ => None,
            },
        }
    }

    /// Returns the number of children of this operation.
    pub fn num_children(&self) -> usize {
        match self {
            AstOp::BoolS(..)
            | AstOp::BoolV(..)
            | AstOp::BVS(..)
            | AstOp::BVV(..)
            | AstOp::FPS(..)
            | AstOp::FPV(..)
            | AstOp::StringS(..)
            | AstOp::StringV(..) => 0,

            AstOp::And(v)
            | AstOp::Or(v)
            | AstOp::Xor(v)
            | AstOp::Add(v)
            | AstOp::Mul(v)
            | AstOp::Concat(v) => v.len(),

            AstOp::Not(_)
            | AstOp::Neg(_)
            | AstOp::ByteReverse(_)
            | AstOp::ZeroExt(..)
            | AstOp::SignExt(..)
            | AstOp::Extract(..)
            | AstOp::StrLen(_)
            | AstOp::StrToBV(_)
            | AstOp::FpToIEEEBV(_)
            | AstOp::FpToUBV(..)
            | AstOp::FpToSBV(..)
            | AstOp::FpNeg(_)
            | AstOp::FpAbs(_)
            | AstOp::FpSqrt(..)
            | AstOp::FpToFp(..)
            | AstOp::BvToFp(..)
            | AstOp::BvToFpSigned(..)
            | AstOp::BvToFpUnsigned(..)
            | AstOp::FpIsNan(_)
            | AstOp::FpIsInf(_)
            | AstOp::StrIsDigit(_)
            | AstOp::BVToStr(_) => 1,

            AstOp::BoolXor(..)
            | AstOp::BoolEq(..)
            | AstOp::BoolNeq(..)
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
            | AstOp::FpEq(..)
            | AstOp::FpNeq(..)
            | AstOp::FpLt(..)
            | AstOp::FpLeq(..)
            | AstOp::FpGt(..)
            | AstOp::FpGeq(..)
            | AstOp::StrContains(..)
            | AstOp::StrPrefixOf(..)
            | AstOp::StrSuffixOf(..)
            | AstOp::StrEq(..)
            | AstOp::StrNeq(..)
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
            | AstOp::Union(..)
            | AstOp::Intersection(..)
            | AstOp::Widen(..)
            | AstOp::FpAdd(..)
            | AstOp::FpSub(..)
            | AstOp::FpMul(..)
            | AstOp::FpDiv(..)
            | AstOp::StrConcat(..) => 2,

            AstOp::ITE(..)
            | AstOp::StrIndexOf(..)
            | AstOp::FpFP(..)
            | AstOp::StrSubstr(..)
            | AstOp::StrReplace(..) => 3,
        }
    }

    pub fn child_iter(&self) -> AstOpChildIter<'_, 'c> {
        AstOpChildIter { op: self, index: 0 }
    }

    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        self.child_at(index)
    }

    pub fn is_true(&self) -> bool {
        matches!(self, AstOp::BoolV(true))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, AstOp::BoolV(false))
    }

    /// Returns true if the op is inherently symbolic regardless of whether it
    /// has variables. VSA operations (Union, Intersection, Widen) are always
    /// symbolic because they represent abstract multi-valued results.
    pub fn is_inherently_symbolic(&self) -> bool {
        matches!(
            self,
            AstOp::Union(..) | AstOp::Intersection(..) | AstOp::Widen(..)
        )
    }

    pub fn variables(&self) -> BTreeSet<InternedString> {
        match self {
            AstOp::BoolS(s) | AstOp::BVS(s, _) | AstOp::FPS(s, _) | AstOp::StringS(s) => {
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

    /// Computes the type (sort) of the result of this operation. The type of an
    /// operation is determined by the operation and the types of its children;
    /// because children cache their type this is O(1) (O(n) for `Concat`).
    pub fn infer_type(&self) -> AstType {
        match self {
            // Booleans
            AstOp::BoolS(..)
            | AstOp::BoolV(..)
            | AstOp::BoolXor(..)
            | AstOp::BoolEq(..)
            | AstOp::BoolNeq(..)
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
            | AstOp::FpEq(..)
            | AstOp::FpNeq(..)
            | AstOp::FpLt(..)
            | AstOp::FpLeq(..)
            | AstOp::FpGt(..)
            | AstOp::FpGeq(..)
            | AstOp::FpIsNan(..)
            | AstOp::FpIsInf(..)
            | AstOp::StrContains(..)
            | AstOp::StrPrefixOf(..)
            | AstOp::StrSuffixOf(..)
            | AstOp::StrIsDigit(..)
            | AstOp::StrEq(..)
            | AstOp::StrNeq(..) => AstType::Bool,

            // Polymorphic: result type follows a child's type
            AstOp::Not(a) => a.ty(),
            AstOp::And(v) | AstOp::Or(v) => {
                v.first().map(|a| a.ty()).unwrap_or(AstType::Bool)
            }
            AstOp::ITE(_, t, _) => t.ty(),

            // Bitvectors
            AstOp::BVS(_, width) => AstType::BitVec(*width),
            AstOp::BVV(bv) => AstType::BitVec(bv.len()),
            AstOp::Xor(v) | AstOp::Add(v) | AstOp::Mul(v) => {
                AstType::BitVec(v.first().map(|a| a.size()).unwrap_or(0))
            }
            AstOp::Neg(a)
            | AstOp::Sub(a, _)
            | AstOp::UDiv(a, _)
            | AstOp::SDiv(a, _)
            | AstOp::URem(a, _)
            | AstOp::SRem(a, _)
            | AstOp::ShL(a, _)
            | AstOp::LShR(a, _)
            | AstOp::AShR(a, _)
            | AstOp::RotateLeft(a, _)
            | AstOp::RotateRight(a, _)
            | AstOp::ByteReverse(a)
            | AstOp::Union(a, _)
            | AstOp::Intersection(a, _)
            | AstOp::Widen(a, _) => AstType::BitVec(a.size()),
            AstOp::ZeroExt(a, ext) | AstOp::SignExt(a, ext) => AstType::BitVec(a.size() + ext),
            AstOp::Extract(_, high, low) => AstType::BitVec(high - low + 1),
            AstOp::Concat(v) => AstType::BitVec(v.iter().map(|a| a.size()).sum()),
            AstOp::FpToIEEEBV(a) => AstType::BitVec(a.size()),
            AstOp::FpToUBV(_, size, _) | AstOp::FpToSBV(_, size, _) => AstType::BitVec(*size),
            AstOp::StrLen(_) | AstOp::StrToBV(_) | AstOp::StrIndexOf(..) => AstType::BitVec(64),

            // Floats
            AstOp::FPS(_, sort) => AstType::Float(*sort),
            AstOp::FPV(value) => AstType::Float(value.fsort()),
            AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpSqrt(a, _)
            | AstOp::FpAdd(a, _, _)
            | AstOp::FpSub(a, _, _)
            | AstOp::FpMul(a, _, _)
            | AstOp::FpDiv(a, _, _) => a.ty(),
            AstOp::FpToFp(_, sort, _)
            | AstOp::BvToFp(_, sort)
            | AstOp::BvToFpSigned(_, sort, _)
            | AstOp::BvToFpUnsigned(_, sort, _) => AstType::Float(*sort),
            AstOp::FpFP(_sign, exp, sig) => {
                // The significand includes the implicit bit, the mantissa doesn't
                AstType::Float(FSort::new(exp.size(), sig.size().saturating_sub(1)))
            }

            // Strings
            AstOp::StringS(..)
            | AstOp::StringV(..)
            | AstOp::StrConcat(..)
            | AstOp::StrSubstr(..)
            | AstOp::StrReplace(..)
            | AstOp::BVToStr(..) => AstType::String,
        }
    }
}

pub struct AstOpChildIter<'a, 'c> {
    op: &'a AstOp<'c>,
    index: usize,
}

impl<'c> Iterator for AstOpChildIter<'_, 'c> {
    type Item = AstRef<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.op.child_at(self.index);
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

impl ExactSizeIterator for AstOpChildIter<'_, '_> {
    fn len(&self) -> usize {
        self.op.num_children().saturating_sub(self.index)
    }
}

impl Hash for AstOp<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
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

            // N-ary
            AstOp::And(v)
            | AstOp::Or(v)
            | AstOp::Xor(v)
            | AstOp::Add(v)
            | AstOp::Mul(v)
            | AstOp::Concat(v) => v.hash(state),

            // Unary with no extra payload
            AstOp::Not(a)
            | AstOp::Neg(a)
            | AstOp::ByteReverse(a)
            | AstOp::StrLen(a)
            | AstOp::StrToBV(a)
            | AstOp::FpToIEEEBV(a)
            | AstOp::FpNeg(a)
            | AstOp::FpAbs(a)
            | AstOp::FpIsNan(a)
            | AstOp::FpIsInf(a)
            | AstOp::StrIsDigit(a)
            | AstOp::BVToStr(a) => a.hash(state),

            AstOp::ZeroExt(a, n) | AstOp::SignExt(a, n) => {
                a.hash(state);
                n.hash(state);
            }
            AstOp::Extract(a, high, low) => {
                a.hash(state);
                high.hash(state);
                low.hash(state);
            }
            AstOp::FpToUBV(a, size, rm) | AstOp::FpToSBV(a, size, rm) => {
                a.hash(state);
                size.hash(state);
                rm.hash(state);
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

            // Binary with no extra payload
            AstOp::BoolXor(a, b)
            | AstOp::BoolEq(a, b)
            | AstOp::BoolNeq(a, b)
            | AstOp::Eq(a, b)
            | AstOp::Neq(a, b)
            | AstOp::ULT(a, b)
            | AstOp::ULE(a, b)
            | AstOp::UGT(a, b)
            | AstOp::UGE(a, b)
            | AstOp::SLT(a, b)
            | AstOp::SLE(a, b)
            | AstOp::SGT(a, b)
            | AstOp::SGE(a, b)
            | AstOp::FpEq(a, b)
            | AstOp::FpNeq(a, b)
            | AstOp::FpLt(a, b)
            | AstOp::FpLeq(a, b)
            | AstOp::FpGt(a, b)
            | AstOp::FpGeq(a, b)
            | AstOp::StrContains(a, b)
            | AstOp::StrPrefixOf(a, b)
            | AstOp::StrSuffixOf(a, b)
            | AstOp::StrEq(a, b)
            | AstOp::StrNeq(a, b)
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
            | AstOp::Union(a, b)
            | AstOp::Intersection(a, b)
            | AstOp::Widen(a, b)
            | AstOp::StrConcat(a, b) => {
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

            // Ternary
            AstOp::ITE(a, b, c)
            | AstOp::StrIndexOf(a, b, c)
            | AstOp::FpFP(a, b, c)
            | AstOp::StrSubstr(a, b, c)
            | AstOp::StrReplace(a, b, c) => {
                a.hash(state);
                b.hash(state);
                c.hash(state);
            }
        }
    }
}
