use crate::{childvecext::ChildVecExt, prelude::*};

pub trait MakeLike<'c>: Sized {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError>;
}

impl<'c> MakeLike<'c> for DynAst<'c> {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError> {
        Ok(match self {
            DynAst::Boolean(ast) => DynAst::Boolean(ast.make_like(children)?),
            DynAst::BitVec(ast) => DynAst::BitVec(ast.make_like(children)?),
            DynAst::Float(ast) => DynAst::Float(ast.make_like(children)?),
            DynAst::String(ast) => DynAst::String(ast.make_like(children)?),
        })
    }
}

impl<'c> MakeLike<'c> for BoolAst<'c> {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError> {
        self.context().make_bool(match self.op() {
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => self.op().clone(),
            BooleanOp::Not(..) => BooleanOp::Not(children.child_bool(0)?),
            BooleanOp::And(..) => BooleanOp::And(children.child_bool(0)?, children.child_bool(1)?),
            BooleanOp::Or(..) => BooleanOp::Or(children.child_bool(0)?, children.child_bool(1)?),
            BooleanOp::Xor(..) => BooleanOp::Xor(children.child_bool(0)?, children.child_bool(1)?),
            BooleanOp::BoolEq(..) => {
                BooleanOp::BoolEq(children.child_bool(0)?, children.child_bool(1)?)
            }
            BooleanOp::BoolNeq(..) => {
                BooleanOp::BoolNeq(children.child_bool(0)?, children.child_bool(1)?)
            }
            BooleanOp::Eq(..) => {
                BooleanOp::Eq(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::Neq(..) => {
                BooleanOp::Neq(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::ULT(..) => {
                BooleanOp::ULT(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::ULE(..) => {
                BooleanOp::ULE(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::UGT(..) => {
                BooleanOp::UGT(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::UGE(..) => {
                BooleanOp::UGE(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::SLT(..) => {
                BooleanOp::SLT(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::SLE(..) => {
                BooleanOp::SLE(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::SGT(..) => {
                BooleanOp::SGT(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::SGE(..) => {
                BooleanOp::SGE(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BooleanOp::FpEq(..) => {
                BooleanOp::FpEq(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpNeq(..) => {
                BooleanOp::FpNeq(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpLt(..) => {
                BooleanOp::FpLt(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpLeq(..) => {
                BooleanOp::FpLeq(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpGt(..) => {
                BooleanOp::FpGt(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpGeq(..) => {
                BooleanOp::FpGeq(children.child_float(0)?, children.child_float(1)?)
            }
            BooleanOp::FpIsNan(..) => BooleanOp::FpIsNan(children.child_float(0)?),
            BooleanOp::FpIsInf(..) => BooleanOp::FpIsInf(children.child_float(0)?),
            BooleanOp::StrContains(..) => {
                BooleanOp::StrContains(children.child_string(0)?, children.child_string(1)?)
            }
            BooleanOp::StrPrefixOf(..) => {
                BooleanOp::StrPrefixOf(children.child_string(0)?, children.child_string(1)?)
            }
            BooleanOp::StrSuffixOf(..) => {
                BooleanOp::StrSuffixOf(children.child_string(0)?, children.child_string(1)?)
            }
            BooleanOp::StrIsDigit(..) => BooleanOp::StrIsDigit(children.child_string(0)?),
            BooleanOp::StrEq(..) => {
                BooleanOp::StrEq(children.child_string(0)?, children.child_string(1)?)
            }
            BooleanOp::StrNeq(..) => {
                BooleanOp::StrNeq(children.child_string(0)?, children.child_string(1)?)
            }
            BooleanOp::If(..) => BooleanOp::If(
                children.child_bool(0)?,
                children.child_bool(1)?,
                children.child_bool(2)?,
            ),
        })
    }
}

impl<'c> MakeLike<'c> for BitVecAst<'c> {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError> {
        self.context().make_bitvec(match self.op() {
            BitVecOp::BVS(_, _) | BitVecOp::BVV(_) | BitVecOp::SI(_, _, _, _) => self.op().clone(),
            BitVecOp::Not(..) => BitVecOp::Not(children.child_bitvec(0)?),
            BitVecOp::And(..) => {
                BitVecOp::And(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Or(..) => BitVecOp::Or(children.child_bitvec(0)?, children.child_bitvec(1)?),
            BitVecOp::Xor(..) => {
                BitVecOp::Xor(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Neg(..) => BitVecOp::Neg(children.child_bitvec(0)?),
            BitVecOp::Add(..) => {
                BitVecOp::Add(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Sub(..) => {
                BitVecOp::Sub(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Mul(..) => {
                BitVecOp::Mul(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::UDiv(..) => {
                BitVecOp::UDiv(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::SDiv(..) => {
                BitVecOp::SDiv(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::URem(..) => {
                BitVecOp::URem(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::SRem(..) => {
                BitVecOp::SRem(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::ShL(..) => {
                BitVecOp::ShL(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::LShR(..) => {
                BitVecOp::LShR(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::AShR(..) => {
                BitVecOp::AShR(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::RotateLeft(..) => {
                BitVecOp::RotateLeft(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::RotateRight(..) => {
                BitVecOp::RotateRight(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::ZeroExt(_, amount) => BitVecOp::ZeroExt(children.child_bitvec(0)?, *amount),
            BitVecOp::SignExt(_, amount) => BitVecOp::SignExt(children.child_bitvec(0)?, *amount),
            BitVecOp::Extract(_, high, low) => {
                BitVecOp::Extract(children.child_bitvec(0)?, *high, *low)
            }
            BitVecOp::Concat(..) => {
                BitVecOp::Concat(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Reverse(..) => BitVecOp::Reverse(children.child_bitvec(0)?),
            BitVecOp::FpToIEEEBV(..) => BitVecOp::FpToIEEEBV(children.child_float(0)?),
            BitVecOp::FpToUBV(_, bv_len, rm) => {
                BitVecOp::FpToUBV(children.child_float(0)?, *bv_len, *rm)
            }
            BitVecOp::FpToSBV(_, bv_len, rm) => {
                BitVecOp::FpToSBV(children.child_float(0)?, *bv_len, *rm)
            }
            BitVecOp::StrLen(..) => BitVecOp::StrLen(children.child_string(0)?),
            BitVecOp::StrIndexOf(..) => BitVecOp::StrIndexOf(
                children.child_string(0)?,
                children.child_string(1)?,
                children.child_bitvec(2)?,
            ),
            BitVecOp::StrToBV(..) => BitVecOp::StrToBV(children.child_string(0)?),
            BitVecOp::If(..) => BitVecOp::If(
                children.child_bool(0)?,
                children.child_bitvec(1)?,
                children.child_bitvec(2)?,
            ),
            BitVecOp::Union(..) => {
                BitVecOp::Union(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
            BitVecOp::Intersection(..) => {
                BitVecOp::Intersection(children.child_bitvec(0)?, children.child_bitvec(1)?)
            }
        })
    }
}

impl<'c> MakeLike<'c> for FloatAst<'c> {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError> {
        self.context().make_float(match self.op() {
            FloatOp::FPS(..) | FloatOp::FPV(..) => self.op().clone(),
            FloatOp::FpNeg(..) => FloatOp::FpNeg(children.child_float(0)?),
            FloatOp::FpAbs(..) => FloatOp::FpAbs(children.child_float(0)?),
            FloatOp::FpAdd(.., fprm) => {
                FloatOp::FpAdd(children.child_float(0)?, children.child_float(1)?, *fprm)
            }
            FloatOp::FpSub(.., fprm) => {
                FloatOp::FpSub(children.child_float(0)?, children.child_float(1)?, *fprm)
            }
            FloatOp::FpMul(.., fprm) => {
                FloatOp::FpMul(children.child_float(0)?, children.child_float(1)?, *fprm)
            }
            FloatOp::FpDiv(.., fprm) => {
                FloatOp::FpDiv(children.child_float(0)?, children.child_float(1)?, *fprm)
            }
            FloatOp::FpSqrt(.., fprm) => FloatOp::FpSqrt(children.child_float(0)?, *fprm),
            FloatOp::FpToFp(.., fsort, fprm) => {
                FloatOp::FpToFp(children.child_float(0)?, *fsort, *fprm)
            }
            FloatOp::BvToFp(.., fsort) => FloatOp::BvToFp(children.child_bitvec(0)?, *fsort),
            FloatOp::BvToFpSigned(.., fsort, fprm) => {
                FloatOp::BvToFpSigned(children.child_bitvec(0)?, *fsort, *fprm)
            }
            FloatOp::BvToFpUnsigned(.., fsort, fprm) => {
                FloatOp::BvToFpUnsigned(children.child_bitvec(0)?, *fsort, *fprm)
            }
            FloatOp::If(..) => FloatOp::If(
                children.child_bool(0)?,
                children.child_float(1)?,
                children.child_float(2)?,
            ),
        })
    }
}

impl<'c> MakeLike<'c> for StringAst<'c> {
    fn make_like(&self, children: &[DynAst<'c>]) -> Result<Self, ClarirsError> {
        self.context().make_string(match self.op() {
            StringOp::StringS(_) | StringOp::StringV(_) => self.op().clone(),
            StringOp::StrConcat(..) => {
                StringOp::StrConcat(children.child_string(0)?, children.child_string(1)?)
            }
            StringOp::StrSubstr(..) => StringOp::StrSubstr(
                children.child_string(0)?,
                children.child_bitvec(1)?,
                children.child_bitvec(2)?,
            ),
            StringOp::StrReplace(..) => StringOp::StrReplace(
                children.child_string(0)?,
                children.child_string(1)?,
                children.child_string(2)?,
            ),
            StringOp::BVToStr(..) => StringOp::BVToStr(children.child_bitvec(0)?),
            StringOp::If(..) => StringOp::If(
                children.child_bool(0)?,
                children.child_string(1)?,
                children.child_string(2)?,
            ),
        })
    }
}
