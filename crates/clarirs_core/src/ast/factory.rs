use num_bigint::BigUint;

use super::factory_support::*;
use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c>: Sized {
    // Required methods
    fn make_bool(&'c self, op: BooleanOp<'c>) -> Result<BoolAst<'c>, ClarirsError>;
    fn make_bitvec(&'c self, op: BitVecOp<'c>) -> Result<BitVecAst<'c>, ClarirsError>;
    fn make_float(&'c self, op: FloatOp<'c>) -> Result<FloatAst<'c>, ClarirsError>;
    fn make_string(&'c self, op: StringOp<'c>) -> Result<StringAst<'c>, ClarirsError>;

    // Provided methods

    fn bools<S: Into<String>>(&'c self, name: S) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::BoolS(name.into()))
    }

    fn boolv(&'c self, value: bool) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::BoolV(value))
    }

    fn bvs<S: Into<String>>(&'c self, name: S, width: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::BVS(name.into(), width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::BVV(value))
    }

    fn fps<S: Into<String>, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FPS(name.into(), sort.into()))
    }

    fn fpv<F: Into<Float>>(&'c self, value: F) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FPV(value.into()))
    }

    fn strings<S: Into<String>>(&'c self, name: S) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StringS(name.into()))
    }

    fn stringv<S: Into<String>>(&'c self, value: S) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StringV(value.into()))
    }

    fn not<Op: SupportsNot<'c>>(
        &'c self,
        ast: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::not(self, ast)
    }

    fn and<Op: SupportsAnd<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::and(self, lhs, rhs)
    }

    fn or<Op: SupportsOr<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::or(self, lhs, rhs)
    }

    fn xor<Op: SupportsXor<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::xor(self, lhs, rhs)
    }

    fn eq_<Op: SupportsEq<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        Op::eq_(self, lhs, rhs)
    }

    fn neq<Op: SupportsNeq<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        Op::neq(self, lhs, rhs)
    }

    fn neg(&'c self, ast: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Neg(ast.clone()))
    }

    fn abs<Op: SupportsAbs<'c>>(
        &'c self,
        ast: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::abs(self, ast)
    }

    fn add<Op: SupportsAdd<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::add(self, lhs, rhs)
    }

    fn sub<Op: SupportsSub<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::sub(self, lhs, rhs)
    }

    fn mul<Op: SupportsMul<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::mul(self, lhs, rhs)
    }

    fn udiv<Op: SupportsUDiv<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::udiv(self, lhs, rhs)
    }

    fn sdiv<Op: SupportsSDiv<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::sdiv(self, lhs, rhs)
    }

    fn urem<Op: SupportsURem<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::urem(self, lhs, rhs)
    }

    fn srem<Op: SupportsSRem<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::srem(self, lhs, rhs)
    }

    fn pow<Op: SupportsPow<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        rhs: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::pow(self, lhs, rhs)
    }

    fn shl(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::ShL(lhs.clone(), rhs.clone()))
    }

    fn ashr(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::AShR(lhs.clone(), rhs.clone()))
    }

    fn lshr(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::LShR(lhs.clone(), rhs.clone()))
    }

    fn rotate_left(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::RotateLeft(lhs.clone(), rhs.clone()))
    }

    fn rotate_right(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::RotateRight(lhs.clone(), rhs.clone()))
    }

    fn zero_ext(&'c self, lhs: &BitVecAst<'c>, width: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::ZeroExt(lhs.clone(), width))
    }

    fn sign_ext(&'c self, lhs: &BitVecAst<'c>, width: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::SignExt(lhs.clone(), width))
    }

    fn extract(
        &'c self,
        lhs: &BitVecAst<'c>,
        high: u32,
        low: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Extract(lhs.clone(), high, low))
    }

    fn concat(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Concat(lhs.clone(), rhs.clone()))
    }

    fn reverse(&'c self, lhs: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Reverse(lhs.clone()))
    }

    fn ult(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::ULT(lhs.clone(), rhs.clone()))
    }

    fn ule(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::ULE(lhs.clone(), rhs.clone()))
    }

    fn ugt(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::UGT(lhs.clone(), rhs.clone()))
    }

    fn uge(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::UGE(lhs.clone(), rhs.clone()))
    }

    fn slt(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SLT(lhs.clone(), rhs.clone()))
    }

    fn sle(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SLE(lhs.clone(), rhs.clone()))
    }

    fn sgt(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SGT(lhs.clone(), rhs.clone()))
    }

    fn sge(
        &'c self,
        lhs: &BitVecAst<'c>,
        rhs: &BitVecAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SGE(lhs.clone(), rhs.clone()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &FloatAst<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpToFp(lhs.clone(), sort.into(), rm.into()))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &BitVecAst<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::BvToFpUnsigned(lhs.clone(), sort.into(), rm.into()))
    }

    fn fp_to_ieeebv(&'c self, lhs: &FloatAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToIEEEBV(lhs.clone()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToUBV(lhs.clone(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToSBV(lhs.clone(), width, rm.into()))
    }

    fn fp_neg(&'c self, lhs: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpNeg(lhs.clone()))
    }

    fn fp_abs(&'c self, lhs: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpAbs(lhs.clone()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpAdd(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpSub(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpMul(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpDiv(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: &FloatAst<'c>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpSqrt(lhs.clone(), rm.into()))
    }

    fn fp_eq(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpEq(lhs.clone(), rhs.clone()))
    }

    fn fp_neq(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpNeq(lhs.clone(), rhs.clone()))
    }

    fn fp_lt(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpLt(lhs.clone(), rhs.clone()))
    }

    fn fp_leq(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpLeq(lhs.clone(), rhs.clone()))
    }

    fn fp_gt(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpGt(lhs.clone(), rhs.clone()))
    }

    fn fp_geq(
        &'c self,
        lhs: &FloatAst<'c>,
        rhs: &FloatAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpGeq(lhs.clone(), rhs.clone()))
    }

    fn fp_is_nan(&'c self, lhs: &FloatAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpIsNan(lhs.clone()))
    }

    fn fp_is_inf(&'c self, lhs: &FloatAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpIsInf(lhs.clone()))
    }

    fn strlen(&'c self, lhs: &StringAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrLen(lhs.clone()))
    }

    fn strconcat(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrConcat(lhs.clone(), rhs.clone()))
    }

    fn strsubstr(
        &'c self,
        lhs: &StringAst<'c>,
        start: &BitVecAst<'c>,
        size: &BitVecAst<'c>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrSubstr(
            lhs.clone(),
            start.clone(),
            size.clone(),
        ))
    }

    fn strcontains(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrContains(lhs.clone(), rhs.clone()))
    }

    fn strindexof(
        &'c self,
        base: &StringAst<'c>,
        substr: &StringAst<'c>,
        offset: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrIndexOf(
            base.clone(),
            substr.clone(),
            offset.clone(),
        ))
    }

    fn strreplace(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
        start: &StringAst<'c>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrReplace(
            lhs.clone(),
            rhs.clone(),
            start.clone(),
        ))
    }

    fn strprefixof(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrPrefixOf(lhs.clone(), rhs.clone()))
    }

    fn strsuffixof(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrSuffixOf(lhs.clone(), rhs.clone()))
    }

    fn strtobv(&'c self, lhs: &StringAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrToBV(lhs.clone()))
    }

    fn bvtostr(&'c self, lhs: &BitVecAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::BVToStr(lhs.clone()))
    }

    fn strisdigit(&'c self, lhs: &StringAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrIsDigit(lhs.clone()))
    }

    fn streq(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrEq(lhs.clone(), rhs.clone()))
    }

    fn strneq(
        &'c self,
        lhs: &StringAst<'c>,
        rhs: &StringAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrNeq(lhs.clone(), rhs.clone()))
    }

    fn if_<Op: SupportsIf<'c>>(
        &'c self,
        cond: &AstRef<'c, BooleanOp<'c>>,
        then: &AstRef<'c, Op>,
        else_: &AstRef<'c, Op>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::if_(self, cond, then, else_)
    }

    fn annotated<Op: SupportsAnnotated<'c>>(
        &'c self,
        lhs: &AstRef<'c, Op>,
        annotation: Annotation,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::annotated(self, lhs, annotation)
    }

    // Helper methods
    fn true_(&'c self) -> Result<BoolAst<'c>, ClarirsError> {
        self.boolv(true)
    }

    fn false_(&'c self) -> Result<BoolAst<'c>, ClarirsError> {
        self.boolv(false)
    }

    fn bvv_prim<T: Into<u64>>(&'c self, value: T) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim(value)?)
    }

    fn bvv_prim_with_size<T: Into<u64>>(
        &'c self,
        value: T,
        length: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim_with_size(value, length)?)
    }

    fn bvv_from_biguint_with_size(
        &'c self,
        value: &BigUint,
        length: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_biguint(value, length)?)
    }

    fn fpv_from_f64(&'c self, value: f64) -> Result<FloatAst<'c>, ClarirsError> {
        self.fpv(Float::from(value))
    }
}
