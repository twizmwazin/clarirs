use num_bigint::BigUint;

use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c> {
    // Required methods
    fn make_ast(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError>;

    // Provided methods

    fn bools<S>(&'c self, name: S) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_ast(AstOp::BoolS(name.into()))
    }

    fn boolv(&'c self, value: bool) -> Result<AstRef<'c>, ClarirsError>
where {
        self.make_ast(AstOp::BoolV(value))
    }

    fn bvs<S>(&'c self, name: S, width: u32) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_ast(AstOp::BVS(name.into(), width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BVV(value))
    }

    fn si<S, I>(
        &'c self,
        name: S,
        lower_bound: I,
        upper_bound: I,
        stride: I,
        width: u32,
    ) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
        I: Into<BitVec>,
    {
        self.make_ast(AstOp::SI(
            name.into(),
            lower_bound.into(),
            upper_bound.into(),
            stride.into(),
            width,
        ))
    }

    fn fps<S, FS: Into<FSort>>(&'c self, name: S, sort: FS) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_ast(AstOp::FPS(name.into(), sort.into()))
    }

    fn fpv<F>(&'c self, value: F) -> Result<AstRef<'c>, ClarirsError>
    where
        F: Into<Float>,
    {
        self.make_ast(AstOp::FPV(value.into()))
    }

    fn strings<S>(&'c self, name: S, width: u32) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_ast(AstOp::StringS(name.into(), width))
    }

    fn stringv<S>(&'c self, value: S) -> Result<AstRef<'c>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_ast(AstOp::StringV(value.into()))
    }

    fn not(&'c self, ast: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Not(ast.clone()))
    }

    fn and(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::And(lhs.clone(), rhs.clone()))
    }

    fn or(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Or(lhs.clone(), rhs.clone()))
    }

    fn xor(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Xor(lhs.clone(), rhs.clone()))
    }

    fn add(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Add(lhs.clone(), rhs.clone()))
    }

    fn sub(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Sub(lhs.clone(), rhs.clone()))
    }

    fn mul(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Mul(lhs.clone(), rhs.clone()))
    }

    fn udiv(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UDiv(lhs.clone(), rhs.clone()))
    }

    fn sdiv(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SDiv(lhs.clone(), rhs.clone()))
    }

    fn urem(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::URem(lhs.clone(), rhs.clone()))
    }

    fn srem(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SRem(lhs.clone(), rhs.clone()))
    }

    fn pow(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Pow(lhs.clone(), rhs.clone()))
    }

    fn lshl(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::LShL(lhs.clone(), rhs.clone()))
    }

    fn lshr(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::LShR(lhs.clone(), rhs.clone()))
    }

    fn ashl(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::AShL(lhs.clone(), rhs.clone()))
    }

    fn ashr(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::AShR(lhs.clone(), rhs.clone()))
    }

    fn rotate_left(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::RotateLeft(lhs.clone(), rhs.clone()))
    }

    fn rotate_right(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::RotateRight(lhs.clone(), rhs.clone()))
    }

    fn zero_ext(&'c self, lhs: &AstRef<'c>, width: u32) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ZeroExt(lhs.clone(), width))
    }

    fn sign_ext(&'c self, lhs: &AstRef<'c>, width: u32) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SignExt(lhs.clone(), width))
    }

    fn extract(
        &'c self,
        lhs: &AstRef<'c>,
        lower: u32,
        upper: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Extract(lhs.clone(), lower, upper))
    }

    fn concat(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Concat(lhs.clone(), rhs.clone()))
    }

    fn reverse(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Reverse(lhs.clone()))
    }

    fn eq_(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Eq(lhs.clone(), rhs.clone()))
    }

    fn neq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Neq(lhs.clone(), rhs.clone()))
    }

    fn ult(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ULT(lhs.clone(), rhs.clone()))
    }

    fn ule(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ULE(lhs.clone(), rhs.clone()))
    }

    fn ugt(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UGT(lhs.clone(), rhs.clone()))
    }

    fn uge(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UGE(lhs.clone(), rhs.clone()))
    }

    fn slt(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SLT(lhs.clone(), rhs.clone()))
    }

    fn sle(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SLE(lhs.clone(), rhs.clone()))
    }

    fn sgt(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SGT(lhs.clone(), rhs.clone()))
    }

    fn sge(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SGE(lhs.clone(), rhs.clone()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &AstRef<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToFp(lhs.clone(), sort.into(), rm.into()))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &AstRef<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BvToFpUnsigned(lhs.clone(), sort.into(), rm.into()))
    }

    fn fp_to_ieeebv(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToIEEEBV(lhs.clone()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToUBV(lhs.clone(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToSBV(lhs.clone(), width, rm.into()))
    }

    fn fp_neg<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpNeg(lhs.clone(), rm.into()))
    }

    fn fp_abs<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpAbs(lhs.clone(), rm.into()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpAdd(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpSub(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpMul(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpDiv(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpSqrt(lhs.clone(), rm.into()))
    }

    fn fp_eq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpEq(lhs.clone(), rhs.clone()))
    }

    fn fp_neq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpNeq(lhs.clone(), rhs.clone()))
    }

    fn fp_lt(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpLt(lhs.clone(), rhs.clone()))
    }

    fn fp_leq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpLeq(lhs.clone(), rhs.clone()))
    }

    fn fp_gt(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpGt(lhs.clone(), rhs.clone()))
    }

    fn fp_geq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpGeq(lhs.clone(), rhs.clone()))
    }

    fn fp_is_nan(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpIsNan(lhs.clone()))
    }

    fn fp_is_inf(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpIsInf(lhs.clone()))
    }

    fn strlen(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrLen(lhs.clone()))
    }

    fn strconcat(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrConcat(lhs.clone(), rhs.clone()))
    }

    fn strsubstr(
        &'c self,
        lhs: &AstRef<'c>,
        start: &AstRef<'c>,
        end: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrSubstr(lhs.clone(), start.clone(), end.clone()))
    }

    fn strcontains(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrContains(lhs.clone(), rhs.clone()))
    }

    fn strindexof(
        &'c self,
        lhs: &AstRef<'c>,
        start: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrIndexOf(lhs.clone(), start.clone()))
    }

    fn strreplace(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
        start: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrReplace(lhs.clone(), rhs.clone(), start.clone()))
    }

    fn strprefixof(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrPrefixOf(lhs.clone(), rhs.clone()))
    }

    fn strsuffixof(
        &'c self,
        lhs: &AstRef<'c>,
        rhs: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrSuffixOf(lhs.clone(), rhs.clone()))
    }

    fn strtobv(&'c self, lhs: &AstRef<'c>, width: u32) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrToBV(lhs.clone(), width))
    }

    fn bvtostr(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BVToStr(lhs.clone()))
    }

    fn strisdigit(&'c self, lhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrIsDigit(lhs.clone()))
    }

    fn streq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrEq(lhs.clone(), rhs.clone()))
    }

    fn strneq(&'c self, lhs: &AstRef<'c>, rhs: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrNeq(lhs.clone(), rhs.clone()))
    }

    fn if_(
        &'c self,
        cond: &AstRef<'c>,
        then: &AstRef<'c>,
        else_: &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::If(cond.clone(), then.clone(), else_.clone()))
    }

    fn annotated(
        &'c self,
        lhs: &AstRef<'c>,
        annotation: Annotation<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Annotated(lhs.clone(), annotation))
    }

    // Helper methods
    fn true_(&'c self) -> Result<AstRef<'c>, ClarirsError> {
        self.boolv(true)
    }

    fn false_(&'c self) -> Result<AstRef<'c>, ClarirsError> {
        self.boolv(false)
    }

    fn bvv_prim<T>(&'c self, value: T) -> Result<AstRef<'c>, ClarirsError>
    where
        T: Into<u64>,
    {
        self.bvv(BitVec::from_prim(value))
    }

    fn bvv_prim_with_size<T>(&'c self, value: T, length: usize) -> Result<AstRef<'c>, ClarirsError>
    where
        T: Into<u64>,
    {
        self.bvv(BitVec::from_prim_with_size(value, length))
    }

    fn bvv_from_biguint_with_size(
        &'c self,
        value: &BigUint,
        length: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.bvv(BitVec::from_biguint(value, length as usize)?)
    }

    fn fpv_from_f64(&'c self, value: f64) -> Result<AstRef<'c>, ClarirsError> {
        self.fpv(Float::from(value))
    }
}
