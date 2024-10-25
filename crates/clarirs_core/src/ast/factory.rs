use num_bigint::BigUint;

use crate::ast::node::AstRef;
use crate::ast::op::{BitVecOp, BooleanOp, FloatOp, StringOp};
use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c> {
    // Required methods
    fn make_boolean_ast(
        &'c self,
        op: BooleanOp<'c>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError>;
    fn make_bitvec_ast(
        &'c self,
        op: BitVecOp<'c>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError>;
    fn make_float_ast(&'c self, op: FloatOp<'c>) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError>;
    fn make_string_ast(
        &'c self,
        op: StringOp<'c>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError>;

    // Provided methods - BooleanOp

    fn bools<S>(&'c self, name: S) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_boolean_ast(BooleanOp::BoolS(name.into()))
    }

    fn boolv(&'c self, value: bool) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::BoolV(value))
    }

    fn bool_not(
        &'c self,
        ast: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Not(ast.clone()))
    }

    fn bool_and(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::And(lhs.clone(), rhs.clone()))
    }

    fn bool_or(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Or(lhs.clone(), rhs.clone()))
    }

    fn bool_xor(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Xor(lhs.clone(), rhs.clone()))
    }

    fn eq_(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Eq(lhs.clone(), rhs.clone()))
    }

    fn neq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Neq(lhs.clone(), rhs.clone()))
    }

    fn ult(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::ULT(lhs.clone(), rhs.clone()))
    }

    fn ule(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::ULE(lhs.clone(), rhs.clone()))
    }

    fn ugt(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::UGT(lhs.clone(), rhs.clone()))
    }

    fn uge(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::UGE(lhs.clone(), rhs.clone()))
    }

    fn slt(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::SLT(lhs.clone(), rhs.clone()))
    }

    fn sle(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::SLE(lhs.clone(), rhs.clone()))
    }

    fn sgt(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::SGT(lhs.clone(), rhs.clone()))
    }

    fn sge(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::SGE(lhs.clone(), rhs.clone()))
    }

    fn fp_eq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpEq(lhs.clone(), rhs.clone()))
    }

    fn fp_neq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpNeq(lhs.clone(), rhs.clone()))
    }

    fn fp_lt(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpLt(lhs.clone(), rhs.clone()))
    }

    fn fp_leq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpLeq(lhs.clone(), rhs.clone()))
    }

    fn fp_gt(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpGt(lhs.clone(), rhs.clone()))
    }

    fn fp_geq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpGeq(lhs.clone(), rhs.clone()))
    }

    fn fp_is_nan(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpIsNan(lhs.clone()))
    }

    fn fp_is_inf(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::FpIsInf(lhs.clone()))
    }

    fn strcontains(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrContains(lhs.clone(), rhs.clone()))
    }

    fn strprefixof(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrPrefixOf(lhs.clone(), rhs.clone()))
    }

    fn strsuffixof(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrSuffixOf(lhs.clone(), rhs.clone()))
    }

    fn strisdigit(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrIsDigit(lhs.clone()))
    }

    fn streq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrEq(lhs.clone(), rhs.clone()))
    }

    fn strneq(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        rhs: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(AstOp::StrNeq(lhs.clone(), rhs.clone()))
    }

    // Provided methods - FloatOp

    fn fps<S, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_float_ast(FloatOp::FPS(name.into(), sort.into()))
    }

    fn fpv<F>(&'c self, value: F) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError>
    where
        F: Into<Float>,
    {
        self.make_float_ast(FloatOp::FPV(value.into()))
    }

    fn fp_neg<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpNeg(lhs.clone(), rm.into()))
    }

    fn fp_abs<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpAbs(lhs.clone(), rm.into()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpAdd(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpSub(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpMul(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpDiv(lhs.clone(), rhs.clone(), rm.into()))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::FpSqrt(lhs.clone(), rm.into()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(AstOp::FpToFp(lhs.clone(), sort.into(), rm.into()))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(AstOp::BvToFpUnsigned(lhs.clone(), sort.into(), rm.into()))
    }

    // Provided methods - BitVecOp

    fn bvs<S>(&'c self, name: S, width: u32) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_bitvec_ast(AstOp::BVS(name.into(), width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(AstOp::BVV(value))
    }

    fn si<S, LB, UB, STRIDE>(
        &'c self,
        name: S,
        lower_bound: LB,
        upper_bound: UB,
        stride: STRIDE,
        width: u32,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError>
    where
        S: Into<String>,
        LB: Into<BitVec>,
        UB: Into<BitVec>,
        STRIDE: Into<BitVec>,
    {
        self.make_bitvec_ast(BitVecOp::SI(
            name.into(),
            lower_bound.into(),
            upper_bound.into(),
            stride.into(),
            width,
        ))
    }

    fn bitvec_not(
        &'c self,
        ast: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Not(ast.clone()))
    }

    fn bitvec_and(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::And(lhs.clone(), rhs.clone()))
    }

    fn bitvec_or(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Or(lhs.clone(), rhs.clone()))
    }

    fn bitvec_xor(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Xor(lhs.clone(), rhs.clone()))
    }

    fn add(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Add(lhs.clone(), rhs.clone()))
    }

    fn sub(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Sub(lhs.clone(), rhs.clone()))
    }

    fn mul(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Mul(lhs.clone(), rhs.clone()))
    }

    fn udiv(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::UDiv(lhs.clone(), rhs.clone()))
    }

    fn sdiv(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::SDiv(lhs.clone(), rhs.clone()))
    }

    fn urem(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::URem(lhs.clone(), rhs.clone()))
    }

    fn srem(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::SRem(lhs.clone(), rhs.clone()))
    }

    fn pow(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Pow(lhs.clone(), rhs.clone()))
    }

    fn lshl(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::LShL(lhs.clone(), rhs.clone()))
    }

    fn lshr(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::LShR(lhs.clone(), rhs.clone()))
    }

    fn ashl(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::AShL(lhs.clone(), rhs.clone()))
    }

    fn ashr(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::AShR(lhs.clone(), rhs.clone()))
    }

    fn rotate_left(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::RotateLeft(lhs.clone(), rhs.clone()))
    }

    fn rotate_right(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::RotateRight(lhs.clone(), rhs.clone()))
    }

    fn zero_ext(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        width: u32,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::ZeroExt(lhs.clone(), width))
    }

    fn sign_ext(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        width: u32,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::SignExt(lhs.clone(), width))
    }

    fn extract(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        lower: u32,
        upper: u32,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Extract(lhs.clone(), lower, upper))
    }

    fn concat(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        rhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Concat(lhs.clone(), rhs.clone()))
    }

    fn reverse(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Reverse(lhs.clone()))
    }

    fn fp_to_ieeebv(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::FpToIEEEBV(lhs.clone()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::FpToUBV(lhs.clone(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::FpToSBV(lhs.clone(), width, rm.into()))
    }

    fn strlen(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::StrLen(lhs.clone()))
    }

    fn strindexof(
        &'c self,
        base: &AstRef<'c, BitVecOp<'c>>,
        substr: &AstRef<'c, BitVecOp<'c>>,
        offset: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::StrIndexOf(
            base.clone(),
            substr.clone(),
            offset.clone(),
        ))
    }

    fn strtobv(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::StrToBV(lhs.clone()))
    }

    // Provided methods - StringOp

    fn strings<S>(&'c self, name: S, width: u32) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_string_ast(StringOp::StringS(name.into(), width))
    }

    fn stringv<S>(&'c self, value: S) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError>
    where
        S: Into<String>,
    {
        self.make_string_ast(StringOp::StringV(value.into()))
    }

    fn strconcat(
        &'c self,
        lhs: &AstRef<'c, StringOp<'c>>,
        rhs: &AstRef<'c, StringOp<'c>>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::StrConcat(lhs.clone(), rhs.clone()))
    }

    fn strsubstr(
        &'c self,
        lhs: &AstRef<'c, StringOp<'c>>,
        start: &AstRef<'c, StringOp<'c>>,
        end: &AstRef<'c, StringOp<'c>>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::StrSubstr(lhs.clone(), start.clone(), end.clone()))
    }

    fn strreplace(
        &'c self,
        lhs: &AstRef<'c, StringOp<'c>>,
        rhs: &AstRef<'c, StringOp<'c>>,
        start: &AstRef<'c, StringOp<'c>>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::StrReplace(
            lhs.clone(),
            rhs.clone(),
            start.clone(),
        ))
    }

    fn bvtostr(
        &'c self,
        lhs: &AstRef<'c, StringOp<'c>>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::BVToStr(lhs.clone()))
    }

    // If methods
    fn bool_if(
        &'c self,
        cond: &AstRef<'c, BooleanOp<'c>>,
        then: &AstRef<'c, BooleanOp<'c>>,
        else_: &AstRef<'c, BooleanOp<'c>>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::If(cond.clone(), then.clone(), else_.clone()))
    }

    fn float_if(
        &'c self,
        cond: &AstRef<'c, BooleanOp<'c>>, // The condition is boolean
        then: &AstRef<'c, FloatOp<'c>>,
        else_: &AstRef<'c, FloatOp<'c>>,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::If(cond.clone(), then.clone(), else_.clone()))
    }

    fn bitvec_if(
        &'c self,
        cond: &AstRef<'c, BooleanOp<'c>>, // The condition is boolean
        then: &AstRef<'c, BitVecOp<'c>>,
        else_: &AstRef<'c, BitVecOp<'c>>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::If(cond.clone(), then.clone(), else_.clone()))
    }

    fn string_if(
        &'c self,
        cond: &AstRef<'c, BooleanOp<'c>>, // The condition is boolean
        then: &AstRef<'c, StringOp<'c>>,
        else_: &AstRef<'c, StringOp<'c>>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::If(cond.clone(), then.clone(), else_.clone()))
    }

    // Annotation methods
    fn bool_annotated(
        &'c self,
        lhs: &AstRef<'c, BooleanOp<'c>>,
        annotation: Annotation<'c>,
    ) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.make_boolean_ast(BooleanOp::Annotated(lhs.clone(), annotation))
    }

    fn float_annotated(
        &'c self,
        lhs: &AstRef<'c, FloatOp<'c>>,
        annotation: Annotation<'c>,
    ) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.make_float_ast(FloatOp::Annotated(lhs.clone(), annotation))
    }

    fn bitvec_annotated(
        &'c self,
        lhs: &AstRef<'c, BitVecOp<'c>>,
        annotation: Annotation<'c>,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.make_bitvec_ast(BitVecOp::Annotated(lhs.clone(), annotation))
    }

    fn string_annotated(
        &'c self,
        lhs: &AstRef<'c, StringOp<'c>>,
        annotation: Annotation<'c>,
    ) -> Result<AstRef<'c, StringOp<'c>>, ClarirsError> {
        self.make_string_ast(StringOp::Annotated(lhs.clone(), annotation))
    }

    // Helper methods
    fn true_(&'c self) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.boolv(true)
    }

    fn false_(&'c self) -> Result<AstRef<'c, BooleanOp<'c>>, ClarirsError> {
        self.boolv(false)
    }

    fn bvv_prim<T>(&'c self, value: T) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError>
    where
        T: Into<u64>,
    {
        self.bvv(BitVec::from_prim(value))
    }

    fn bvv_prim_with_size<T>(&'c self, value: T, length: usize) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError>
    where
        T: Into<u64>,
    {
        self.bvv(BitVec::from_prim_with_size(value, length))
    }

    fn bvv_from_biguint_with_size(
        &'c self,
        value: &BigUint,
        length: u32,
    ) -> Result<AstRef<'c, BitVecOp<'c>>, ClarirsError> {
        self.bvv(BitVec::from_biguint(value, length as usize)?)
    }

    fn fpv_from_f64(&'c self, value: f64) -> Result<AstRef<'c, FloatOp<'c>>, ClarirsError> {
        self.fpv(Float::from(value))
    }
}
