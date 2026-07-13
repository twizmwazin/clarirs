use crate::prelude::*;
use anyhow::Result;

#[test]
fn test_bv_to_fp_of_fp_to_ieeebv_is_identity() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let round_trip = ctx.bv_to_fp(ctx.fp_to_ieeebv(&x)?, FSort::f64())?;

    assert_eq!(round_trip.simplify()?, x);
    Ok(())
}

#[test]
fn test_bv_to_fp_of_fp_to_ieeebv_different_sort_not_simplified() -> Result<()> {
    let ctx = Context::new();

    // Reinterpreting an f64's 64-bit pattern as some other 64-bit float sort
    // is NOT the identity; the round-trip must be preserved.
    let odd_sort = FSort::new(15, 49);
    let x = ctx.fps("x", FSort::f64())?;
    let reinterpret = ctx.bv_to_fp(ctx.fp_to_ieeebv(&x)?, odd_sort)?;

    let simplified = reinterpret.simplify()?;
    assert!(matches!(simplified.op(), AstOp::BvToFp(..)));
    Ok(())
}

// -- FPV / FPS --

#[test]
fn test_fp_prim() -> Result<()> {
    let ctx = Context::new();

    let concrete = ctx.fpv(1.5f64)?;
    let symbolic = ctx.fps("x", FSort::f64())?;

    assert_eq!(concrete.simplify()?, concrete);
    assert_eq!(symbolic.simplify()?, symbolic);

    Ok(())
}

// -- FpFP (component construction) --

#[test]
fn test_fp_fp_concrete_f64() -> Result<()> {
    let ctx = Context::new();

    // 1.0f64 = sign 0, exponent 0x3FF, mantissa 0
    let result = ctx
        .fp_fp(
            ctx.bvv(BitVec::from((0u64, 1)))?,
            ctx.bvv(BitVec::from((0x3FFu64, 11)))?,
            ctx.bvv(BitVec::from((0u64, 52)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(1.0f64)?);

    // Sign bit set -> -1.0
    let result = ctx
        .fp_fp(
            ctx.bvv(BitVec::from((1u64, 1)))?,
            ctx.bvv(BitVec::from((0x3FFu64, 11)))?,
            ctx.bvv(BitVec::from((0u64, 52)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(-1.0f64)?);

    Ok(())
}

#[test]
fn test_fp_fp_concrete_f32() -> Result<()> {
    let ctx = Context::new();

    // 1.5f32 = sign 0, exponent 0x7F, mantissa 0x400000
    let result = ctx
        .fp_fp(
            ctx.bvv(BitVec::from((0u64, 1)))?,
            ctx.bvv(BitVec::from((0x7Fu64, 8)))?,
            ctx.bvv(BitVec::from((0x400000u64, 23)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(1.5f32)?);

    Ok(())
}

#[test]
fn test_fp_fp_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_fp(
            ctx.bvs("sign", 1)?,
            ctx.bvv(BitVec::from((0x3FFu64, 11)))?,
            ctx.bvv(BitVec::from((0u64, 52)))?,
        )?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::FpFP(..)));

    Ok(())
}

// -- FpNeg / FpAbs --

#[test]
fn test_fp_neg_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx.fp_neg(ctx.fpv(1.5f64)?)?.simplify()?;
    assert_eq!(result, ctx.fpv(-1.5f64)?);

    let result = ctx.fp_neg(ctx.fpv(-2.5f64)?)?.simplify()?;
    assert_eq!(result, ctx.fpv(2.5f64)?);

    // Negating +0.0 yields -0.0. Note that Float's derived PartialEq uses
    // native float equality (so FPV(-0.0) == FPV(0.0) as AST nodes); check
    // the sign bit explicitly to observe the distinct bit pattern.
    let result = ctx.fp_neg(ctx.fpv(0.0f64)?)?.simplify()?;
    assert_eq!(result, ctx.fpv(-0.0f64)?);
    assert!(matches!(result.op(), AstOp::FPV(f) if f.sign() && f.is_zero()));

    Ok(())
}

#[test]
fn test_fp_abs_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx.fp_abs(ctx.fpv(-2.5f64)?)?.simplify()?;
    assert_eq!(result, ctx.fpv(2.5f64)?);

    let result = ctx.fp_abs(ctx.fpv(2.5f64)?)?.simplify()?;
    assert_eq!(result, ctx.fpv(2.5f64)?);

    let result = ctx.fp_abs(ctx.fpv(-0.0f64)?)?.simplify()?;
    assert!(matches!(result.op(), AstOp::FPV(f) if !f.sign() && f.is_zero()));

    Ok(())
}

#[test]
fn test_fp_neg_abs_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    assert!(matches!(
        ctx.fp_neg(&x)?.simplify()?.op(),
        AstOp::FpNeg(..)
    ));
    assert!(matches!(
        ctx.fp_abs(&x)?.simplify()?.op(),
        AstOp::FpAbs(..)
    ));

    Ok(())
}

// -- FpAdd / FpSub / FpMul / FpDiv --

#[test]
fn test_fp_add_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_add(ctx.fpv(1.5f64)?, ctx.fpv(2.25f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(3.75f64)?);

    // The concrete fold uses native f64 arithmetic regardless of the
    // requested rounding mode, so TowardZero yields the same node.
    let result_tz = ctx
        .fp_add(ctx.fpv(1.5f64)?, ctx.fpv(2.25f64)?, FPRM::TowardZero)?
        .simplify()?;
    assert_eq!(result_tz, result);

    Ok(())
}

#[test]
fn test_fp_sub_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_sub(ctx.fpv(5.5f64)?, ctx.fpv(2.25f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(3.25f64)?);

    Ok(())
}

#[test]
fn test_fp_mul_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_mul(ctx.fpv(3.0f64)?, ctx.fpv(2.5f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(7.5f64)?);

    Ok(())
}

#[test]
fn test_fp_div_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_div(ctx.fpv(7.0f64)?, ctx.fpv(2.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(3.5f64)?);

    Ok(())
}

#[test]
fn test_fp_div_by_zero_concrete() -> Result<()> {
    let ctx = Context::new();

    // IEEE semantics: x/0 is +/- infinity, 0/0 is NaN
    let result = ctx
        .fp_div(ctx.fpv(1.0f64)?, ctx.fpv(0.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(f64::INFINITY)?);

    let result = ctx
        .fp_div(ctx.fpv(-1.0f64)?, ctx.fpv(0.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(f64::NEG_INFINITY)?);

    let result = ctx
        .fp_div(ctx.fpv(0.0f64)?, ctx.fpv(0.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::FPV(f) if f.is_nan()));

    Ok(())
}

#[test]
fn test_fp_arith_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let one = ctx.fpv(1.0f64)?;

    assert!(matches!(
        ctx.fp_add(&x, &one, FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::FpAdd(..)
    ));
    assert!(matches!(
        ctx.fp_sub(&x, &one, FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::FpSub(..)
    ));
    assert!(matches!(
        ctx.fp_mul(&x, &one, FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::FpMul(..)
    ));
    assert!(matches!(
        ctx.fp_div(&x, &one, FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::FpDiv(..)
    ));

    Ok(())
}

// -- FpSqrt --

#[test]
fn test_fp_sqrt_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_sqrt(ctx.fpv(4.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(2.0f64)?);

    let result = ctx
        .fp_sqrt(ctx.fpv(2.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(2.0f64.sqrt())?);

    // sqrt of a negative number is NaN
    let result = ctx
        .fp_sqrt(ctx.fpv(-1.0f64)?, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::FPV(f) if f.is_nan()));

    Ok(())
}

#[test]
fn test_fp_sqrt_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let result = ctx.fp_sqrt(&x, FPRM::NearestTiesToEven)?.simplify()?;
    assert!(matches!(result.op(), AstOp::FpSqrt(..)));

    Ok(())
}

// -- FpToFp --

#[test]
fn test_fp_to_fp_same_sort_is_identity() -> Result<()> {
    let ctx = Context::new();

    let val = ctx.fpv(1.5f64)?;
    let result = ctx
        .fp_to_fp(&val, FSort::f64(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, val);

    Ok(())
}

#[test]
fn test_fp_to_fp_f64_to_f32() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_to_fp(ctx.fpv(1.5f64)?, FSort::f32(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(1.5f32)?);

    // Values not exactly representable in f32 round via the native cast
    let result = ctx
        .fp_to_fp(ctx.fpv(0.1f64)?, FSort::f32(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(0.1f64 as f32)?);

    Ok(())
}

#[test]
fn test_fp_to_fp_f32_to_f64() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_to_fp(ctx.fpv(1.5f32)?, FSort::f64(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(1.5f64)?);

    Ok(())
}

#[test]
fn test_fp_to_fp_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let result = ctx
        .fp_to_fp(&x, FSort::f32(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::FpToFp(..)));

    Ok(())
}

// -- BvToFp (bit reinterpretation) --

#[test]
fn test_bv_to_fp_concrete() -> Result<()> {
    let ctx = Context::new();

    // Reinterpret the IEEE 754 bit pattern of 1.0f64
    let result = ctx
        .bv_to_fp(
            ctx.bvv(BitVec::from((1.0f64.to_bits(), 64)))?,
            FSort::f64(),
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(1.0f64)?);

    // And of -2.5f32
    let result = ctx
        .bv_to_fp(
            ctx.bvv(BitVec::from(((-2.5f32).to_bits() as u64, 32)))?,
            FSort::f32(),
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(-2.5f32)?);

    Ok(())
}

#[test]
fn test_bv_to_fp_size_mismatch_is_error() -> Result<()> {
    let ctx = Context::new();

    // A 32-bit bitvector cannot be reinterpreted as a 64-bit float
    let expr = ctx.bv_to_fp(ctx.bvv(BitVec::from((0u64, 32)))?, FSort::f64())?;
    assert!(expr.simplify().is_err());

    Ok(())
}

// -- BvToFpSigned / BvToFpUnsigned --

#[test]
fn test_bv_to_fp_signed_concrete() -> Result<()> {
    let ctx = Context::new();

    // 0xFFFFFFFD as a signed 32-bit integer is -3
    let neg3 = ctx.bvv(BitVec::from((0xFFFF_FFFDu64, 32)))?;
    let result = ctx
        .bv_to_fp_signed(&neg3, FSort::f64(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(-3.0f64)?);

    let result = ctx
        .bv_to_fp_signed(&neg3, FSort::f32(), FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.fpv(-3.0f32)?);

    // Positive values convert directly
    let result = ctx
        .bv_to_fp_signed(
            ctx.bvv(BitVec::from((5u64, 32)))?,
            FSort::f64(),
            FPRM::NearestTiesToEven,
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(5.0f64)?);

    Ok(())
}

#[test]
fn test_bv_to_fp_unsigned_concrete() -> Result<()> {
    let ctx = Context::new();

    // The same bit pattern interpreted unsigned is 4294967293
    let result = ctx
        .bv_to_fp_unsigned(
            ctx.bvv(BitVec::from((0xFFFF_FFFDu64, 32)))?,
            FSort::f64(),
            FPRM::NearestTiesToEven,
        )?
        .simplify()?;
    assert_eq!(result, ctx.fpv(4294967293.0f64)?);

    Ok(())
}

#[test]
fn test_bv_to_fp_signed_unsigned_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.bvs("x", 32)?;
    assert!(matches!(
        ctx.bv_to_fp_signed(&x, FSort::f64(), FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::BvToFpSigned(..)
    ));
    assert!(matches!(
        ctx.bv_to_fp_unsigned(&x, FSort::f64(), FPRM::NearestTiesToEven)?
            .simplify()?
            .op(),
        AstOp::BvToFpUnsigned(..)
    ));

    Ok(())
}

// -- FpToIEEEBV --

#[test]
fn test_fp_to_ieeebv_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx.fp_to_ieeebv(ctx.fpv(1.0f64)?)?.simplify()?;
    assert_eq!(result, ctx.bvv(BitVec::from((1.0f64.to_bits(), 64)))?);

    let result = ctx.fp_to_ieeebv(ctx.fpv(-2.5f32)?)?.simplify()?;
    assert_eq!(
        result,
        ctx.bvv(BitVec::from(((-2.5f32).to_bits() as u64, 32)))?
    );

    Ok(())
}

#[test]
fn test_fp_to_ieeebv_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let result = ctx.fp_to_ieeebv(&x)?.simplify()?;
    assert!(matches!(result.op(), AstOp::FpToIEEEBV(..)));

    Ok(())
}

// -- FpToUBV / FpToSBV --

#[test]
fn test_fp_to_ubv_concrete() -> Result<()> {
    let ctx = Context::new();

    // The fractional part is truncated
    let result = ctx
        .fp_to_ubv(ctx.fpv(7.9f64)?, 32, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.bvv(BitVec::from((7u64, 32)))?);

    // Negative floats saturate to 0 in the unsigned conversion
    let result = ctx
        .fp_to_ubv(ctx.fpv(-3.0f64)?, 32, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.bvv(BitVec::from((0u64, 32)))?);

    Ok(())
}

#[test]
fn test_fp_to_sbv_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .fp_to_sbv(ctx.fpv(42.9f64)?, 32, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.bvv(BitVec::from((42u64, 32)))?);

    Ok(())
}

#[test]
fn test_fp_to_sbv_negative_documents_current_behavior() -> Result<()> {
    let ctx = Context::new();

    // SUSPECTED BUG: converting a negative float with fp.to_sbv currently
    // yields 0 rather than the two's-complement encoding (0xFFFFFFFD for
    // -3). The simplifier converts through BigInt::to_biguint(), which
    // returns None for negative values and falls back to zero. This test
    // documents the current behavior.
    let result = ctx
        .fp_to_sbv(ctx.fpv(-3.0f64)?, 32, FPRM::NearestTiesToEven)?
        .simplify()?;
    assert_eq!(result, ctx.bvv(BitVec::from((0u64, 32)))?);

    Ok(())
}

// -- Comparisons (fp_eq / fp_lt / fp_leq / fp_gt / fp_geq) --

#[test]
fn test_fp_comparisons_concrete() -> Result<()> {
    let ctx = Context::new();

    let one = ctx.fpv(1.0f64)?;
    let two = ctx.fpv(2.0f64)?;
    let true_ = ctx.true_()?;
    let false_ = ctx.false_()?;

    assert_eq!(ctx.fp_lt(&one, &two)?.simplify()?, true_);
    assert_eq!(ctx.fp_lt(&two, &one)?.simplify()?, false_);
    assert_eq!(ctx.fp_lt(&one, &one)?.simplify()?, false_);

    assert_eq!(ctx.fp_leq(&one, &two)?.simplify()?, true_);
    assert_eq!(ctx.fp_leq(&one, &one)?.simplify()?, true_);
    assert_eq!(ctx.fp_leq(&two, &one)?.simplify()?, false_);

    assert_eq!(ctx.fp_gt(&two, &one)?.simplify()?, true_);
    assert_eq!(ctx.fp_gt(&one, &two)?.simplify()?, false_);
    assert_eq!(ctx.fp_gt(&one, &one)?.simplify()?, false_);

    assert_eq!(ctx.fp_geq(&two, &one)?.simplify()?, true_);
    assert_eq!(ctx.fp_geq(&one, &one)?.simplify()?, true_);
    assert_eq!(ctx.fp_geq(&one, &two)?.simplify()?, false_);

    assert_eq!(ctx.fp_eq(&one, &one)?.simplify()?, true_);
    assert_eq!(ctx.fp_eq(&one, &two)?.simplify()?, false_);

    Ok(())
}

#[test]
fn test_fp_comparisons_nan() -> Result<()> {
    let ctx = Context::new();

    let nan = ctx.fpv(f64::NAN)?;
    let one = ctx.fpv(1.0f64)?;
    let false_ = ctx.false_()?;

    // All ordered comparisons involving NaN are false, including NaN == NaN
    assert_eq!(ctx.fp_eq(&nan, &nan)?.simplify()?, false_);
    assert_eq!(ctx.fp_lt(&nan, &one)?.simplify()?, false_);
    assert_eq!(ctx.fp_leq(&nan, &one)?.simplify()?, false_);
    assert_eq!(ctx.fp_gt(&nan, &one)?.simplify()?, false_);
    assert_eq!(ctx.fp_geq(&nan, &one)?.simplify()?, false_);
    assert_eq!(ctx.fp_lt(&one, &nan)?.simplify()?, false_);

    Ok(())
}

#[test]
fn test_fp_eq_signed_zero_documents_current_behavior() -> Result<()> {
    let ctx = Context::new();

    // Note: IEEE 754 fp.eq treats +0.0 and -0.0 as equal, but clarirs'
    // Float::compare_fp deliberately distinguishes them by sign bit
    // (see the test suite in clarirs-num). This test documents that
    // simplification follows compare_fp.
    let pos_zero = ctx.fpv(0.0f64)?;
    let neg_zero = ctx.fpv(-0.0f64)?;

    assert_eq!(ctx.fp_eq(&pos_zero, &neg_zero)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.fp_eq(&pos_zero, &pos_zero)?.simplify()?, ctx.true_()?);

    // The ordered comparisons treat the two zeros as equal in magnitude
    assert_eq!(ctx.fp_lt(&neg_zero, &pos_zero)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.fp_leq(&neg_zero, &pos_zero)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.fp_geq(&pos_zero, &neg_zero)?.simplify()?, ctx.true_()?);

    Ok(())
}

#[test]
fn test_fp_comparisons_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.fps("x", FSort::f64())?;
    let one = ctx.fpv(1.0f64)?;

    assert!(matches!(
        ctx.fp_lt(&x, &one)?.simplify()?.op(),
        AstOp::FpLt(..)
    ));
    assert!(matches!(
        ctx.fp_leq(&x, &one)?.simplify()?.op(),
        AstOp::FpLeq(..)
    ));
    assert!(matches!(
        ctx.fp_gt(&x, &one)?.simplify()?.op(),
        AstOp::FpGt(..)
    ));
    assert!(matches!(
        ctx.fp_geq(&x, &one)?.simplify()?.op(),
        AstOp::FpGeq(..)
    ));

    Ok(())
}

// -- FpIsNan / FpIsInf --

#[test]
fn test_fp_is_nan() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.fp_is_nan(ctx.fpv(f64::NAN)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_nan(ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.false_()?
    );
    assert_eq!(
        ctx.fp_is_nan(ctx.fpv(f64::INFINITY)?)?.simplify()?,
        ctx.false_()?
    );

    let x = ctx.fps("x", FSort::f64())?;
    assert!(matches!(
        ctx.fp_is_nan(&x)?.simplify()?.op(),
        AstOp::FpIsNan(..)
    ));

    Ok(())
}

#[test]
fn test_fp_is_inf() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.fp_is_inf(ctx.fpv(f64::INFINITY)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_inf(ctx.fpv(f64::NEG_INFINITY)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_inf(ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.false_()?
    );
    assert_eq!(
        ctx.fp_is_inf(ctx.fpv(f64::NAN)?)?.simplify()?,
        ctx.false_()?
    );

    let x = ctx.fps("x", FSort::f64())?;
    assert!(matches!(
        ctx.fp_is_inf(&x)?.simplify()?.op(),
        AstOp::FpIsInf(..)
    ));

    Ok(())
}

// -- ITE --

#[test]
fn test_fp_ite_concrete_condition() -> Result<()> {
    let ctx = Context::new();

    let then_ = ctx.fpv(1.0f64)?;
    let else_ = ctx.fpv(2.0f64)?;

    let result = ctx.ite(ctx.true_()?, &then_, &else_)?.simplify()?;
    assert_eq!(result, then_);

    let result = ctx.ite(ctx.false_()?, &then_, &else_)?.simplify()?;
    assert_eq!(result, else_);

    Ok(())
}

#[test]
fn test_fp_ite_equal_branches() -> Result<()> {
    let ctx = Context::new();

    // With identical branches, the (symbolic) condition is dropped
    let branch = ctx.fpv(1.5f64)?;
    let result = ctx.ite(ctx.bools("c")?, &branch, &branch)?.simplify()?;
    assert_eq!(result, branch);

    // Branches that only become equal after simplification also collapse
    let sum = ctx.fp_add(ctx.fpv(1.0f64)?, ctx.fpv(0.5f64)?, FPRM::NearestTiesToEven)?;
    let result = ctx.ite(ctx.bools("c")?, sum, &branch)?.simplify()?;
    assert_eq!(result, branch);

    Ok(())
}

#[test]
fn test_fp_ite_not_condition_inverts_branches() -> Result<()> {
    let ctx = Context::new();

    let c = ctx.bools("c")?;
    let a = ctx.fpv(1.0f64)?;
    let b = ctx.fpv(2.0f64)?;

    // ite(!c, a, b) => ite(c, b, a)
    let result = ctx.ite(ctx.not(&c)?, &a, &b)?.simplify()?;
    assert_eq!(result, ctx.ite(&c, &b, &a)?);

    Ok(())
}

#[test]
fn test_fp_ite_symbolic_preserved() -> Result<()> {
    let ctx = Context::new();

    let expr = ctx.ite(ctx.bools("c")?, ctx.fpv(1.0f64)?, ctx.fpv(2.0f64)?)?;
    assert_eq!(expr.simplify()?, expr);

    Ok(())
}
