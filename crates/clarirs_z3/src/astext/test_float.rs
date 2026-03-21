use clarirs_core::prelude::*;
use z3::ast::{Ast, Dynamic, Bool, BV, RoundingMode};

use super::AstExtZ3;

fn round_trip<'c>(ctx: &'c Context<'c>, ast: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
    FloatAst::from_z3(ctx, ast.to_z3()?)
}

// ---------------------------------------------------------------
// to_z3 tests
// ---------------------------------------------------------------
mod to_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol_f32() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let z3_ast = x.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::UNINTERPRETED);
        assert_eq!(z3_ast.safe_decl().unwrap().name(), "x");
    }

    #[test]
    fn symbol_f64() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f64()).unwrap();
        let z3_ast = x.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::UNINTERPRETED);
        assert_eq!(z3_ast.safe_decl().unwrap().name(), "x");
    }

    #[test]
    fn value_f32() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F32(3.14f32)).unwrap();
        let z3_ast = f.to_z3().unwrap();
        // Z3 represents float numerals as FpaNum
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_NUM);
    }

    #[test]
    fn value_f64() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F64(2.718281828459045f64)).unwrap();
        let z3_ast = f.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_NUM);
    }

    #[test]
    fn value_f32_zero() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F32(0.0f32)).unwrap();
        let z3_ast = f.to_z3().unwrap();
        // Z3 may represent +0.0 as FpaNum or FpaPlusZero
        let dk = z3_ast.safe_decl().unwrap().kind();
        assert!(dk == z3::DeclKind::FPA_NUM || dk == z3::DeclKind::FPA_PLUS_ZERO);
    }

    #[test]
    fn value_f32_neg_zero() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F32(-0.0f32)).unwrap();
        let z3_ast = f.to_z3().unwrap();
        let dk = z3_ast.safe_decl().unwrap().kind();
        assert!(dk == z3::DeclKind::FPA_NUM || dk == z3::DeclKind::FPA_MINUS_ZERO);
    }

    // -- Unary ops --

    #[test]
    fn fp_neg() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let neg = ctx.fp_neg(x).unwrap();
        let z3_ast = neg.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_NEG);
        assert_eq!(z3_ast.num_children() as u32, 1);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "x");
    }

    #[test]
    fn fp_abs() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let abs = ctx.fp_abs(x).unwrap();
        let z3_ast = abs.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_ABS);
        assert_eq!(z3_ast.num_children() as u32, 1);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "x");
    }

    // -- Binary arithmetic ops (with rounding mode) --

    #[test]
    fn fp_add() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::NearestTiesToEven).unwrap();
        let z3_ast = add.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_ADD);
        // 3 args: rounding mode, a, b
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN
        );
        assert_eq!(z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(), "a");
        assert_eq!(z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(), "b");
    }

    #[test]
    fn fp_sub() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let sub = ctx.fp_sub(a, b, FPRM::TowardZero).unwrap();
        let z3_ast = sub.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_SUB);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_ZERO
        );
    }

    #[test]
    fn fp_mul() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let mul = ctx.fp_mul(a, b, FPRM::TowardPositive).unwrap();
        let z3_ast = mul.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_MUL);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_POSITIVE
        );
    }

    #[test]
    fn fp_div() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let div = ctx.fp_div(a, b, FPRM::TowardNegative).unwrap();
        let z3_ast = div.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_DIV);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_NEGATIVE
        );
    }

    #[test]
    fn fp_sqrt() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let sqrt = ctx.fp_sqrt(x, FPRM::NearestTiesToAway).unwrap();
        let z3_ast = sqrt.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_SQRT);
        // 2 args: rounding mode, operand
        assert_eq!(z3_ast.num_children() as u32, 2);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY
        );
        assert_eq!(z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(), "x");
    }

    // -- Conversion ops --

    #[test]
    fn fp_to_fp() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let conv = ctx
            .fp_to_fp(x, FSort::f64(), FPRM::NearestTiesToEven)
            .unwrap();
        let z3_ast = conv.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_TO_FP);
        // 2 args: rounding mode, operand
        assert_eq!(z3_ast.num_children() as u32, 2);
    }

    #[test]
    fn bv_to_fp() {
        let ctx = Context::new();
        let bv = ctx.bvs("bits", 32).unwrap();
        let conv = ctx.bv_to_fp(bv, FSort::f32()).unwrap();
        let z3_ast = conv.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_TO_FP);
    }

    #[test]
    fn bv_to_fp_signed() {
        let ctx = Context::new();
        let bv = ctx.bvs("bits", 32).unwrap();
        let conv = ctx
            .bv_to_fp_signed(bv, FSort::f32(), FPRM::NearestTiesToEven)
            .unwrap();
        let z3_ast = conv.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_TO_FP);
        assert_eq!(z3_ast.num_children() as u32, 2);
    }

    #[test]
    fn bv_to_fp_unsigned() {
        let ctx = Context::new();
        let bv = ctx.bvs("bits", 32).unwrap();
        let conv = ctx
            .bv_to_fp_unsigned(bv, FSort::f32(), FPRM::NearestTiesToEven)
            .unwrap();
        let z3_ast = conv.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_TO_FP_UNSIGNED);
        assert_eq!(z3_ast.num_children() as u32, 2);
    }

    #[test]
    fn fp_fp() {
        let ctx = Context::new();
        let sign = ctx.bvv_prim(0u8).unwrap();
        let sign = ctx.extract(sign, 0, 0).unwrap(); // 1-bit
        let exp = ctx.bvs("exp", 8).unwrap();
        let sig = ctx.bvs("sig", 23).unwrap();
        let fp = ctx.fp_fp(sign, exp, sig).unwrap();
        let z3_ast = fp.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_FP);
        assert_eq!(z3_ast.num_children() as u32, 3);
    }

    // -- ITE --

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ite = ctx.ite(c, a, b).unwrap();
        let z3_ast = ite.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ITE);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "c");
        assert_eq!(z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(), "a");
        assert_eq!(z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(), "b");
    }

    // -- Rounding modes --

    #[test]
    fn rounding_mode_rne() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::NearestTiesToEven).unwrap();
        let z3_ast = add.to_z3().unwrap();
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN
        );
    }

    #[test]
    fn rounding_mode_rtp() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::TowardPositive).unwrap();
        let z3_ast = add.to_z3().unwrap();
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_POSITIVE
        );
    }

    #[test]
    fn rounding_mode_rtn() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::TowardNegative).unwrap();
        let z3_ast = add.to_z3().unwrap();
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_NEGATIVE
        );
    }

    #[test]
    fn rounding_mode_rtz() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::TowardZero).unwrap();
        let z3_ast = add.to_z3().unwrap();
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_TOWARD_ZERO
        );
    }

    #[test]
    fn rounding_mode_rna() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(a, b, FPRM::NearestTiesToAway).unwrap();
        let z3_ast = add.to_z3().unwrap();
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().kind(),
            z3::DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY
        );
    }
}

// ---------------------------------------------------------------
// from_z3 tests
// ---------------------------------------------------------------
mod from_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol_f32() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_ast = Dynamic::from(z3::ast::Float::new_const("x", sort.exponent, sort.mantissa + 1));
        let result = FloatAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fps("x", FSort::f32()).unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn symbol_f64() {
        let ctx = Context::new();
        let sort = FSort::f64();
        let z3_ast = Dynamic::from(z3::ast::Float::new_const("x", sort.exponent, sort.mantissa + 1));
        let result = FloatAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fps("x", FSort::f64()).unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn value_f32() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(z3::ast::Float::from_f32(3.14f32));
        let result = FloatAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fpv(Float::F32(3.14f32)).unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn value_f64() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(z3::ast::Float::from_f64(2.718281828459045f64));
        let result = FloatAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fpv(Float::F64(2.718281828459045f64)).unwrap();
        assert_eq!(expected, result);
    }

    // -- Unary ops --

    #[test]
    fn fp_neg() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_neg = {
            let x = z3::ast::Float::new_const("x", sort.exponent, sort.mantissa + 1);
            Dynamic::from(x.unary_neg())
        };
        let result = FloatAst::from_z3(&ctx, z3_neg).unwrap();
        let expected = ctx.fp_neg(ctx.fps("x", FSort::f32()).unwrap()).unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn fp_abs() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_abs = {
            let x = z3::ast::Float::new_const("x", sort.exponent, sort.mantissa + 1);
            Dynamic::from(x.unary_abs())
        };
        let result = FloatAst::from_z3(&ctx, z3_abs).unwrap();
        let expected = ctx.fp_abs(ctx.fps("x", FSort::f32()).unwrap()).unwrap();
        assert_eq!(expected, result);
    }

    // -- Binary arithmetic ops --

    #[test]
    fn fp_add() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_add = {
            let a = z3::ast::Float::new_const("a", sort.exponent, sort.mantissa + 1);
            let b = z3::ast::Float::new_const("b", sort.exponent, sort.mantissa + 1);
            let rm = RoundingMode::round_nearest_ties_to_even();
            Dynamic::from(a.add_with_rounding_mode(&b, &rm))
        };
        let result = FloatAst::from_z3(&ctx, z3_add).unwrap();
        let expected = ctx
            .fp_add(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
                FPRM::NearestTiesToEven,
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn fp_sub() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_sub = {
            let a = z3::ast::Float::new_const("a", sort.exponent, sort.mantissa + 1);
            let b = z3::ast::Float::new_const("b", sort.exponent, sort.mantissa + 1);
            let rm = RoundingMode::round_towards_zero();
            Dynamic::from(a.sub_with_rounding_mode(&b, &rm))
        };
        let result = FloatAst::from_z3(&ctx, z3_sub).unwrap();
        let expected = ctx
            .fp_sub(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
                FPRM::TowardZero,
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn fp_mul() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_mul = {
            let a = z3::ast::Float::new_const("a", sort.exponent, sort.mantissa + 1);
            let b = z3::ast::Float::new_const("b", sort.exponent, sort.mantissa + 1);
            let rm = RoundingMode::round_towards_positive();
            Dynamic::from(a.mul_with_rounding_mode(&b, &rm))
        };
        let result = FloatAst::from_z3(&ctx, z3_mul).unwrap();
        let expected = ctx
            .fp_mul(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
                FPRM::TowardPositive,
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn fp_div() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_div = {
            let a = z3::ast::Float::new_const("a", sort.exponent, sort.mantissa + 1);
            let b = z3::ast::Float::new_const("b", sort.exponent, sort.mantissa + 1);
            let rm = RoundingMode::round_towards_negative();
            Dynamic::from(a.div_with_rounding_mode(&b, &rm))
        };
        let result = FloatAst::from_z3(&ctx, z3_div).unwrap();
        let expected = ctx
            .fp_div(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
                FPRM::TowardNegative,
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn fp_sqrt() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_sqrt = {
            let x = z3::ast::Float::new_const("x", sort.exponent, sort.mantissa + 1);
            let rm = RoundingMode::round_nearest_ties_to_away();
            Dynamic::from(x.sqrt_with_rounding_mode(&rm))
        };
        let result = FloatAst::from_z3(&ctx, z3_sqrt).unwrap();
        let expected = ctx
            .fp_sqrt(ctx.fps("x", FSort::f32()).unwrap(), FPRM::NearestTiesToAway)
            .unwrap();
        assert_eq!(expected, result);
    }

    // -- Conversion ops --

    #[test]
    fn fp_fp() {
        let ctx = Context::new();
        let z3_fp = {
            let sign = BV::from_u64(0, 1);
            let exp = BV::new_const("exp", 8);
            let sig = BV::new_const("sig", 23);
            crate::astext::float::float_from_sign_exp_sig(&sign, &exp, &sig)
        };
        let result = FloatAst::from_z3(&ctx, z3_fp).unwrap();

        // Verify it's an FpFP node with the right structure
        match result.op() {
            FloatOp::FpFP(..) => {} // expected
            other => panic!("Expected FpFP, got {:?}", other),
        }
    }

    #[test]
    fn ite() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let z3_ite = {
            let c = Bool::new_const("c");
            let a = Dynamic::from(z3::ast::Float::new_const("a", sort.exponent, sort.mantissa + 1));
            let b = Dynamic::from(z3::ast::Float::new_const("b", sort.exponent, sort.mantissa + 1));
            c.ite(&a, &b)
        };
        let result = FloatAst::from_z3(&ctx, z3_ite).unwrap();
        let expected = ctx
            .ite(
                ctx.bools("c").unwrap(),
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }
}

// ---------------------------------------------------------------
// roundtrip tests
// ---------------------------------------------------------------
mod roundtrip {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol_f32() {
        let ctx = Context::new();
        let ast = ctx.fps("x", FSort::f32()).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn symbol_f64() {
        let ctx = Context::new();
        let ast = ctx.fps("x", FSort::f64()).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f32_pi() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F32(std::f32::consts::PI)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f64_e() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F64(std::f64::consts::E)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f32_one() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F32(1.0f32)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f64_one() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F64(1.0f64)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f32_negative() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F32(-42.5f32)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_f64_negative() {
        let ctx = Context::new();
        let ast = ctx.fpv(Float::F64(-123.456f64)).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- Unary ops --

    #[test]
    fn fp_neg() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let ast = ctx.fp_neg(x).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_abs() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let ast = ctx.fp_abs(x).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- Binary arithmetic ops --

    #[test]
    fn fp_add() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_sub() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_sub(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_mul() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_mul(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_div() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_div(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_sqrt() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let ast = ctx.fp_sqrt(x, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- Conversion ops --

    #[test]
    fn fp_to_fp_f32_to_f64() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let ast = ctx
            .fp_to_fp(x, FSort::f64(), FPRM::NearestTiesToEven)
            .unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_to_fp_f64_to_f32() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f64()).unwrap();
        let ast = ctx
            .fp_to_fp(x, FSort::f32(), FPRM::NearestTiesToEven)
            .unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bv_to_fp() {
        let ctx = Context::new();
        let bv = ctx.bvs("bits", 32).unwrap();
        let ast = ctx.bv_to_fp(bv, FSort::f32()).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bv_to_fp_signed() {
        let ctx = Context::new();
        let bv = ctx.bvs("bits", 32).unwrap();
        let ast = ctx
            .bv_to_fp_signed(bv, FSort::f32(), FPRM::NearestTiesToEven)
            .unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_fp() {
        let ctx = Context::new();
        let sign = ctx.bvv_prim(0u8).unwrap();
        let sign = ctx.extract(sign, 0, 0).unwrap(); // 1-bit
        let exp = ctx.bvs("exp", 8).unwrap();
        let sig = ctx.bvs("sig", 23).unwrap();
        let ast = ctx.fp_fp(sign, exp, sig).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- ITE --

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.ite(c, a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- F64 variants --

    #[test]
    fn fp_neg_f64() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f64()).unwrap();
        let ast = ctx.fp_neg(x).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_abs_f64() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f64()).unwrap();
        let ast = ctx.fp_abs(x).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_add_f64() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f64()).unwrap();
        let b = ctx.fps("b", FSort::f64()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_mul_f64() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f64()).unwrap();
        let b = ctx.fps("b", FSort::f64()).unwrap();
        let ast = ctx.fp_mul(a, b, FPRM::NearestTiesToEven).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- Rounding mode variants --

    #[test]
    fn fp_add_toward_zero() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::TowardZero).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_add_toward_positive() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::TowardPositive).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_add_toward_negative() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::TowardNegative).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_add_nearest_ties_away() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_add(a, b, FPRM::NearestTiesToAway).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }
}
