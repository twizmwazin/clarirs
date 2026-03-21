use clarirs_core::prelude::*;
use z3::ast::{Ast, BV, Bool, Dynamic, Float};

use super::AstExtZ3;

fn round_trip<'c>(ctx: &'c Context<'c>, ast: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
    BoolAst::from_z3(ctx, ast.to_z3()?)
}

// ---------------------------------------------------------------
// to_z3 tests
// ---------------------------------------------------------------
mod to_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let sym = ctx.bools("x").unwrap();
        let z3_ast = sym.to_z3().unwrap();
        assert_eq!(
            z3_ast.safe_decl().unwrap().kind(),
            z3::DeclKind::UNINTERPRETED
        );
        assert_eq!(z3_ast.safe_decl().unwrap().name(), "x");
    }

    #[test]
    fn true_value() {
        let ctx = Context::new();
        let t = ctx.true_().unwrap();
        let z3_ast = t.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::TRUE);
    }

    #[test]
    fn false_value() {
        let ctx = Context::new();
        let f = ctx.false_().unwrap();
        let z3_ast = f.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FALSE);
    }

    // -- Pure boolean ops --

    #[test]
    fn not() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let not_x = ctx.not(x).unwrap();
        let z3_ast = not_x.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::NOT);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
    }

    #[test]
    fn and_2args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let and = ctx.and2(x, y).unwrap();
        let z3_ast = and.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::AND);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
    }

    #[test]
    fn and_3args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let z = ctx.bools("z").unwrap();
        let and = ctx.and([x, y, z]).unwrap();
        let z3_ast = and.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::AND);
        assert_eq!(z3_ast.num_children(), 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
        assert_eq!(
            z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(),
            "z"
        );
    }

    #[test]
    fn or_2args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let or = ctx.or2(x, y).unwrap();
        let z3_ast = or.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::OR);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
    }

    #[test]
    fn or_3args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let z = ctx.bools("z").unwrap();
        let or = ctx.or([x, y, z]).unwrap();
        let z3_ast = or.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::OR);
        assert_eq!(z3_ast.num_children(), 3);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
        assert_eq!(
            z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(),
            "z"
        );
    }

    #[test]
    fn xor() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let xor = ctx.xor(x, y).unwrap();
        let z3_ast = xor.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::XOR);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
    }

    #[test]
    fn bool_eq() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let eq = ctx.eq_(x, y).unwrap();
        let z3_ast = eq.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::EQ);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
    }

    #[test]
    fn bool_neq() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let neq = ctx.neq(x, y).unwrap();
        let z3_ast = neq.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::DISTINCT);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "x"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "y"
        );
    }

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let t = ctx.bools("t").unwrap();
        let e = ctx.bools("e").unwrap();
        let ite = ctx.ite(c, t, e).unwrap();
        let z3_ast = ite.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ITE);
        assert_eq!(
            z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(),
            "c"
        );
        assert_eq!(
            z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(),
            "t"
        );
        assert_eq!(
            z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(),
            "e"
        );
    }

    // -- BV comparisons --

    #[test]
    fn bv_eq() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let eq = ctx.eq_(a, b).unwrap();
        let z3_ast = eq.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::EQ);
    }

    #[test]
    fn bv_neq() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let neq = ctx.neq(a, b).unwrap();
        let z3_ast = neq.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::DISTINCT);
    }

    #[test]
    fn ult() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.ult(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ULT);
    }

    #[test]
    fn ule() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.ule(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ULEQ);
    }

    #[test]
    fn ugt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.ugt(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::UGT);
    }

    #[test]
    fn uge() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.uge(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::UGEQ);
    }

    #[test]
    fn slt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.slt(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SLT);
    }

    #[test]
    fn sle() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.sle(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SLEQ);
    }

    #[test]
    fn sgt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.sgt(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SGT);
    }

    #[test]
    fn sge() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let r = ctx.sge(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SGEQ);
    }

    // -- FP comparisons --

    #[test]
    fn fp_eq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_eq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_EQ);
    }

    #[test]
    fn fp_neq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_neq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::DISTINCT);
    }

    #[test]
    fn fp_lt() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_lt(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_LT);
    }

    #[test]
    fn fp_leq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_leq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_LE);
    }

    #[test]
    fn fp_gt() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_gt(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_GT);
    }

    #[test]
    fn fp_geq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let r = ctx.fp_geq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_GE);
    }

    #[test]
    fn fp_is_nan() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let r = ctx.fp_is_nan(a).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_IS_NAN);
    }

    #[test]
    fn fp_is_inf() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let r = ctx.fp_is_inf(a).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::FPA_IS_INF);
    }

    // -- String predicates --

    #[test]
    fn str_contains() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let r = ctx.str_contains(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(
            z3_ast.safe_decl().unwrap().kind(),
            z3::DeclKind::SEQ_CONTAINS
        );
    }

    #[test]
    fn str_prefix_of() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let r = ctx.str_prefix_of(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_PREFIX);
    }

    #[test]
    fn str_suffix_of() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let r = ctx.str_suffix_of(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_SUFFIX);
    }

    #[test]
    fn str_eq() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let r = ctx.str_eq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::EQ);
    }

    #[test]
    fn str_neq() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let r = ctx.str_neq(a, b).unwrap();
        let z3_ast = r.to_z3().unwrap();
        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::DISTINCT);
    }
}

// ---------------------------------------------------------------
// from_z3 tests
// ---------------------------------------------------------------
mod from_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(Bool::new_const("x"));
        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        assert_eq!(result, ctx.bools("x").unwrap());
    }

    #[test]
    fn true_value() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(Bool::from_bool(true));
        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        assert_eq!(result, ctx.true_().unwrap());
    }

    #[test]
    fn false_value() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(Bool::from_bool(false));
        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        assert_eq!(result, ctx.false_().unwrap());
    }

    // -- Pure boolean ops --

    #[test]
    fn not() {
        let ctx = Context::new();
        let x = Bool::new_const("x");
        let not_z3 = Dynamic::from(x.not());

        let result = BoolAst::from_z3(&ctx, not_z3).unwrap();
        let expected = ctx.not(ctx.bools("x").unwrap()).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn and_2args() {
        let ctx = Context::new();
        let x = Bool::new_const("x");
        let y = Bool::new_const("y");
        let and_z3 = Dynamic::from(Bool::and(&[&x, &y]));

        let result = BoolAst::from_z3(&ctx, and_z3).unwrap();
        let expected = ctx
            .and2(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn or_2args() {
        let ctx = Context::new();
        let x = Bool::new_const("x");
        let y = Bool::new_const("y");
        let or_z3 = Dynamic::from(Bool::or(&[&x, &y]));

        let result = BoolAst::from_z3(&ctx, or_z3).unwrap();
        let expected = ctx
            .or2(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn xor() {
        let ctx = Context::new();
        let x = Bool::new_const("x");
        let y = Bool::new_const("y");
        let xor_z3 = Dynamic::from(x.xor(&y));

        let result = BoolAst::from_z3(&ctx, xor_z3).unwrap();
        let expected = ctx
            .xor(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn bool_eq() {
        let ctx = Context::new();
        let x = Dynamic::from(Bool::new_const("x"));
        let y = Dynamic::from(Bool::new_const("y"));
        let eq_z3 = Dynamic::from(x.eq(&y));

        let result = BoolAst::from_z3(&ctx, eq_z3).unwrap();
        let expected = ctx
            .eq_(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn bool_neq() {
        let ctx = Context::new();
        let x = Dynamic::from(Bool::new_const("x"));
        let y = Dynamic::from(Bool::new_const("y"));
        let neq_z3 = Dynamic::from(Dynamic::distinct(&[&x, &y]));

        let result = BoolAst::from_z3(&ctx, neq_z3).unwrap();
        let expected = ctx
            .neq(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = Bool::new_const("c");
        let t = Dynamic::from(Bool::from_bool(true));
        let e = Dynamic::from(Bool::from_bool(false));
        let ite_z3 = c.ite(&t, &e);

        let result = BoolAst::from_z3(&ctx, ite_z3).unwrap();
        let expected = ctx
            .ite(
                ctx.bools("c").unwrap(),
                ctx.true_().unwrap(),
                ctx.false_().unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    // -- BV comparisons --

    #[test]
    fn bv_eq() {
        let ctx = Context::new();
        let a = Dynamic::from(BV::new_const("a", 32));
        let b = Dynamic::from(BV::new_const("b", 32));
        let eq_z3 = Dynamic::from(a.eq(&b));

        let result = BoolAst::from_z3(&ctx, eq_z3).unwrap();
        let expected = ctx
            .eq_(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn bv_neq() {
        let ctx = Context::new();
        let a = Dynamic::from(BV::new_const("a", 32));
        let b = Dynamic::from(BV::new_const("b", 32));
        let neq_z3 = Dynamic::from(Dynamic::distinct(&[&a, &b]));

        let result = BoolAst::from_z3(&ctx, neq_z3).unwrap();
        let expected = ctx
            .neq(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn ult() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvult(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .ult(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn ule() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvule(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .ule(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn ugt() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvugt(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .ugt(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn uge() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvuge(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .uge(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn slt() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvslt(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .slt(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn sle() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvsle(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .sle(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn sgt() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvsgt(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .sgt(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn sge() {
        let ctx = Context::new();
        let a = BV::new_const("a", 32);
        let b = BV::new_const("b", 32);
        let z3_ast = Dynamic::from(a.bvsge(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .sge(ctx.bvs("a", 32).unwrap(), ctx.bvs("b", 32).unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    // -- FP comparisons --

    #[test]
    fn fp_eq() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let b = Float::new_const("b", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.eq_fpa(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .fp_eq(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_neq() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Dynamic::from(Float::new_const("a", sort.exponent, sort.mantissa + 1));
        let b = Dynamic::from(Float::new_const("b", sort.exponent, sort.mantissa + 1));
        let z3_ast = Dynamic::from(Dynamic::distinct(&[&a, &b]));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .neq(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_lt() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let b = Float::new_const("b", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.lt(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .fp_lt(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_leq() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let b = Float::new_const("b", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.le(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .fp_leq(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_gt() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let b = Float::new_const("b", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.gt(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .fp_gt(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_geq() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let b = Float::new_const("b", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.ge(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .fp_geq(
                ctx.fps("a", FSort::f32()).unwrap(),
                ctx.fps("b", FSort::f32()).unwrap(),
            )
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_is_nan() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.is_nan());

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fp_is_nan(ctx.fps("a", FSort::f32()).unwrap()).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn fp_is_inf() {
        let ctx = Context::new();
        let sort = FSort::f32();
        let a = Float::new_const("a", sort.exponent, sort.mantissa + 1);
        let z3_ast = Dynamic::from(a.is_infinite());

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.fp_is_inf(ctx.fps("a", FSort::f32()).unwrap()).unwrap();
        assert_eq!(result, expected);
    }

    // -- String predicates --

    #[test]
    fn str_contains() {
        let ctx = Context::new();
        let a = z3::ast::String::new_const("a");
        let b = z3::ast::String::new_const("b");
        let z3_ast = Dynamic::from(a.contains(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .str_contains(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn str_prefix_of() {
        let ctx = Context::new();
        let a = z3::ast::String::new_const("a");
        let b = z3::ast::String::new_const("b");
        let z3_ast = Dynamic::from(a.prefix(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .str_prefix_of(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn str_suffix_of() {
        let ctx = Context::new();
        let a = z3::ast::String::new_const("a");
        let b = z3::ast::String::new_const("b");
        let z3_ast = Dynamic::from(a.suffix(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .str_suffix_of(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn str_eq() {
        let ctx = Context::new();
        let a = Dynamic::from(z3::ast::String::new_const("a"));
        let b = Dynamic::from(z3::ast::String::new_const("b"));
        let z3_ast = Dynamic::from(a.eq(&b));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .eq_(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn str_neq() {
        let ctx = Context::new();
        let a = Dynamic::from(z3::ast::String::new_const("a"));
        let b = Dynamic::from(z3::ast::String::new_const("b"));
        let z3_ast = Dynamic::from(Dynamic::distinct(&[&a, &b]));

        let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx
            .neq(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(result, expected);
    }
}

// ---------------------------------------------------------------
// roundtrip tests
// ---------------------------------------------------------------
mod roundtrip {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let ast = ctx.bools("x").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn true_value() {
        let ctx = Context::new();
        let ast = ctx.true_().unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn false_value() {
        let ctx = Context::new();
        let ast = ctx.false_().unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- Pure boolean ops --

    #[test]
    fn not() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let ast = ctx.not(x).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn and_2args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let ast = ctx.and2(x, y).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn and_3args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let z = ctx.bools("z").unwrap();
        let ast = ctx.and([x, y, z]).unwrap();
        // With n-ary And/Or support, a 3-arg And round-trips exactly.
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn or_2args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let ast = ctx.or2(x, y).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn or_3args() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let z = ctx.bools("z").unwrap();
        let ast = ctx.or([x, y, z]).unwrap();
        // With n-ary And/Or support, a 3-arg Or round-trips exactly.
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn xor() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let ast = ctx.xor(x, y).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bool_eq() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let ast = ctx.eq_(x, y).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bool_neq() {
        let ctx = Context::new();
        let x = ctx.bools("x").unwrap();
        let y = ctx.bools("y").unwrap();
        let ast = ctx.neq(x, y).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let t = ctx.bools("t").unwrap();
        let e = ctx.bools("e").unwrap();
        let ast = ctx.ite(c, t, e).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- BV comparisons --

    #[test]
    fn bv_eq() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.eq_(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bv_neq() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.neq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ult() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.ult(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ule() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.ule(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ugt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.ugt(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn uge() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.uge(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn slt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.slt(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn sle() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.sle(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn sgt() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.sgt(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn sge() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let ast = ctx.sge(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- FP comparisons --

    #[test]
    fn fp_eq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_eq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_neq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_neq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_lt() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_lt(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_leq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_leq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_gt() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_gt(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_geq() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let ast = ctx.fp_geq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_is_nan() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let ast = ctx.fp_is_nan(a).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn fp_is_inf() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let ast = ctx.fp_is_inf(a).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- String predicates --

    #[test]
    fn str_contains() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.str_contains(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn str_prefix_of() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.str_prefix_of(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn str_suffix_of() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.str_suffix_of(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn str_eq() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.str_eq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn str_neq() {
        let ctx = Context::new();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.str_neq(a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- StrIsDigit --
    // StrIsDigit is encoded as a composite Z3 expression, so round-trip
    // won't produce the same AST. We test that to_z3 succeeds.

    #[test]
    fn str_is_digit_symbol() {
        let ctx = Context::new();
        let s = ctx.strings("s").unwrap();
        let ast = ctx.str_is_digit(s).unwrap();
        assert!(ast.to_z3().is_ok());
    }

    #[test]
    fn str_is_digit_value() {
        let ctx = Context::new();
        let s = ctx.stringv("123").unwrap();
        let ast = ctx.str_is_digit(s).unwrap();
        assert!(ast.to_z3().is_ok());
    }
}
