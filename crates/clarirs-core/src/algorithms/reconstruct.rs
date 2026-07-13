//! Shared helper for reconstructing an AST node from its transformed children.
//! Used by the `replace` algorithm.

use crate::{ast::op::AstOp, prelude::*};

/// Rebuilds `ast`'s op with `children` substituted in, without interning.
/// Returns `None` for leaves. The structural half of [`reconstruct_node`].
pub fn rebuild_op<'c>(ast: &AstRef<'c>, children: &[AstRef<'c>]) -> Option<AstOp<'c>> {
    let c = |i: usize| children[i].clone();
    Some(match ast.op() {
        // Leaves have no children to substitute.
        AstOp::BoolS(..)
        | AstOp::BoolV(..)
        | AstOp::BVS(..)
        | AstOp::BVV(..)
        | AstOp::FPS(..)
        | AstOp::FPV(..)
        | AstOp::StringS(..)
        | AstOp::StringV(..) => return None,

        // N-ary
        AstOp::And(..) => AstOp::And(children.to_vec()),
        AstOp::Or(..) => AstOp::Or(children.to_vec()),
        AstOp::Xor(..) => AstOp::Xor(children.to_vec()),
        AstOp::Add(..) => AstOp::Add(children.to_vec()),
        AstOp::Mul(..) => AstOp::Mul(children.to_vec()),
        AstOp::Concat(..) => AstOp::Concat(children.to_vec()),

        // Unary
        AstOp::Not(..) => AstOp::Not(c(0)),
        AstOp::Neg(..) => AstOp::Neg(c(0)),
        AstOp::ByteReverse(..) => AstOp::ByteReverse(c(0)),
        AstOp::ZeroExt(_, n) => AstOp::ZeroExt(c(0), *n),
        AstOp::SignExt(_, n) => AstOp::SignExt(c(0), *n),
        AstOp::Extract(_, hi, lo) => AstOp::Extract(c(0), *hi, *lo),
        AstOp::StrLen(..) => AstOp::StrLen(c(0)),
        AstOp::StrToBV(..) => AstOp::StrToBV(c(0)),
        AstOp::FpToIEEEBV(..) => AstOp::FpToIEEEBV(c(0)),
        AstOp::FpToUBV(_, size, rm) => AstOp::FpToUBV(c(0), *size, *rm),
        AstOp::FpToSBV(_, size, rm) => AstOp::FpToSBV(c(0), *size, *rm),
        AstOp::FpNeg(..) => AstOp::FpNeg(c(0)),
        AstOp::FpAbs(..) => AstOp::FpAbs(c(0)),
        AstOp::FpSqrt(_, rm) => AstOp::FpSqrt(c(0), *rm),
        AstOp::FpToFp(_, sort, rm) => AstOp::FpToFp(c(0), *sort, *rm),
        AstOp::BvToFp(_, sort) => AstOp::BvToFp(c(0), *sort),
        AstOp::BvToFpSigned(_, sort, rm) => AstOp::BvToFpSigned(c(0), *sort, *rm),
        AstOp::BvToFpUnsigned(_, sort, rm) => AstOp::BvToFpUnsigned(c(0), *sort, *rm),
        AstOp::FpIsNan(..) => AstOp::FpIsNan(c(0)),
        AstOp::FpIsInf(..) => AstOp::FpIsInf(c(0)),
        AstOp::StrIsDigit(..) => AstOp::StrIsDigit(c(0)),
        AstOp::BVToStr(..) => AstOp::BVToStr(c(0)),

        // Binary
        AstOp::Eq(..) => AstOp::Eq(c(0), c(1)),
        AstOp::Neq(..) => AstOp::Neq(c(0), c(1)),
        AstOp::ULT(..) => AstOp::ULT(c(0), c(1)),
        AstOp::ULE(..) => AstOp::ULE(c(0), c(1)),
        AstOp::UGT(..) => AstOp::UGT(c(0), c(1)),
        AstOp::UGE(..) => AstOp::UGE(c(0), c(1)),
        AstOp::SLT(..) => AstOp::SLT(c(0), c(1)),
        AstOp::SLE(..) => AstOp::SLE(c(0), c(1)),
        AstOp::SGT(..) => AstOp::SGT(c(0), c(1)),
        AstOp::SGE(..) => AstOp::SGE(c(0), c(1)),
        AstOp::FpLt(..) => AstOp::FpLt(c(0), c(1)),
        AstOp::FpLeq(..) => AstOp::FpLeq(c(0), c(1)),
        AstOp::FpGt(..) => AstOp::FpGt(c(0), c(1)),
        AstOp::FpGeq(..) => AstOp::FpGeq(c(0), c(1)),
        AstOp::StrContains(..) => AstOp::StrContains(c(0), c(1)),
        AstOp::StrPrefixOf(..) => AstOp::StrPrefixOf(c(0), c(1)),
        AstOp::StrSuffixOf(..) => AstOp::StrSuffixOf(c(0), c(1)),
        AstOp::Sub(..) => AstOp::Sub(c(0), c(1)),
        AstOp::UDiv(..) => AstOp::UDiv(c(0), c(1)),
        AstOp::SDiv(..) => AstOp::SDiv(c(0), c(1)),
        AstOp::URem(..) => AstOp::URem(c(0), c(1)),
        AstOp::SRem(..) => AstOp::SRem(c(0), c(1)),
        AstOp::ShL(..) => AstOp::ShL(c(0), c(1)),
        AstOp::LShR(..) => AstOp::LShR(c(0), c(1)),
        AstOp::AShR(..) => AstOp::AShR(c(0), c(1)),
        AstOp::RotateLeft(..) => AstOp::RotateLeft(c(0), c(1)),
        AstOp::RotateRight(..) => AstOp::RotateRight(c(0), c(1)),
        AstOp::Union(..) => AstOp::Union(c(0), c(1)),
        AstOp::Intersection(..) => AstOp::Intersection(c(0), c(1)),
        AstOp::Widen(..) => AstOp::Widen(c(0), c(1)),
        AstOp::FpAdd(_, _, rm) => AstOp::FpAdd(c(0), c(1), *rm),
        AstOp::FpSub(_, _, rm) => AstOp::FpSub(c(0), c(1), *rm),
        AstOp::FpMul(_, _, rm) => AstOp::FpMul(c(0), c(1), *rm),
        AstOp::FpDiv(_, _, rm) => AstOp::FpDiv(c(0), c(1), *rm),
        AstOp::StrConcat(..) => AstOp::StrConcat(c(0), c(1)),

        // Ternary
        AstOp::ITE(..) => AstOp::ITE(c(0), c(1), c(2)),
        AstOp::StrIndexOf(..) => AstOp::StrIndexOf(c(0), c(1), c(2)),
        AstOp::FpFP(..) => AstOp::FpFP(c(0), c(1), c(2)),
        AstOp::StrSubstr(..) => AstOp::StrSubstr(c(0), c(1), c(2)),
        AstOp::StrReplace(..) => AstOp::StrReplace(c(0), c(1), c(2)),
    })
}

/// Reconstructs a node from its operation and transformed children.
///
/// Leaf nodes are returned as-is. Non-leaf nodes are rebuilt by replacing the
/// op's children with the transformed ones and re-interning via the context;
/// the node's type is re-inferred from the (same-typed) children.
pub fn reconstruct_node<'c>(
    ctx: &'c Context<'c>,
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    match rebuild_op(ast, children) {
        Some(op) => ctx.make_ast(op),
        None => Ok(ast.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    /// Reconstructing a node from its own (untransformed) children must yield
    /// a node equal to the original.
    fn assert_round_trip<'c>(ctx: &'c Context<'c>, ast: &AstRef<'c>) {
        let children: Vec<AstRef<'c>> = ast.child_iter().collect();
        let rebuilt = reconstruct_node(ctx, ast, &children)
            .unwrap_or_else(|e| panic!("reconstruct failed for {:?}: {e:?}", ast.op()));
        assert_eq!(
            rebuilt,
            *ast,
            "round-trip changed node for op {:?}",
            ast.op()
        );
    }

    #[test]
    fn test_rebuild_op_returns_none_for_leaves() {
        let ctx = Context::new();
        let leaves = [
            ctx.bools("b").unwrap(),
            ctx.true_().unwrap(),
            ctx.bvs("x", 32).unwrap(),
            ctx.bvv(BitVec::from((42, 32))).unwrap(),
            ctx.fps("f", FSort::f64()).unwrap(),
            ctx.fpv_from_f64(1.5).unwrap(),
            ctx.strings("s").unwrap(),
            ctx.stringv("hello").unwrap(),
        ];
        for leaf in &leaves {
            assert!(
                rebuild_op(leaf, &[]).is_none(),
                "leaf {:?} should not be rebuilt",
                leaf.op()
            );
        }
    }

    #[test]
    fn test_reconstruct_leaf_returns_same_node() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let result = reconstruct_node(&ctx, &x, &[]).unwrap();
        assert!(Arc::ptr_eq(&result, &x));
    }

    #[test]
    fn test_reconstruct_substitutes_children() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();

        let add = ctx.add(&x, &y).unwrap();
        let rebuilt = reconstruct_node(&ctx, &add, &[a.clone(), b.clone()]).unwrap();
        assert_eq!(rebuilt, ctx.add(&a, &b).unwrap());
    }

    #[test]
    fn test_reconstruct_preserves_non_child_parameters() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let a = ctx.bvs("a", 32).unwrap();

        // Extract keeps its bounds
        let extract = ctx.extract(&x, 15, 8).unwrap();
        let rebuilt = reconstruct_node(&ctx, &extract, &[a.clone()]).unwrap();
        assert_eq!(rebuilt, ctx.extract(&a, 15, 8).unwrap());

        // ZeroExt/SignExt keep their extension width
        let zext = ctx.zero_ext(&x, 16).unwrap();
        let rebuilt = reconstruct_node(&ctx, &zext, &[a.clone()]).unwrap();
        assert_eq!(rebuilt, ctx.zero_ext(&a, 16).unwrap());

        // FpAdd keeps its rounding mode
        let f = ctx.fps("f", FSort::f64()).unwrap();
        let g = ctx.fps("g", FSort::f64()).unwrap();
        let fp_add = ctx.fp_add(&f, &g, FPRM::TowardZero).unwrap();
        let rebuilt = reconstruct_node(&ctx, &fp_add, &[g.clone(), f.clone()]).unwrap();
        assert_eq!(rebuilt, ctx.fp_add(&g, &f, FPRM::TowardZero).unwrap());
        match rebuilt.op() {
            AstOp::FpAdd(_, _, rm) => assert_eq!(*rm, FPRM::TowardZero),
            other => panic!("expected FpAdd, got {other:?}"),
        }
    }

    #[test]
    fn test_round_trip_bool_ops() {
        let ctx = Context::new();
        let a = ctx.bools("a").unwrap();
        let b = ctx.bools("b").unwrap();
        let c = ctx.bools("c").unwrap();

        for ast in [
            ctx.not(&a).unwrap(),
            ctx.and([a.clone(), b.clone(), c.clone()]).unwrap(),
            ctx.or([a.clone(), b.clone()]).unwrap(),
            ctx.xor([a.clone(), b.clone()]).unwrap(),
            ctx.eq_(&a, &b).unwrap(),
            ctx.neq(&a, &b).unwrap(),
            ctx.ite(&a, &b, &c).unwrap(),
        ] {
            assert_round_trip(&ctx, &ast);
        }
    }

    #[test]
    fn test_round_trip_bv_ops() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let z = ctx.bvs("z", 32).unwrap();

        for ast in [
            ctx.add(&x, &y).unwrap(),
            ctx.sub(&x, &y).unwrap(),
            ctx.mul(&x, &y).unwrap(),
            ctx.udiv(&x, &y).unwrap(),
            ctx.sdiv(&x, &y).unwrap(),
            ctx.urem(&x, &y).unwrap(),
            ctx.srem(&x, &y).unwrap(),
            ctx.neg(&x).unwrap(),
            ctx.shl(&x, &y).unwrap(),
            ctx.lshr(&x, &y).unwrap(),
            ctx.ashr(&x, &y).unwrap(),
            ctx.rotate_left(&x, &y).unwrap(),
            ctx.rotate_right(&x, &y).unwrap(),
            ctx.zero_ext(&x, 32).unwrap(),
            ctx.sign_ext(&x, 32).unwrap(),
            ctx.extract(&x, 7, 0).unwrap(),
            ctx.concat([x.clone(), y.clone(), z.clone()]).unwrap(),
            ctx.byte_reverse(&x).unwrap(),
            ctx.ult(&x, &y).unwrap(),
            ctx.ule(&x, &y).unwrap(),
            ctx.ugt(&x, &y).unwrap(),
            ctx.uge(&x, &y).unwrap(),
            ctx.slt(&x, &y).unwrap(),
            ctx.sle(&x, &y).unwrap(),
            ctx.sgt(&x, &y).unwrap(),
            ctx.sge(&x, &y).unwrap(),
            ctx.union(&x, &y).unwrap(),
            ctx.intersection(&x, &y).unwrap(),
            ctx.widen(&x, &y).unwrap(),
        ] {
            assert_round_trip(&ctx, &ast);
        }
    }

    #[test]
    fn test_round_trip_float_ops() {
        let ctx = Context::new();
        let f = ctx.fps("f", FSort::f64()).unwrap();
        let g = ctx.fps("g", FSort::f64()).unwrap();
        let x = ctx.bvs("x", 64).unwrap();
        let sign = ctx.bvs("s", 1).unwrap();
        let exp = ctx.bvs("e", 11).unwrap();
        let sig = ctx.bvs("m", 53).unwrap();
        let rm = FPRM::NearestTiesToEven;

        for ast in [
            ctx.fp_neg(&f).unwrap(),
            ctx.fp_abs(&f).unwrap(),
            ctx.fp_add(&f, &g, rm).unwrap(),
            ctx.fp_sub(&f, &g, rm).unwrap(),
            ctx.fp_mul(&f, &g, rm).unwrap(),
            ctx.fp_div(&f, &g, rm).unwrap(),
            ctx.fp_sqrt(&f, rm).unwrap(),
            ctx.fp_lt(&f, &g).unwrap(),
            ctx.fp_leq(&f, &g).unwrap(),
            ctx.fp_gt(&f, &g).unwrap(),
            ctx.fp_geq(&f, &g).unwrap(),
            ctx.fp_is_nan(&f).unwrap(),
            ctx.fp_is_inf(&f).unwrap(),
            ctx.fp_to_fp(&f, FSort::f32(), rm).unwrap(),
            ctx.fp_to_ieeebv(&f).unwrap(),
            ctx.fp_to_ubv(&f, 64, rm).unwrap(),
            ctx.fp_to_sbv(&f, 64, rm).unwrap(),
            ctx.bv_to_fp(&x, FSort::f64()).unwrap(),
            ctx.bv_to_fp_signed(&x, FSort::f64(), rm).unwrap(),
            ctx.bv_to_fp_unsigned(&x, FSort::f64(), rm).unwrap(),
            ctx.fp_fp(&sign, &exp, &sig).unwrap(),
        ] {
            assert_round_trip(&ctx, &ast);
        }
    }

    #[test]
    fn test_round_trip_string_ops() {
        let ctx = Context::new();
        let s = ctx.strings("s").unwrap();
        let t = ctx.strings("t").unwrap();
        let u = ctx.strings("u").unwrap();
        let i = ctx.bvs("i", 64).unwrap();
        let j = ctx.bvs("j", 64).unwrap();

        for ast in [
            ctx.str_len(&s).unwrap(),
            ctx.str_concat(&s, &t).unwrap(),
            ctx.str_substr(&s, &i, &j).unwrap(),
            ctx.str_contains(&s, &t).unwrap(),
            ctx.str_prefix_of(&s, &t).unwrap(),
            ctx.str_suffix_of(&s, &t).unwrap(),
            ctx.str_index_of(&s, &t, &i).unwrap(),
            ctx.str_replace(&s, &t, &u).unwrap(),
            ctx.str_is_digit(&s).unwrap(),
            ctx.str_to_bv(&s).unwrap(),
            ctx.bv_to_str(&i).unwrap(),
        ] {
            assert_round_trip(&ctx, &ast);
        }
    }

    #[test]
    fn test_reconstruct_nested_expression() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let a = ctx.bvs("a", 32).unwrap();

        // (x + y) with the whole child list replaced by [a, a]
        let add = ctx.add(&x, &y).unwrap();
        let rebuilt = reconstruct_node(&ctx, &add, &[a.clone(), a.clone()]).unwrap();
        assert_eq!(rebuilt, ctx.add(&a, &a).unwrap());
        // The original is untouched
        assert_eq!(add, ctx.add(&x, &y).unwrap());
    }
}
