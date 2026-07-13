use anyhow::Result;
use clarirs_num::BitVec;

use crate::{
    ast::{
        AstFactory,
        annotation::{Annotation, AnnotationType},
    },
    context::Context,
};

#[test]
fn test_prim() -> Result<()> {
    let ctx = Context::default();
    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;

    assert_eq!(true_ast.simplify()?, true_ast);
    assert_eq!(false_ast.simplify()?, false_ast);
    assert_eq!(sym_ast.simplify()?, sym_ast);

    Ok(())
}

#[test]
fn test_xor_double_negation() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.bools("x")?;
    let y = ctx.bools("y")?;
    let not_x = ctx.not(&x)?;
    let not_y = ctx.not(&y)?;

    // Test: ¬x ⊕ ¬y = x ⊕ y
    let xor_not_not = ctx.xor2(&not_x, &not_y)?.simplify()?;
    let xor_plain = ctx.xor2(&x, &y)?.simplify()?;
    assert_eq!(xor_not_not, xor_plain);

    // Verify with concrete values
    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;

    // ¬T ⊕ ¬T = F ⊕ F = F, and T ⊕ T = F
    let not_true = ctx.not(&true_ast)?;
    let result = ctx.xor2(&not_true, &not_true)?.simplify()?;
    assert_eq!(result, false_ast);

    // ¬T ⊕ ¬F = F ⊕ T = T, and T ⊕ F = T
    let not_false = ctx.not(&false_ast)?;
    let result2 = ctx.xor2(&not_true, &not_false)?.simplify()?;
    assert_eq!(result2, true_ast);

    // ¬F ⊕ ¬T = T ⊕ F = T, and F ⊕ T = T
    let result3 = ctx.xor2(&not_false, &not_true)?.simplify()?;
    assert_eq!(result3, true_ast);

    // ¬F ⊕ ¬F = T ⊕ T = F, and F ⊕ F = F
    let result4 = ctx.xor2(&not_false, &not_false)?.simplify()?;
    assert_eq!(result4, false_ast);

    Ok(())
}

#[test]
fn test_not() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;

    let table = vec![
        (&true_ast, &true_ast, &true_ast),
        (&true_ast, &false_ast, &false_ast),
        (&true_ast, &sym_ast, &sym_ast),
        (&false_ast, &true_ast, &false_ast),
        (&false_ast, &false_ast, &false_ast),
        (&false_ast, &sym_ast, &false_ast),
        (&sym_ast, &true_ast, &sym_ast),
        (&sym_ast, &false_ast, &false_ast),
        (&sym_ast, &sym_ast, &sym_ast),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.and2(lhs, rhs)?.simplify()?,
            expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_or() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;

    let table = vec![
        (&true_ast, &true_ast, &true_ast),
        (&true_ast, &false_ast, &true_ast),
        (&true_ast, &sym_ast, &true_ast),
        (&false_ast, &true_ast, &true_ast),
        (&false_ast, &false_ast, &false_ast),
        (&false_ast, &sym_ast, &sym_ast),
        (&sym_ast, &true_ast, &true_ast),
        (&sym_ast, &false_ast, &sym_ast),
        (&sym_ast, &sym_ast, &sym_ast),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.or2(lhs, rhs)?.simplify()?,
            expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_xor() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;
    let not_sym_ast = ctx.not(&sym_ast)?;

    let table = vec![
        (&true_ast, &true_ast, &false_ast),
        (&true_ast, &false_ast, &true_ast),
        (&true_ast, &sym_ast, &not_sym_ast),
        (&false_ast, &true_ast, &true_ast),
        (&false_ast, &false_ast, &false_ast),
        (&false_ast, &sym_ast, &sym_ast),
        (&sym_ast, &true_ast, &not_sym_ast),
        (&sym_ast, &false_ast, &sym_ast),
        (&sym_ast, &sym_ast, &false_ast),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.xor2(lhs, rhs)?.simplify()?,
            expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_if() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;
    let not_sym_ast = ctx.not(&sym_ast)?;

    let table = vec![
        (&true_ast, &true_ast, &true_ast, &true_ast),
        (&true_ast, &true_ast, &false_ast, &true_ast),
        (&true_ast, &true_ast, &sym_ast, &true_ast),
        (&true_ast, &false_ast, &true_ast, &false_ast),
        (&true_ast, &false_ast, &false_ast, &false_ast),
        (&true_ast, &false_ast, &sym_ast, &false_ast),
        (&true_ast, &sym_ast, &true_ast, &sym_ast),
        (&true_ast, &sym_ast, &false_ast, &sym_ast),
        (&true_ast, &sym_ast, &sym_ast, &sym_ast),
        (&false_ast, &true_ast, &true_ast, &true_ast),
        (&false_ast, &true_ast, &false_ast, &false_ast),
        (&false_ast, &true_ast, &sym_ast, &sym_ast),
        (&false_ast, &false_ast, &true_ast, &true_ast),
        (&false_ast, &false_ast, &false_ast, &false_ast),
        (&false_ast, &false_ast, &sym_ast, &sym_ast),
        (&false_ast, &sym_ast, &true_ast, &true_ast),
        (&false_ast, &sym_ast, &false_ast, &false_ast),
        (&false_ast, &sym_ast, &sym_ast, &sym_ast),
        (&sym_ast, &true_ast, &true_ast, &true_ast),
        (&sym_ast, &true_ast, &false_ast, &sym_ast),
        (&sym_ast, &true_ast, &sym_ast, &sym_ast),
        (&sym_ast, &false_ast, &true_ast, &not_sym_ast),
        (&sym_ast, &false_ast, &false_ast, &false_ast),
        (&sym_ast, &false_ast, &sym_ast, &false_ast),
        (&sym_ast, &sym_ast, &true_ast, &true_ast),
        (&sym_ast, &sym_ast, &false_ast, &sym_ast),
        (&sym_ast, &sym_ast, &sym_ast, &sym_ast),
    ];

    for (cond, then_, else_, expected) in table {
        assert_eq!(
            &ctx.ite(cond, then_, else_)?.simplify()?,
            expected,
            "cond: {cond:?}, then_branch: {then_:?}, else_branch: {else_:?}"
        );
    }

    Ok(())
}

#[test]
fn test_eq() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;
    let not_sym_ast = ctx.not(&sym_ast)?;

    let table = vec![
        (&true_ast, &true_ast, &true_ast),
        (&true_ast, &false_ast, &false_ast),
        (&true_ast, &sym_ast, &sym_ast),
        (&false_ast, &true_ast, &false_ast),
        (&false_ast, &false_ast, &true_ast),
        (&false_ast, &sym_ast, &not_sym_ast),
        (&sym_ast, &true_ast, &sym_ast),
        (&sym_ast, &false_ast, &not_sym_ast),
        // Note: sym == sym does NOT simplify to true (NaN consideration)
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.eq_(lhs, rhs)?.simplify()?,
            expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_neq() -> Result<()> {
    let ctx = Context::new();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;
    let not_sym_ast = ctx.not(&sym_ast)?;

    let table = vec![
        (&true_ast, &true_ast, &false_ast),
        (&true_ast, &false_ast, &true_ast),
        (&true_ast, &sym_ast, &not_sym_ast),
        (&false_ast, &true_ast, &true_ast),
        (&false_ast, &false_ast, &false_ast),
        (&false_ast, &sym_ast, &sym_ast),
        (&sym_ast, &true_ast, &not_sym_ast),
        (&sym_ast, &false_ast, &sym_ast),
        // Note: sym != sym does NOT simplify to false (NaN consideration)
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.neq(lhs, rhs)?.simplify()?,
            expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_ult() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.false_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.ult(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_ule() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.true_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.ule(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_ugt() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.false_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.ugt(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_uge() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.true_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.uge(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_slt() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.false_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.false_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.slt(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_sle() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.false_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.true_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.sle(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_sgt() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.true_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.false_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.sgt(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_sge() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((2, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.true_()?,
        ),
        (
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.false_()?,
        ),
        (
            ctx.bvv(BitVec::from((1, 8)))?,
            ctx.bvv(BitVec::from((255, 8)))?,
            ctx.true_()?,
        ),
        (ctx.bvs("a", 8)?, ctx.bvs("a", 8)?, ctx.true_()?),
    ];

    for (lhs, rhs, expected) in table {
        assert_eq!(
            &ctx.sge(&lhs, &rhs)?.simplify()?,
            &expected,
            "lhs: {lhs:?}, rhs: {rhs:?}"
        );
    }

    Ok(())
}

#[test]
fn test_boolean_identity_simplifications() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.bools("x")?;
    let not_x = ctx.not(&x)?.simplify()?;

    // x && !x == false
    let simplified = ctx.and2(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.false_()?);

    let simplified = ctx.and2(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.false_()?);

    // x || !x == true
    let simplified = ctx.or2(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    let simplified = ctx.or2(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    // x ^ !x == true
    let simplified = ctx.xor2(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    let simplified = ctx.xor2(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    Ok(())
}

#[test]
fn test_booleq_identity_simplification_without_floats() -> Result<()> {
    // BoolEq(x, x) should simplify to true
    let ctx = Context::default();
    let a = ctx.bvs("a", 64)?;
    let b = ctx.bvs("b", 64)?;

    let neq = ctx.neq(&a, &b)?;
    let eq_check = ctx.eq_(&neq, &neq)?;
    let simplified = eq_check.simplify()?;

    assert!(
        matches!(simplified.op(), crate::ast::AstOp::BoolV(true)),
        "BoolEq(x, x) should simplify to true when no floats are involved, got: {:?}",
        simplified.op()
    );
    Ok(())
}

#[test]
fn test_booleq_identity_simplification_with_floats() -> Result<()> {
    // BoolEq(x, x) SHOULD simplify to true even when x involves floats.
    // NaN != NaN applies to fp== itself, but bool== of two identical boolean
    // expressions is always true: whatever value (fp== A B) takes, both sides
    // are the same expression and thus equal.
    let ctx = Context::default();
    let a = ctx.fps("a", clarirs_num::FSort::f64())?;
    let b = ctx.fps("b", clarirs_num::FSort::f64())?;

    let fp_eq = ctx.fp_eq(&a, &b)?;
    let eq_check = ctx.eq_(&fp_eq, &fp_eq)?;
    let simplified = eq_check.simplify()?;

    assert!(
        matches!(simplified.op(), crate::ast::AstOp::BoolV(true)),
        "BoolEq(x, x) should simplify to true even when floats are involved, got: {:?}",
        simplified.op()
    );
    Ok(())
}

#[test]
fn test_relocatable_annotations_preserved_through_simplification() -> Result<()> {
    let ctx = Context::new();

    let annotation = Annotation::new(AnnotationType::Uninitialized, true, true);

    // Create an expression that will be simplified: true && x => x
    let x = ctx.bools("x")?;
    let true_ast = ctx.true_()?;

    // Annotate x with a relocatable+eliminatable annotation
    let annotated_x = ctx.annotate(&x, vec![annotation.clone()])?;
    let expr = ctx.and2(&true_ast, &annotated_x)?;

    let simplified = expr.simplify()?;

    // The annotation should be preserved on the simplified result
    assert!(
        simplified.annotations().contains(&annotation),
        "Relocatable annotation should be preserved through simplification, got annotations: {:?}",
        simplified.annotations()
    );

    Ok(())
}

#[test]
fn test_non_eliminatable_non_relocatable_blocks_simplification() -> Result<()> {
    let ctx = Context::new();

    // SimplificationAvoidance is !eliminatable && !relocatable
    let annotation = Annotation::new(AnnotationType::SimplificationAvoidance, false, false);

    // Create an expression that would normally simplify: true && x => x
    let x = ctx.bools("x")?;
    let true_ast = ctx.true_()?;
    let expr = ctx.and2(&true_ast, &x)?;

    // Annotate the expression with a blocking annotation
    let annotated = ctx.annotate(&expr, vec![annotation])?;

    // Simplification should be blocked — the expression should remain unchanged
    let simplified = annotated.simplify()?;
    assert_eq!(
        simplified, annotated,
        "Non-eliminatable, non-relocatable annotation should block simplification"
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Not rules
// ---------------------------------------------------------------------------

#[test]
fn test_not_double_negation() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bools("x")?;

    // !!x => x
    assert_eq!(ctx.not(&ctx.not(&x)?)?.simplify()?, x);

    // !!!x => !x
    assert_eq!(
        ctx.not(&ctx.not(&ctx.not(&x)?)?)?.simplify()?,
        ctx.not(&x)?
    );

    // Concrete negation
    assert_eq!(ctx.not(&ctx.true_()?)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.not(&ctx.false_()?)?.simplify()?, ctx.true_()?);

    Ok(())
}

#[test]
fn test_not_eq_neq_inversion() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bvs("a", 64)?;
    let b = ctx.bvs("b", 64)?;

    // !(a == b) => a != b
    assert_eq!(ctx.not(&ctx.eq_(&a, &b)?)?.simplify()?, ctx.neq(&a, &b)?);
    // !(a != b) => a == b
    assert_eq!(ctx.not(&ctx.neq(&a, &b)?)?.simplify()?, ctx.eq_(&a, &b)?);

    Ok(())
}

#[test]
fn test_not_unsigned_comparison_inversion() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bvs("a", 64)?;
    let b = ctx.bvs("b", 64)?;

    // !(a > b) => a <= b
    assert_eq!(ctx.not(&ctx.ugt(&a, &b)?)?.simplify()?, ctx.ule(&a, &b)?);
    // !(a >= b) => a < b
    assert_eq!(ctx.not(&ctx.uge(&a, &b)?)?.simplify()?, ctx.ult(&a, &b)?);
    // !(a < b) => a >= b
    assert_eq!(ctx.not(&ctx.ult(&a, &b)?)?.simplify()?, ctx.uge(&a, &b)?);
    // !(a <= b) => a > b
    assert_eq!(ctx.not(&ctx.ule(&a, &b)?)?.simplify()?, ctx.ugt(&a, &b)?);

    Ok(())
}

#[test]
fn test_not_signed_comparison_inversion() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bvs("a", 64)?;
    let b = ctx.bvs("b", 64)?;

    // !(a s> b) => a s<= b
    assert_eq!(ctx.not(&ctx.sgt(&a, &b)?)?.simplify()?, ctx.sle(&a, &b)?);
    // !(a s>= b) => a s< b
    assert_eq!(ctx.not(&ctx.sge(&a, &b)?)?.simplify()?, ctx.slt(&a, &b)?);
    // !(a s< b) => a s>= b
    assert_eq!(ctx.not(&ctx.slt(&a, &b)?)?.simplify()?, ctx.sge(&a, &b)?);
    // !(a s<= b) => a s> b
    assert_eq!(ctx.not(&ctx.sle(&a, &b)?)?.simplify()?, ctx.sgt(&a, &b)?);

    Ok(())
}

// ---------------------------------------------------------------------------
// And rules
// ---------------------------------------------------------------------------

#[test]
fn test_and_flattening() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;
    let c = ctx.bools("c")?;

    // (a & b) & c => a & b & c
    assert_eq!(
        ctx.and2(&ctx.and2(&a, &b)?, &c)?.simplify()?,
        ctx.and(vec![a.clone(), b.clone(), c.clone()])?
    );

    Ok(())
}

#[test]
fn test_and_deduplication() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;

    // a & b & a => a & b
    assert_eq!(
        ctx.and(vec![a.clone(), b.clone(), a.clone()])?.simplify()?,
        ctx.and2(&a, &b)?
    );

    Ok(())
}

#[test]
fn test_and_true_filtering_and_single_arg() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;

    // true & a & b => a & b
    assert_eq!(
        ctx.and(vec![ctx.true_()?, a.clone(), b.clone()])?
            .simplify()?,
        ctx.and2(&a, &b)?
    );

    // And of a single argument => that argument
    assert_eq!(ctx.and(vec![a.clone()])?.simplify()?, a);

    // And of only true arguments => true
    assert_eq!(
        ctx.and(vec![ctx.true_()?, ctx.true_()?])?.simplify()?,
        ctx.true_()?
    );

    Ok(())
}

#[test]
fn test_and_contradictory_comparisons() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let k = ctx.bvv(BitVec::from((42, 8)))?;
    let f = ctx.false_()?;

    // (x == k) & (x != k) => false (both orders)
    assert_eq!(
        ctx.and2(&ctx.eq_(&x, &k)?, &ctx.neq(&x, &k)?)?.simplify()?,
        f
    );
    assert_eq!(
        ctx.and2(&ctx.neq(&x, &k)?, &ctx.eq_(&x, &k)?)?.simplify()?,
        f
    );

    // (x < k) & (x >= k) => false
    assert_eq!(
        ctx.and2(&ctx.ult(&x, &k)?, &ctx.uge(&x, &k)?)?.simplify()?,
        f
    );
    // (x <= k) & (x > k) => false
    assert_eq!(
        ctx.and2(&ctx.ule(&x, &k)?, &ctx.ugt(&x, &k)?)?.simplify()?,
        f
    );
    // (x s< k) & (x s>= k) => false
    assert_eq!(
        ctx.and2(&ctx.slt(&x, &k)?, &ctx.sge(&x, &k)?)?.simplify()?,
        f
    );
    // (x s<= k) & (x s> k) => false
    assert_eq!(
        ctx.and2(&ctx.sle(&x, &k)?, &ctx.sgt(&x, &k)?)?.simplify()?,
        f
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Or rules
// ---------------------------------------------------------------------------

#[test]
fn test_or_flattening() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;
    let c = ctx.bools("c")?;

    // (a | b) | c => a | b | c
    assert_eq!(
        ctx.or2(&ctx.or2(&a, &b)?, &c)?.simplify()?,
        ctx.or(vec![a.clone(), b.clone(), c.clone()])?
    );

    Ok(())
}

#[test]
fn test_or_deduplication() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;

    // a | b | a => a | b
    assert_eq!(
        ctx.or(vec![a.clone(), b.clone(), a.clone()])?.simplify()?,
        ctx.or2(&a, &b)?
    );

    Ok(())
}

#[test]
fn test_or_false_filtering_and_single_arg() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bools("a")?;
    let b = ctx.bools("b")?;

    // false | a | b => a | b
    assert_eq!(
        ctx.or(vec![ctx.false_()?, a.clone(), b.clone()])?
            .simplify()?,
        ctx.or2(&a, &b)?
    );

    // Or of a single argument => that argument
    assert_eq!(ctx.or(vec![a.clone()])?.simplify()?, a);

    // Or of only false arguments => false
    assert_eq!(
        ctx.or(vec![ctx.false_()?, ctx.false_()?])?.simplify()?,
        ctx.false_()?
    );

    Ok(())
}

#[test]
fn test_or_tautological_comparisons() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let k = ctx.bvv(BitVec::from((42, 8)))?;
    let t = ctx.true_()?;

    // (x == k) | (x != k) => true (both orders)
    assert_eq!(
        ctx.or2(&ctx.eq_(&x, &k)?, &ctx.neq(&x, &k)?)?.simplify()?,
        t
    );
    assert_eq!(
        ctx.or2(&ctx.neq(&x, &k)?, &ctx.eq_(&x, &k)?)?.simplify()?,
        t
    );

    // (x < k) | (x >= k) => true
    assert_eq!(
        ctx.or2(&ctx.ult(&x, &k)?, &ctx.uge(&x, &k)?)?.simplify()?,
        t
    );
    // (x <= k) | (x > k) => true
    assert_eq!(
        ctx.or2(&ctx.ule(&x, &k)?, &ctx.ugt(&x, &k)?)?.simplify()?,
        t
    );
    // (x s< k) | (x s>= k) => true
    assert_eq!(
        ctx.or2(&ctx.slt(&x, &k)?, &ctx.sge(&x, &k)?)?.simplify()?,
        t
    );
    // (x s<= k) | (x s> k) => true
    assert_eq!(
        ctx.or2(&ctx.sle(&x, &k)?, &ctx.sgt(&x, &k)?)?.simplify()?,
        t
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Xor rules
// ---------------------------------------------------------------------------

#[test]
fn test_xor_multiway_cancellation() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bools("x")?;
    let y = ctx.bools("y")?;

    // x ^ y ^ x => y
    assert_eq!(
        ctx.xor(vec![x.clone(), y.clone(), x.clone()])?.simplify()?,
        y
    );

    // x ^ x ^ x => x (odd count survives)
    assert_eq!(
        ctx.xor(vec![x.clone(), x.clone(), x.clone()])?.simplify()?,
        x
    );

    // x ^ y ^ x ^ y => false
    assert_eq!(
        ctx.xor(vec![x.clone(), y.clone(), x.clone(), y.clone()])?
            .simplify()?,
        ctx.false_()?
    );

    Ok(())
}

#[test]
fn test_xor_parity_negation() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bools("x")?;
    let y = ctx.bools("y")?;

    // x ^ y ^ true => !(x ^ y)
    assert_eq!(
        ctx.xor(vec![x.clone(), y.clone(), ctx.true_()?])?
            .simplify()?,
        ctx.not(&ctx.xor2(&x, &y)?)?
    );

    // !x ^ y => !(x ^ y) (negation stripped into parity)
    assert_eq!(
        ctx.xor2(&ctx.not(&x)?, &y)?.simplify()?,
        ctx.not(&ctx.xor2(&x, &y)?)?
    );

    // x ^ true ^ true => x (two constants cancel)
    assert_eq!(
        ctx.xor(vec![x.clone(), ctx.true_()?, ctx.true_()?])?
            .simplify()?,
        x
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Eq / Neq rules per sort
// ---------------------------------------------------------------------------

#[test]
fn test_eq_neq_float_concrete() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.eq_(&ctx.fpv(1.0f64)?, &ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.eq_(&ctx.fpv(1.0f64)?, &ctx.fpv(2.0f64)?)?.simplify()?,
        ctx.false_()?
    );
    // NaN != NaN under fp.eq semantics
    assert_eq!(
        ctx.eq_(&ctx.fpv(f64::NAN)?, &ctx.fpv(f64::NAN)?)?
            .simplify()?,
        ctx.false_()?
    );
    // compare_fp distinguishes +0.0 from -0.0
    assert_eq!(
        ctx.eq_(&ctx.fpv(0.0f64)?, &ctx.fpv(-0.0f64)?)?.simplify()?,
        ctx.false_()?
    );
    assert_eq!(
        ctx.neq(&ctx.fpv(1.0f64)?, &ctx.fpv(2.0f64)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.neq(&ctx.fpv(f64::NAN)?, &ctx.fpv(f64::NAN)?)?
            .simplify()?,
        ctx.true_()?
    );

    // Symbolic float Eq/Neq lower to FpEq/FpNeq
    let fa = ctx.fps("fa", clarirs_num::FSort::f64())?;
    let fb = ctx.fps("fb", clarirs_num::FSort::f64())?;
    assert_eq!(ctx.eq_(&fa, &fb)?.simplify()?, ctx.fp_eq(&fa, &fb)?);
    assert_eq!(ctx.neq(&fa, &fb)?.simplify()?, ctx.fp_neq(&fa, &fb)?);

    Ok(())
}

#[test]
fn test_eq_neq_string() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.eq_(&ctx.stringv("abc")?, &ctx.stringv("abc")?)?
            .simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.eq_(&ctx.stringv("abc")?, &ctx.stringv("abd")?)?
            .simplify()?,
        ctx.false_()?
    );
    assert_eq!(
        ctx.neq(&ctx.stringv("abc")?, &ctx.stringv("abd")?)?
            .simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.neq(&ctx.stringv("abc")?, &ctx.stringv("abc")?)?
            .simplify()?,
        ctx.false_()?
    );

    // Symbolic string Eq/Neq lower to StrEq/StrNeq
    let s = ctx.strings("s")?;
    let v = ctx.stringv("abc")?;
    assert_eq!(ctx.eq_(&s, &v)?.simplify()?, ctx.str_eq(&s, &v)?);
    assert_eq!(ctx.neq(&s, &v)?.simplify()?, ctx.str_neq(&s, &v)?);

    Ok(())
}

#[test]
fn test_eq_neq_bv_basic() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let one = ctx.bvv(BitVec::from((1, 8)))?;
    let two = ctx.bvv(BitVec::from((2, 8)))?;

    // Structural identity
    assert_eq!(ctx.eq_(&x, &x)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.neq(&x, &x)?.simplify()?, ctx.false_()?);

    // Concrete folds
    assert_eq!(ctx.eq_(&one, &one)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.eq_(&one, &two)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.neq(&one, &two)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.neq(&one, &one)?.simplify()?, ctx.false_()?);

    Ok(())
}

#[test]
fn test_eq_neq_with_mask_and() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;

    // (x & 0x00FF) == 0x12 => extract(x, 7, 0) == 0x12
    let masked_low = ctx.and2(&x, &ctx.bvv(BitVec::from((0x00FF, 16)))?)?;
    assert_eq!(
        ctx.eq_(&masked_low, &ctx.bvv(BitVec::from((0x12, 16)))?)?
            .simplify()?,
        ctx.eq_(
            &ctx.extract(&x, 7, 0)?,
            &ctx.bvv(BitVec::from((0x12, 8)))?
        )?
    );

    // (x & 0x0FF0) == 0x0120 => extract(x, 11, 4) == 0x12
    let masked_mid = ctx.and2(&x, &ctx.bvv(BitVec::from((0x0FF0, 16)))?)?;
    assert_eq!(
        ctx.eq_(&masked_mid, &ctx.bvv(BitVec::from((0x0120, 16)))?)?
            .simplify()?,
        ctx.eq_(
            &ctx.extract(&x, 11, 4)?,
            &ctx.bvv(BitVec::from((0x12, 8)))?
        )?
    );

    // (x & 0x00FF) != 0x12 => extract(x, 7, 0) != 0x12
    assert_eq!(
        ctx.neq(&masked_low, &ctx.bvv(BitVec::from((0x12, 16)))?)?
            .simplify()?,
        ctx.neq(
            &ctx.extract(&x, 7, 0)?,
            &ctx.bvv(BitVec::from((0x12, 8)))?
        )?
    );

    Ok(())
}

#[test]
fn test_eq_neq_zero_ext() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let ze_x = ctx.zero_ext(&x, 8)?;
    let ze_y = ctx.zero_ext(&y, 8)?;
    let v16 = ctx.bvv(BitVec::from((0x12, 16)))?;
    let v8 = ctx.bvv(BitVec::from((0x12, 8)))?;

    // ZeroExt(x) == small constant => x == truncated constant (both orders)
    assert_eq!(ctx.eq_(&ze_x, &v16)?.simplify()?, ctx.eq_(&x, &v8)?);
    assert_eq!(ctx.eq_(&v16, &ze_x)?.simplify()?, ctx.eq_(&x, &v8)?);

    // ZeroExt(x) == ZeroExt(y) => x == y
    assert_eq!(ctx.eq_(&ze_x, &ze_y)?.simplify()?, ctx.eq_(&x, &y)?);

    // Same rules for Neq
    assert_eq!(ctx.neq(&ze_x, &v16)?.simplify()?, ctx.neq(&x, &v8)?);
    assert_eq!(ctx.neq(&v16, &ze_x)?.simplify()?, ctx.neq(&x, &v8)?);
    assert_eq!(ctx.neq(&ze_x, &ze_y)?.simplify()?, ctx.neq(&x, &y)?);

    Ok(())
}

#[test]
fn test_eq_neq_ite_bit() -> Result<()> {
    let ctx = Context::new();
    let c = ctx.bools("c")?;
    let one = ctx.bvv(BitVec::from((1, 8)))?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;
    let ite10 = ctx.ite(&c, &one, &zero)?;
    let ite01 = ctx.ite(&c, &zero, &one)?;

    // (ite c 1 0) == 0 => !c
    assert_eq!(ctx.eq_(&ite10, &zero)?.simplify()?, ctx.not(&c)?);
    // (ite c 1 0) == 1 => c
    assert_eq!(ctx.eq_(&ite10, &one)?.simplify()?, c);
    // (ite c 0 1) == 0 => c
    assert_eq!(ctx.eq_(&ite01, &zero)?.simplify()?, c);
    // (ite c 0 1) == 1 => !c
    assert_eq!(ctx.eq_(&ite01, &one)?.simplify()?, ctx.not(&c)?);
    // Constant on the left works too
    assert_eq!(ctx.eq_(&zero, &ite10)?.simplify()?, ctx.not(&c)?);

    // (ite c 1 0) != 0 => c
    assert_eq!(ctx.neq(&ite10, &zero)?.simplify()?, c);
    // (ite c 1 0) != 1 => !c
    assert_eq!(ctx.neq(&ite10, &one)?.simplify()?, ctx.not(&c)?);
    // (ite c 0 1) != 0 => !c
    assert_eq!(ctx.neq(&ite01, &zero)?.simplify()?, ctx.not(&c)?);
    // (ite c 0 1) != 1 => c
    assert_eq!(ctx.neq(&ite01, &one)?.simplify()?, c);

    Ok(())
}

#[test]
fn test_eq_neq_sub_add_against_zero() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;

    // (x - 5) == 0 => x == 5 (both orders)
    assert_eq!(
        ctx.eq_(&ctx.sub(&x, &five)?, &zero)?.simplify()?,
        ctx.eq_(&x, &five)?
    );
    assert_eq!(
        ctx.eq_(&zero, &ctx.sub(&x, &five)?)?.simplify()?,
        ctx.eq_(&x, &five)?
    );
    // (x - 5) != 0 => x != 5
    assert_eq!(
        ctx.neq(&ctx.sub(&x, &five)?, &zero)?.simplify()?,
        ctx.neq(&x, &five)?
    );

    // (x + 5) == 0 => x == -5 (251 in 8 bits)
    let neg_five = ctx.bvv(BitVec::from((251, 8)))?;
    assert_eq!(
        ctx.eq_(&ctx.add(&x, &five)?, &zero)?.simplify()?,
        ctx.eq_(&x, &neg_five)?
    );
    // (x + 5) != 0 => x != -5
    assert_eq!(
        ctx.neq(&ctx.add(&x, &five)?, &zero)?.simplify()?,
        ctx.neq(&x, &neg_five)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Unsigned comparison structural rules
// ---------------------------------------------------------------------------

#[test]
fn test_unsigned_comparison_with_mask_and() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;
    let masked = ctx.and2(&x, &ctx.bvv(BitVec::from((0x00FF, 16)))?)?;
    let k16 = ctx.bvv(BitVec::from((5, 16)))?;
    let k8 = ctx.bvv(BitVec::from((5, 8)))?;
    let ex = ctx.extract(&x, 7, 0)?;

    assert_eq!(ctx.ult(&masked, &k16)?.simplify()?, ctx.ult(&ex, &k8)?);
    assert_eq!(ctx.ult(&k16, &masked)?.simplify()?, ctx.ult(&k8, &ex)?);
    assert_eq!(ctx.ule(&masked, &k16)?.simplify()?, ctx.ule(&ex, &k8)?);
    assert_eq!(ctx.ule(&k16, &masked)?.simplify()?, ctx.ule(&k8, &ex)?);
    assert_eq!(ctx.ugt(&masked, &k16)?.simplify()?, ctx.ugt(&ex, &k8)?);
    assert_eq!(ctx.ugt(&k16, &masked)?.simplify()?, ctx.ugt(&k8, &ex)?);
    assert_eq!(ctx.uge(&masked, &k16)?.simplify()?, ctx.uge(&ex, &k8)?);
    assert_eq!(ctx.uge(&k16, &masked)?.simplify()?, ctx.uge(&k8, &ex)?);

    Ok(())
}

#[test]
fn test_unsigned_comparison_zero_ext() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let ze_x = ctx.zero_ext(&x, 8)?;
    let ze_y = ctx.zero_ext(&y, 8)?;
    let k16 = ctx.bvv(BitVec::from((5, 16)))?;
    let k8 = ctx.bvv(BitVec::from((5, 8)))?;

    // ZeroExt(x) vs small constant => inner comparison
    assert_eq!(ctx.ult(&ze_x, &k16)?.simplify()?, ctx.ult(&x, &k8)?);
    assert_eq!(ctx.ult(&k16, &ze_x)?.simplify()?, ctx.ult(&k8, &x)?);
    assert_eq!(ctx.ule(&ze_x, &k16)?.simplify()?, ctx.ule(&x, &k8)?);
    assert_eq!(ctx.ugt(&ze_x, &k16)?.simplify()?, ctx.ugt(&x, &k8)?);
    assert_eq!(ctx.uge(&ze_x, &k16)?.simplify()?, ctx.uge(&x, &k8)?);
    assert_eq!(ctx.uge(&k16, &ze_x)?.simplify()?, ctx.uge(&k8, &x)?);

    // ZeroExt vs ZeroExt => inner comparison
    assert_eq!(ctx.ult(&ze_x, &ze_y)?.simplify()?, ctx.ult(&x, &y)?);
    assert_eq!(ctx.ule(&ze_x, &ze_y)?.simplify()?, ctx.ule(&x, &y)?);
    assert_eq!(ctx.ugt(&ze_x, &ze_y)?.simplify()?, ctx.ugt(&x, &y)?);
    assert_eq!(ctx.uge(&ze_x, &ze_y)?.simplify()?, ctx.uge(&x, &y)?);

    Ok(())
}

#[test]
fn test_ule_ugt_zero_ext_large_constant() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze_x = ctx.zero_ext(&x, 8)?;
    // 0x100 does not fit in the 8 inner bits
    let big = ctx.bvv(BitVec::from((0x100, 16)))?;

    // ZeroExt(x) <= 0x100 is always true
    assert_eq!(ctx.ule(&ze_x, &big)?.simplify()?, ctx.true_()?);
    // 0x100 <= ZeroExt(x) is always false
    assert_eq!(ctx.ule(&big, &ze_x)?.simplify()?, ctx.false_()?);
    // ZeroExt(x) > 0x100 is always false
    assert_eq!(ctx.ugt(&ze_x, &big)?.simplify()?, ctx.false_()?);
    // 0x100 > ZeroExt(x) is always true
    assert_eq!(ctx.ugt(&big, &ze_x)?.simplify()?, ctx.true_()?);

    // ULT has no such concretization rule; the expression is unchanged
    assert_eq!(ctx.ult(&ze_x, &big)?.simplify()?, ctx.ult(&ze_x, &big)?);

    Ok(())
}

#[test]
fn test_unsigned_comparison_concat_trailing_zeros() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let cc = ctx.concat2(&x, &ctx.bvv(BitVec::from((0, 8)))?)?;
    let k = ctx.bvv(BitVec::from((0x1200, 16)))?;
    let k_hi = ctx.bvv(BitVec::from((0x12, 8)))?;

    // Concat(x, 0x00) cmp 0x1200 => x cmp 0x12
    assert_eq!(ctx.ult(&cc, &k)?.simplify()?, ctx.ult(&x, &k_hi)?);
    assert_eq!(ctx.ult(&k, &cc)?.simplify()?, ctx.ult(&k_hi, &x)?);
    assert_eq!(ctx.ule(&cc, &k)?.simplify()?, ctx.ule(&x, &k_hi)?);
    assert_eq!(ctx.ugt(&cc, &k)?.simplify()?, ctx.ugt(&x, &k_hi)?);
    assert_eq!(ctx.uge(&cc, &k)?.simplify()?, ctx.uge(&x, &k_hi)?);

    // If the constant's low bits are not zero, no rewrite happens
    let k_odd = ctx.bvv(BitVec::from((0x1201, 16)))?;
    assert_eq!(ctx.ult(&cc, &k_odd)?.simplify()?, ctx.ult(&cc, &k_odd)?);

    Ok(())
}

#[test]
fn test_unsigned_comparison_sub_zero_ext_bound() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze = ctx.zero_ext(&x, 8)?;
    let c16 = ctx.bvv(BitVec::from((3, 16)))?;
    let b16 = ctx.bvv(BitVec::from((5, 16)))?;
    let sub16 = ctx.sub(&ze, &c16)?;

    let b8 = ctx.bvv(BitVec::from((5, 8)))?;
    let sub8 = ctx.sub(&x, &ctx.bvv(BitVec::from((3, 8)))?)?;

    // cmp(b, ZeroExt(x) - c) and cmp(ZeroExt(x) - c, b) narrow to the inner width
    assert_eq!(ctx.ult(&b16, &sub16)?.simplify()?, ctx.ult(&b8, &sub8)?);
    assert_eq!(ctx.ult(&sub16, &b16)?.simplify()?, ctx.ult(&sub8, &b8)?);
    assert_eq!(ctx.ule(&sub16, &b16)?.simplify()?, ctx.ule(&sub8, &b8)?);
    assert_eq!(ctx.ugt(&sub16, &b16)?.simplify()?, ctx.ugt(&sub8, &b8)?);
    assert_eq!(ctx.uge(&b16, &sub16)?.simplify()?, ctx.uge(&b8, &sub8)?);
    assert_eq!(ctx.uge(&sub16, &b16)?.simplify()?, ctx.uge(&sub8, &b8)?);

    Ok(())
}

#[test]
fn test_unsigned_comparison_add_zero_ext_bound() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze = ctx.zero_ext(&x, 8)?;
    let c16 = ctx.bvv(BitVec::from((3, 16)))?;
    let b16 = ctx.bvv(BitVec::from((5, 16)))?;
    let add16 = ctx.add(&ze, &c16)?;

    let b8 = ctx.bvv(BitVec::from((5, 8)))?;
    let add8 = ctx.add(&x, &ctx.bvv(BitVec::from((3, 8)))?)?;

    // cmp involving ZeroExt(x) + c narrows to the inner width
    assert_eq!(ctx.ult(&b16, &add16)?.simplify()?, ctx.ult(&b8, &add8)?);
    assert_eq!(ctx.ule(&add16, &b16)?.simplify()?, ctx.ule(&add8, &b8)?);
    assert_eq!(ctx.ugt(&add16, &b16)?.simplify()?, ctx.ugt(&add8, &b8)?);
    assert_eq!(ctx.uge(&b16, &add16)?.simplify()?, ctx.uge(&b8, &add8)?);

    Ok(())
}

// ---------------------------------------------------------------------------
// Float predicates
// ---------------------------------------------------------------------------

#[test]
fn test_fp_comparison_concrete() -> Result<()> {
    let ctx = Context::new();
    let one = ctx.fpv(1.0f64)?;
    let two = ctx.fpv(2.0f64)?;

    assert_eq!(ctx.fp_lt(&one, &two)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.fp_lt(&two, &one)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.fp_leq(&one, &one)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.fp_leq(&two, &one)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.fp_gt(&two, &one)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.fp_gt(&one, &two)?.simplify()?, ctx.false_()?);
    assert_eq!(ctx.fp_geq(&one, &one)?.simplify()?, ctx.true_()?);
    assert_eq!(ctx.fp_geq(&one, &two)?.simplify()?, ctx.false_()?);

    Ok(())
}

#[test]
fn test_fp_is_nan_is_inf_concrete() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.fp_is_nan(&ctx.fpv(f64::NAN)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_nan(&ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.false_()?
    );
    assert_eq!(
        ctx.fp_is_inf(&ctx.fpv(f64::INFINITY)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_inf(&ctx.fpv(f64::NEG_INFINITY)?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.fp_is_inf(&ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.false_()?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// String predicates (boolean-valued ops that live in bool.rs)
// ---------------------------------------------------------------------------

#[test]
fn test_str_predicates_concrete() -> Result<()> {
    let ctx = Context::new();
    let hello = ctx.stringv("hello")?;

    // StrContains(input, needle)
    assert_eq!(
        ctx.str_contains(&hello, &ctx.stringv("ell")?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.str_contains(&hello, &ctx.stringv("xyz")?)?.simplify()?,
        ctx.false_()?
    );

    // StrPrefixOf(prefix, input)
    assert_eq!(
        ctx.str_prefix_of(&ctx.stringv("he")?, &hello)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.str_prefix_of(&ctx.stringv("lo")?, &hello)?.simplify()?,
        ctx.false_()?
    );

    // StrSuffixOf(suffix, input)
    assert_eq!(
        ctx.str_suffix_of(&ctx.stringv("lo")?, &hello)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.str_suffix_of(&ctx.stringv("he")?, &hello)?.simplify()?,
        ctx.false_()?
    );

    // StrIsDigit
    assert_eq!(
        ctx.str_is_digit(&ctx.stringv("123")?)?.simplify()?,
        ctx.true_()?
    );
    assert_eq!(
        ctx.str_is_digit(&ctx.stringv("12a")?)?.simplify()?,
        ctx.false_()?
    );
    // Empty string is not a digit string
    assert_eq!(
        ctx.str_is_digit(&ctx.stringv("")?)?.simplify()?,
        ctx.false_()?
    );

    Ok(())
}

#[test]
fn test_eliminatable_non_relocatable_does_not_block_simplification() -> Result<()> {
    let ctx = Context::new();

    // An eliminatable, non-relocatable annotation should NOT block simplification
    let annotation = Annotation::new(AnnotationType::Uninitialized, true, false);

    // Create an expression that would normally simplify: true && x => x
    let x = ctx.bools("x")?;
    let true_ast = ctx.true_()?;
    let expr = ctx.and2(&true_ast, &x)?;

    // Annotate the expression
    let annotated = ctx.annotate(&expr, vec![annotation])?;

    // Simplification should proceed since the annotation is eliminatable
    let simplified = annotated.simplify()?;

    // The result should be simplified (x, not the original and-expression)
    // The non-relocatable annotation is dropped since it can't move to the new expression
    assert_eq!(
        simplified.annotations().len(),
        0,
        "Non-relocatable annotation should be dropped after simplification"
    );

    Ok(())
}
