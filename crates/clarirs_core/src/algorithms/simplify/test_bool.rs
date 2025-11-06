use anyhow::Result;

use crate::{algorithms::Simplify, ast::AstFactory, context::Context};

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
    let xor_not_not = ctx.xor(&not_x, &not_y)?.simplify()?;
    let xor_plain = ctx.xor(&x, &y)?.simplify()?;
    assert_eq!(xor_not_not, xor_plain);

    // Verify with concrete values
    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;

    // ¬T ⊕ ¬T = F ⊕ F = F, and T ⊕ T = F
    let not_true = ctx.not(&true_ast)?;
    let result = ctx.xor(&not_true, &not_true)?.simplify()?;
    assert_eq!(result, false_ast);

    // ¬T ⊕ ¬F = F ⊕ T = T, and T ⊕ F = T
    let not_false = ctx.not(&false_ast)?;
    let result2 = ctx.xor(&not_true, &not_false)?.simplify()?;
    assert_eq!(result2, true_ast);

    // ¬F ⊕ ¬T = T ⊕ F = T, and F ⊕ T = T
    let result3 = ctx.xor(&not_false, &not_true)?.simplify()?;
    assert_eq!(result3, true_ast);

    // ¬F ⊕ ¬F = T ⊕ T = F, and F ⊕ F = F
    let result4 = ctx.xor(&not_false, &not_false)?.simplify()?;
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
            &ctx.and(lhs, rhs)?.simplify()?,
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
            &ctx.or(lhs, rhs)?.simplify()?,
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
            &ctx.xor(lhs, rhs)?.simplify()?,
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
            &ctx.if_(cond, then_, else_)?.simplify()?,
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
        (&sym_ast, &sym_ast, &true_ast),
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
        (&sym_ast, &sym_ast, &false_ast),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.true_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.true_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.false_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.false_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.true_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(255u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(255u8)?, ctx.false_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.true_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(255u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(255u8)?, ctx.false_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.false_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(255u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(255u8)?, ctx.true_()?),
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
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(2u8)?, ctx.false_()?),
        (ctx.bvv_prim(2u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(1u8)?, ctx.true_()?),
        (ctx.bvv_prim(255u8)?, ctx.bvv_prim(1u8)?, ctx.false_()?),
        (ctx.bvv_prim(1u8)?, ctx.bvv_prim(255u8)?, ctx.true_()?),
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
    let simplified = ctx.and(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.false_()?);

    let simplified = ctx.and(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.false_()?);

    // x || !x == true
    let simplified = ctx.or(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    let simplified = ctx.or(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    // x ^ !x == true
    let simplified = ctx.xor(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    let simplified = ctx.xor(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, ctx.true_()?);

    Ok(())
}
