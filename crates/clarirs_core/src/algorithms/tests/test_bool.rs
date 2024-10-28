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
fn test_not() -> Result<()> {
    let ctx = Context::default();

    let true_ast = ctx.true_()?;
    let false_ast = ctx.false_()?;
    let sym_ast = ctx.bools("test")?;
    let not_sym_ast = ctx.not(&sym_ast)?;

    let table = vec![
        (&true_ast, &false_ast),
        (&false_ast, &true_ast),
        (&sym_ast, &not_sym_ast),
    ];

    for (ast, expected) in table {
        assert_eq!(&ctx.not(ast)?.simplify()?, expected, "ast: {:?}", ast);
    }

    Ok(())
}

#[test]
fn test_and() -> Result<()> {
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "cond: {:?}, then_branch: {:?}, else_branch: {:?}",
            cond,
            then_,
            else_
        );
    }

    Ok(())
}

// #[test]
// fn test_eq() -> Result<()> {
//     let ctx = Context::new();

//     let true_ast = ctx.true_()?;
//     let false_ast = ctx.false_()?;
//     let sym_ast = ctx.bools("test")?;
//     let not_sym_ast = ctx.not(&sym_ast)?;

//     let table = vec![
//         (&true_ast, &true_ast, &true_ast),
//         (&true_ast, &false_ast, &false_ast),
//         (&true_ast, &sym_ast, &sym_ast),
//         (&false_ast, &true_ast, &false_ast),
//         (&false_ast, &false_ast, &true_ast),
//         (&false_ast, &sym_ast, &not_sym_ast),
//         (&sym_ast, &true_ast, &sym_ast),
//         (&sym_ast, &false_ast, &not_sym_ast),
//         (&sym_ast, &sym_ast, &true_ast),
//     ];

//     for (lhs, rhs, expected) in table {
//         assert_eq!(
//             &ctx.eq_(lhs, rhs)?.simplify()?,
//             expected,
//             "lhs: {:?}, rhs: {:?}",
//             lhs,
//             rhs
//         );
//     }

//     Ok(())
// }

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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
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
            "lhs: {:?}, rhs: {:?}",
            lhs,
            rhs
        );
    }

    Ok(())
}
