use crate::prelude::*;
use anyhow::Result;

#[test]
fn test_add() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 1),
        (1, 0, 1),
        (1, 1, 2),
        (1, 2, 3),
        (2, 1, 3),
        (2, 2, 4),
        (2, 3, 5),
        (3, 2, 5),
        (3, 3, 6),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.add(&a, &b)?;
        let simplified = result.simplify()?;

        assert_eq!(simplified, expected);
    }

    Ok(())
}

#[test]
fn test_sub() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, u64::MAX),
        (1, 0, 1),
        (1, 1, 0),
        (1, 2, u64::MAX),
        (2, 1, 1),
        (2, 2, 0),
        (2, 3, u64::MAX),
        (3, 2, 1),
        (3, 3, 0),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.sub(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_mul() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 0),
        (1, 1, 1),
        (1, 2, 2),
        (2, 1, 2),
        (2, 2, 4),
        (2, 3, 6),
        (3, 2, 6),
        (3, 3, 9),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.mul(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_udiv() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u8, u8, u8)> = vec![
        (0, 1, 0),
        // (1, 1, 1),
        // (1, 2, 0),
        // (2, 1, 2),
        // (2, 2, 1),
        // (2, 3, 0),
        // (3, 2, 1),
        // (3, 3, 1),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.udiv(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_sdiv() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 1, 0),
        (1, 1, 1),
        (1, 2, 0),
        (2, 1, 2),
        (2, 2, 1),
        (2, 3, 0),
        (3, 2, 1),
        (3, 3, 1),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.sdiv(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_urem() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 1, 0),
        (1, 1, 0),
        (1, 2, 1),
        (2, 1, 0),
        (2, 2, 0),
        (2, 3, 2),
        (3, 2, 1),
        (3, 3, 0),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.urem(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_srem() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 1, 0),
        (1, 1, 0),
        (1, 2, 1),
        (2, 1, 0),
        (2, 2, 0),
        (2, 3, 2),
        (3, 2, 1),
        (3, 3, 0),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.srem(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_pow() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 1),
        (0, 1, 0),
        (1, 0, 1),
        (1, 1, 1),
        (1, 2, 1),
        (2, 1, 2),
        (2, 2, 4),
        (2, 3, 8),
        (3, 2, 9),
        (3, 3, 27),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.pow(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_and() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 0),
        (1, 1, 1),
        (1, 2, 0),
        (2, 1, 0),
        (2, 2, 2),
        (2, 3, 2),
        (3, 2, 2),
        (3, 3, 3),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.and(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_or() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 1),
        (1, 0, 1),
        (1, 1, 1),
        (1, 2, 3),
        (2, 1, 3),
        (2, 2, 2),
        (2, 3, 3),
        (3, 2, 3),
        (3, 3, 3),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.or(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_xor() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 1),
        (1, 0, 1),
        (1, 1, 0),
        (1, 2, 3),
        (2, 1, 3),
        (2, 2, 0),
        (2, 3, 1),
        (3, 2, 1),
        (3, 3, 0),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.xor(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_not() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64)> = vec![
        (0, u64::MAX),
        (1, u64::MAX - 1),
        (2, u64::MAX - 2),
        (3, u64::MAX - 3),
        (4, u64::MAX - 4),
        (5, u64::MAX - 5),
        (6, u64::MAX - 6),
        (7, u64::MAX - 7),
        (8, u64::MAX - 8),
        (9, u64::MAX - 9),
    ];

    for (a, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.not(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

// #[test]
// fn test_shl() -> Result<()> {
//     let ctx = Context::new();

//     let table: Vec<(u64, u64, u64)> = vec![
//         (0, 0, 0),
//         (0, 1, 0),
//         (1, 0, 1),
//         (1, 1, 2),
//         (1, 2, 4),
//         (2, 1, 4),
//         (2, 2, 8),
//         (2, 3, 16),
//         (3, 2, 12),
//         (3, 3, 24),
//         (u64::MAX, 1, u64::MAX),
//         (u64::MAX, 2, u64::MAX),
//     ];

//     for (a, b, expected) in table {
//         let a = ctx.bvv_prim(a).unwrap();
//         let b = ctx.bvv_prim(b).unwrap();
//         let expected = ctx.bvv_prim(expected).unwrap();

//         let result = ctx.shl(&a, &b)?.simplify()?;
//         assert_eq!(result, expected);
//     }

//     Ok(())
// }

#[test]
fn test_lshr() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 1),
        (1, 1, 0),
        (1, 2, 0),
        (2, 1, 1),
        (2, 2, 0),
        (2, 3, 0),
        (3, 2, 0),
        (3, 3, 0),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.lshr(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_ashr() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 1),
        (1, 1, 0),
        (1, 2, 0),
        (2, 1, 1),
        (2, 2, 0),
        (2, 3, 0),
        (3, 2, 0),
        (3, 3, 0),
        (u64::MAX, 1, u64::MAX),
        (u64::MAX, 2, u64::MAX),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim(a).unwrap();
        let b = ctx.bvv_prim(b).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.ashr(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_concat() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u8, u8, u8)> = vec![
        (0, 0, 0),
        (0b0000, 0b0001, 0b00010000),
        (0b0001, 0b0000, 0b00000001),
        (0b0001, 0b0001, 0b00010001),
        (0b0001, 0b0010, 0b00100001),
        (0b0010, 0b0001, 0b00010010),
        (0b0010, 0b0010, 0b00100010),
        (0b0010, 0b0011, 0b00110010),
        (0b0011, 0b0010, 0b00100011),
        (0b0011, 0b0011, 0b00110011),
        (0b1111, 0b0000, 0b00001111),
        (0b0000, 0b1111, 0b11110000),
        (0b1111, 0b1111, 0b11111111),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv_prim_with_size(a, 4).unwrap();
        let b = ctx.bvv_prim_with_size(b, 4).unwrap();
        let expected = ctx.bvv_prim_with_size(expected, 8).unwrap();

        let result = ctx.concat(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_extract() -> Result<()> {
    let _ctx = Context::new();

    todo!();
}

#[test]
fn test_zext() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv_prim_with_size(0u8, 4)?,
            0,
            ctx.bvv_prim_with_size(0u8, 4)?,
        ),
        (
            ctx.bvv_prim_with_size(0u8, 4)?,
            1,
            ctx.bvv_prim_with_size(0u8, 5)?,
        ),
        (
            ctx.bvv_prim_with_size(1u8, 4)?,
            0,
            ctx.bvv_prim_with_size(1u8, 4)?,
        ),
        (
            ctx.bvv_prim_with_size(1u8, 4)?,
            1,
            ctx.bvv_prim_with_size(1u8, 5)?,
        ),
    ];

    for (a, b, expected) in table {
        assert_eq!(ctx.zero_ext(&a, b)?.simplify()?, expected);
    }

    Ok(())
}

#[test]
fn test_sext() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv_prim_with_size(0u8, 4)?,
            0,
            ctx.bvv_prim_with_size(0u8, 4)?,
        ),
        (
            ctx.bvv_prim_with_size(0u8, 4)?,
            1,
            ctx.bvv_prim_with_size(0u8, 5)?,
        ),
        (
            ctx.bvv_prim_with_size(1u8, 4)?,
            0,
            ctx.bvv_prim_with_size(1u8, 4)?,
        ),
        (
            ctx.bvv_prim_with_size(1u8, 4)?,
            1,
            ctx.bvv_prim_with_size(1u8, 5)?,
        ),
        (
            ctx.bvv_prim_with_size(15u8, 4)?,
            0,
            ctx.bvv_prim_with_size(15u8, 4)?,
        ),
        (
            ctx.bvv_prim_with_size(15u8, 4)?,
            1,
            ctx.bvv_prim_with_size(15u8, 5)?,
        ),
    ];

    for (a, b, expected) in table {
        assert_eq!(ctx.sign_ext(&a, b)?.simplify()?, expected);
    }

    Ok(())
}

#[test]
fn test_reverse() -> Result<()> {
    let context = Context::new();

    let table: Vec<(u64, u64)> = vec![
        (0, 0),
        (1, 1 << 63),
        (2, 1 << 62),
        (3, 1 << 62 | 1 << 63),
        (4, 1 << 61),
        (5, 1 << 61 | 1 << 63),
        (6, 1 << 61 | 1 << 62),
        (7, 1 << 61 | 1 << 62 | 1 << 63),
        (8, 1 << 60),
        (9, 1 << 60 | 1 << 63),
    ];

    for (a, expected) in table {
        let a = context.bvv_prim(a).unwrap();
        let expected = context.bvv_prim(expected).unwrap();

        let result = context.reverse(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_rotate_left() -> Result<()> {
    let context = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 1),
        (2, 1, 4),
        (8, 1, 1),
        (15, 3, 15),
    ];

    for (a, b, expected) in table {
        let a = context.bvv_prim_with_size(a, 4).unwrap();
        let b = context.bvv_prim_with_size(b, 4).unwrap();
        let expected = context.bvv_prim_with_size(expected, 4).unwrap();

        let result = context.rotate_left(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_rotate_right() -> Result<()> {
    let context = Context::new();

    let table: Vec<(u8, u8, u8)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 1),
        (4, 1, 2),
        (1, 1, 8),
        (15, 3, 15),
    ];

    for (a, b, expected) in table {
        let a = context.bvv_prim_with_size(a, 4).unwrap();
        let b = context.bvv_prim_with_size(b, 4).unwrap();
        let expected = context.bvv_prim_with_size(expected, 4).unwrap();

        let result = context.rotate_right(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}
