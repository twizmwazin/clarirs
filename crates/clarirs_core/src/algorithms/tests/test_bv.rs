use crate::{ast::bitvec::BitVecExt, prelude::*};
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
        (u64::MAX, 0, u64::MAX),
        (0, u64::MAX, u64::MAX),
        (u64::MAX, 1, 0),
        (1, u64::MAX, 0),
        (u64::MAX, u64::MAX, u64::MAX - 1),
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
        (123, 45, 78),
        (u64::MAX, 1, u64::MAX - 1),
        (u64::MAX, u64::MAX, 0),
        (u64::MAX, 0, u64::MAX),
        (0, u64::MAX, 1),
        (1, u64::MAX, 2),
        (u64::MAX - 1, u64::MAX, u64::MAX),
        (45, 123, u64::MAX - 77),
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
        (u64::MAX, 0, 0),
        (0, u64::MAX, 0),
        (u64::MAX, 1, u64::MAX),
        (1, u64::MAX, u64::MAX),
        (u64::MAX, u64::MAX, 1),
        (0x8000000000000000, 2, 0),
        (2, 0x8000000000000000, 0),
        (0x8000000000000001, 2, 2),
        (2, 0x8000000000000001, 2),
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
        (1, 1, 1),
        (255, 1, 255),
        (0, 255, 0),
        (1, 255, 0),
        (255, 255, 1),
        (128, 128, 1),
        (255, 128, 1),
        (1, 2, 0),
        (100, 200, 0),
        (u8::MAX, 3, 85),
        (u8::MAX, 4, 63),
        (240, 15, 16),
        ((u8::MAX - 1) / 2, 2, 63),
        ((u8::MAX - 1) / 2, 8, 15),
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

    let table: Vec<(i64, i64, i64)> = vec![
        (0, 1, 0),
        (1, 1, 1),
        (1, 2, 0),
        (2, 1, 2),
        (2, 2, 1),
        (2, 3, 0),
        (3, 2, 1),
        (3, 3, 1),
        (3, 0, 3),
        (-1, 1, -1),
        (-2, 3, 0),
        (-3, 2, -1),
        (-4, 3, -1),
        (1, -1, -1),
        (2, -3, 0),
        (3, -2, -1),
        (4, -3, -1),
        (-1, -1, 1),
        (-2, -3, 0),
        (-3, -2, 1),
        (-4, -3, 1),
        (0, 2, 0),
        (0, -2, 0),
        (14, 7, 2),
        (14, -7, -2),
        (-14, 7, -2),
        (-14, -7, 2),
        (15, 4, 3),
        (15, -4, -3),
        (-15, 4, -3),
        (-15, -4, 3),
        (1, i64::MAX, 0),
        (-1, i64::MAX, 0),
        (i64::MAX, 2, 4611686018427387903),
        (i64::MIN, 2, -4611686018427387904),
        (i64::MIN, 3, -3074457345618258602),
    ];

    for (a_i64, b_i64, expected_i64) in table {
        let a_bits = a_i64 as u64;
        let b_bits = b_i64 as u64;
        let expected_bits = expected_i64 as u64;

        let a = ctx.bvv_prim(a_bits)?;
        let b = ctx.bvv_prim(b_bits)?;
        let expected = ctx.bvv_prim(expected_bits)?;

        let result = ctx.sdiv(&a, &b)?.simplify()?;
        assert_eq!(result, expected, "Failed for a={}, b={}", a_i64, b_i64);
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
        (4, 2, 0),
        (5, 2, 1),
        (5, 5, 0),
        (5, 0, 5),
        (10, 3, 1),
        (10, 5, 0),
        (15, 4, 3),
        (16, 8, 0),
        (u64::MAX, 1, 0),
        (u64::MAX, 2, 1),
        (u64::MAX, u64::MAX, 0),
        (u64::MAX - 1, u64::MAX, u64::MAX - 1),
        (0, u64::MAX, 0),
        (1, u64::MAX, 1),
        (1 << 63, 1 << 32, (1 << 63) % (1 << 32)),
        (98765432123456789, 123456789, 98765432123456789 % 123456789),
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

    let table: Vec<(i64, i64, i64)> = vec![
        (0, 1, 0),
        (1, 1, 0),
        (1, 0, 1),
        (1, 2, 1),
        (2, 1, 0),
        (2, 2, 0),
        (2, 3, 2),
        (3, 2, 1),
        (3, 3, 0),
        (-1, 2, -1),
        (-2, 3, -2),
        (-3, 2, -1),
        (-4, 3, -1),
        (1, -2, 1),
        (2, -3, 2),
        (3, -2, 1),
        (4, -3, 1),
        (-1, -2, -1),
        (-2, -3, -2),
        (-3, -2, -1),
        (-4, -3, -1),
        (0, 2, 0),
        (0, -2, 0),
        (1, i64::MAX, 1),
        (-1, i64::MAX, -1),
        (i64::MAX, 2, 1),
        (i64::MIN, 2, 0),
        (i64::MIN, 3, -2),
    ];

    for (a_i64, b_i64, expected_i64) in table {
        // Cast to u64 to interpret bits in two's complement form
        let a_bits = a_i64 as u64;
        let b_bits = b_i64 as u64;
        let expected_bits = expected_i64 as u64;

        let a = ctx.bvv_prim(a_bits)?;
        let b = ctx.bvv_prim(b_bits)?;
        let expected = ctx.bvv_prim(expected_bits)?;

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
        (0, 10, 0),
        (0, u64::MAX, 0),
        (1, 10, 1),
        (1, u64::MAX, 1),
        (2, 10, 1024),
        (2, 63, 0x8000_0000_0000_0000),
        (u64::MAX, 0, 1),
        (u64::MAX, 1, u64::MAX),
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
        (u64::MAX, 0, 0),
        (u64::MAX, u64::MAX, u64::MAX),
        (u64::MAX, 1, 1),
        (1, u64::MAX, 1),
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
        (u64::MAX, 0, u64::MAX),
        (u64::MAX, u64::MAX, u64::MAX),
        (u64::MAX, 1, u64::MAX),
        (1, u64::MAX, u64::MAX),
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
        (u64::MAX, 0, u64::MAX),
        (u64::MAX, u64::MAX, 0),
        (u64::MAX, 1, u64::MAX - 1),
        (1, u64::MAX, u64::MAX - 1),
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
        (u64::MAX, 0),
        (u64::MAX - 1, 1),
        (u64::MAX - 2, 2),
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
        (0, 64, 0),
        (0, 63, 0),
        (64, 2, 16),
        (64, 3, 8),
        (64, 4, 4),
        (64, 5, 2),
        (64, 6, 1),
        (64, 7, 0),
        (0x8000000000000000, 0, 0x8000000000000000),
        (0x8000000000000000, 1, 0x4000000000000000),
        (0x8000000000000000, 63, 1),
        (0x8000000000000000, 64, 0),
        (u64::MAX, 0, u64::MAX),
        (u64::MAX, 1, u64::MAX >> 1),
        (u64::MAX, 63, 1),
        (u64::MAX, 64, 0),
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
        (64, 2, 16),
        (64, 3, 8),
        (64, 6, 1),
        (64, 7, 0),
        // Edge cases for signed numbers
        (u64::MAX, 1, u64::MAX),
        (u64::MAX, 2, u64::MAX),
        (u64::MAX, 64, u64::MAX),
        (0x8000000000000000, 0, 0x8000000000000000),
        (0x8000000000000000, 1, 0xC000000000000000),
        (0x8000000000000000, 63, 0xFFFFFFFFFFFFFFFF),
        (0x8000000000000000, 64, 0xFFFFFFFFFFFFFFFF),
        (0xFFFFFFFFFFFFFFFF, 0, 0xFFFFFFFFFFFFFFFF),
        (0xFFFFFFFFFFFFFFFF, 1, 0xFFFFFFFFFFFFFFFF),
        (0xFFFFFFFFFFFFFFFF, 63, 0xFFFFFFFFFFFFFFFF),
        (0xFFFFFFFFFFFFFFFF, 64, 0xFFFFFFFFFFFFFFFF),
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
            ctx.bvv_prim_with_size(31u8, 5)?,
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

#[test]
fn test_extract_concat() -> Result<()> {
    let ctx = Context::new();

    // Symbolic test cases
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;
    let concat = ctx.concat(&x, &y)?;

    // Extract exactly one side of symbolic values
    let extract_left = ctx.extract(&concat, 0, 16)?.simplify()?;
    assert_eq!(extract_left, x);

    let extract_right = ctx.extract(&concat, 16, 32)?.simplify()?;
    assert_eq!(extract_right, y);

    // Extract middle bits crossing the symbolic boundary
    let middle = ctx.extract(&concat, 8, 24)?.simplify()?;

    // Verify properties of the middle extraction
    let size = middle.size();
    assert_eq!(size, 16); // Should be 16 bits

    Ok(())
}
