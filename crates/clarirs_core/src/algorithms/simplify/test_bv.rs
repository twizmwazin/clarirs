use crate::{ast::bitvec::BitVecOpExt, prelude::*};
use anyhow::Result;
use smallvec::SmallVec;

#[test]
fn test_neg() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64)> = vec![
        (0, 0),
        (1, u64::MAX),
        (2, u64::MAX - 1),
        (3, u64::MAX - 2),
        (4, u64::MAX - 3),
        (5, u64::MAX - 4),
        (6, u64::MAX - 5),
        (7, u64::MAX - 6),
        (8, u64::MAX - 7),
        (9, u64::MAX - 8),
        (u64::MAX, 1),
        (u64::MAX - 1, 2),
        (u64::MAX - 2, 3),
    ];

    for (a, expected) in table.clone() {
        let a = ctx.bvv_prim(a).unwrap();
        let expected = ctx.bvv_prim(expected).unwrap();

        let result = ctx.neg(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

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
        (
            ctx.bvv_prim_with_size(0u8, 1)?,
            1,
            ctx.bvv_prim_with_size(0u8, 2)?,
        ),
        (
            ctx.bvv_prim_with_size(1u8, 1)?,
            1,
            ctx.bvv_prim_with_size(3u8, 2)?,
        ),
        (
            ctx.bvv_prim_with_size(8u8, 4)?,
            4,
            ctx.bvv_prim_with_size(248u8, 8)?,
        ),
        (
            ctx.bvv_prim_with_size(5u8, 4)?,
            4,
            ctx.bvv_prim_with_size(5u8, 8)?,
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
        (1, 0x0100000000000000),
        (4, 0x0400000000000000),
        (5, 0x0500000000000000),
        (1 << 63, 128),
        (1 << 62, 64),
        (128, 1 << 63),
        (255, 0xFF00000000000000),
        (0xFF00FF00AB000012, 0x120000AB00FF00FF),
    ];

    for (a, expected) in table {
        let a = context.bvv_prim(a).unwrap();
        let expected = context.bvv_prim(expected).unwrap();

        let result = context.reverse(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    // Testing multi-word bitvector
    // Input: 0xEEFFFFFFFFFFFFFFFF.
    // Internal representation (little-endian), it is stored as:
    //   word[0] = 0xFFFFFFFFFFFFFFFF
    //   word[1] = 0x00000000000000EE   (only 8 bits used)
    let mut words: SmallVec<[u64; 1]> = SmallVec::new();
    words.push(0xFFFFFFFFFFFFFFFF);
    words.push(0xEE);
    let original = BitVec::new(words, 72)?;

    // Input: [EE, FF, FF, FF, FF, FF, FF, FF, FF].
    // After byte reversal: [FF, FF, FF, FF, FF, FF, FF, FF, EE].
    // When repacked in little-endian order, the new words should be:
    //   new_words[0] = 0xFFFFFFFFFFFFFFEE
    //   new_words[1] = 0x00000000000000FF
    let reversed = original.reverse_bytes()?;

    // Expected words after byte reversal
    let mut expected_words: SmallVec<[u64; 1]> = SmallVec::new();
    expected_words.push(0xFFFFFFFFFFFFFFEE);
    expected_words.push(0x00000000000000FF);
    let expected = BitVec::new(expected_words, 72)?;

    assert_eq!(
        reversed, expected,
        "Multi-word bitvector byte reversal failed"
    );

    Ok(())
}

#[test]
fn test_rotate_left() -> Result<()> {
    let context = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (0, 2, 0),
        (0, 3, 0),
        (1, 1, 2),
        (1, 2, 4),
        (1, 3, 8),
        (1, 4, 1),
        (8, 2, 2),
        (8, 3, 4),
        (15, 0, 15),
        (15, 1, 15),
        (15, 2, 15),
        (15, 3, 15),
        (15, 4, 15),
        (10, 1, 5),
        (10, 2, 10),
        (10, 3, 5),
        (10, 4, 10),
        (10, 5, 5),
        (13, 1, 11),
        (5, 1, 10),
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

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (0, 2, 0),
        (0, 3, 0),
        (1, 1, 8),
        (1, 2, 4),
        (1, 3, 2),
        (1, 4, 1),
        (8, 2, 2),
        (8, 3, 1),
        (15, 0, 15),
        (15, 1, 15),
        (15, 2, 15),
        (15, 3, 15),
        (15, 4, 15),
        (10, 1, 5),
        (10, 2, 10),
        (10, 3, 5),
        (10, 4, 10),
        (10, 5, 5),
        (13, 1, 14),
        (5, 1, 10),
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
fn test_extract() -> Result<()> {
    let ctx = Context::new();

    // Whole bitvector, concrete
    let bv = ctx.bvv_prim(0x1234_5678_9ABC_DEF0_u64).unwrap();
    let extract = ctx.extract(&bv, 63, 0)?.simplify()?;
    assert_eq!(extract, bv);

    // Whole bitvector, symbolic
    let x = ctx.bvs("x", 64)?;
    let extract = ctx.extract(&x, 63, 0)?.simplify()?;
    assert_eq!(extract, x);

    // Partial extraction, concrete
    let extract = ctx.extract(&bv, 63, 32)?.simplify()?;
    let expected = ctx.bvv_prim(0x1234_5678_u32).unwrap();
    assert_eq!(extract, expected);

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
    let extract_left = ctx.extract(&concat, 31, 16)?.simplify()?;
    assert_eq!(extract_left, x);

    let extract_right = ctx.extract(&concat, 15, 0)?.simplify()?;
    assert_eq!(extract_right, y);

    // Extract middle bits crossing the symbolic boundary
    let middle = ctx.extract(&concat, 23, 8)?.simplify()?;

    // Verify properties of the middle extraction
    let size = middle.size();
    assert_eq!(size, 16); // Should be 16 bits

    Ok(())
}

#[test]
fn test_identity_simplifications() -> anyhow::Result<()> {
    let ctx = Context::new();

    let x = ctx.bvs("x", 64)?;

    let zero = ctx.bvv_prim(0u64)?;
    let one = ctx.bvv_prim(1u64)?;
    let all_ones = ctx.bvv_prim(u64::MAX)?;

    // AND identities
    let simplified = ctx.and(&x, &zero)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.and(&zero, &x)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.and(&x, &all_ones)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.and(&all_ones, &x)?.simplify()?;
    assert_eq!(simplified, x);

    // OR identities
    let simplified = ctx.or(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.or(&zero, &x)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.or(&x, &all_ones)?.simplify()?;
    assert_eq!(simplified, all_ones);

    let simplified = ctx.or(&all_ones, &x)?.simplify()?;
    assert_eq!(simplified, all_ones);

    // XOR identities
    let simplified = ctx.xor(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.xor(&zero, &x)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.xor(&x, &all_ones)?.simplify()?;
    let not_x = ctx.not(&x)?.simplify()?;
    assert_eq!(simplified, not_x);

    let simplified = ctx.xor(&all_ones, &x)?.simplify()?;
    assert_eq!(simplified, not_x);

    // ADD identities
    let simplified = ctx.add(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.add(&zero, &x)?.simplify()?;
    assert_eq!(simplified, x);

    // SUB identities
    let simplified = ctx.sub(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.sub(&x, &x)?.simplify()?;
    assert_eq!(simplified, zero);

    // MUL identities
    let simplified = ctx.mul(&x, &zero)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.mul(&zero, &x)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.mul(&x, &one)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.mul(&one, &x)?.simplify()?;
    assert_eq!(simplified, x);

    // UDIV identities
    let simplified = ctx.udiv(&x, &one)?.simplify()?;
    assert_eq!(simplified, x);

    // SDIV identities
    let simplified = ctx.sdiv(&x, &one)?.simplify()?;
    assert_eq!(simplified, x);

    Ok(())
}
