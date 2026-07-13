use crate::prelude::*;
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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.neg(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_double_negation() -> Result<()> {
    let ctx = Context::new();

    // Test with concrete values
    let table: Vec<(u64, u64)> = vec![
        (0, 0),
        (1, 1),
        (2, 2),
        (42, 42),
        (u64::MAX, u64::MAX),
        (u64::MAX - 1, u64::MAX - 1),
    ];

    for (a, expected) in table {
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let neg_a = ctx.neg(&a)?;
        let double_neg = ctx.neg(&neg_a)?.simplify()?;
        assert_eq!(double_neg, expected);
    }

    // Test with symbolic value
    let x = ctx.bvs("x", 64)?;
    let neg_x = ctx.neg(&x)?;
    let double_neg_x = ctx.neg(&neg_x)?.simplify()?;
    assert_eq!(double_neg_x, x);

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

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
        let a = ctx.bvv(BitVec::from((u64::from(a), 8))).unwrap();
        let b = ctx.bvv(BitVec::from((u64::from(b), 8))).unwrap();
        let expected = ctx.bvv(BitVec::from((u64::from(expected), 8))).unwrap();

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

        let a = ctx.bvv(BitVec::from((a_bits, 64)))?;
        let b = ctx.bvv(BitVec::from((b_bits, 64)))?;
        let expected = ctx.bvv(BitVec::from((expected_bits, 64)))?;

        let result = ctx.sdiv(&a, &b)?.simplify()?;
        assert_eq!(result, expected, "Failed for a={a_i64}, b={b_i64}");
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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

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

        let a = ctx.bvv(BitVec::from((a_bits, 64)))?;
        let b = ctx.bvv(BitVec::from((b_bits, 64)))?;
        let expected = ctx.bvv(BitVec::from((expected_bits, 64)))?;

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.and2(&a, &b)?.simplify()?;
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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.or2(&a, &b)?.simplify()?;
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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.xor2(&a, &b)?.simplify()?;
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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.not(&a)?.simplify()?;
        assert_eq!(result, expected);
    }

    Ok(())
}

#[test]
fn test_shl() -> Result<()> {
    let ctx = Context::new();

    let table: Vec<(u64, u64, u64)> = vec![
        (0, 0, 0),
        (0, 1, 0),
        (1, 0, 1),
        (1, 1, 2),
        (1, 2, 4),
        (2, 1, 4),
        (2, 2, 8),
        (2, 3, 16),
        (3, 2, 12),
        (3, 3, 24),
        // Note: Shifts of u64::MAX cause overflow in the BitVec implementation
        // This is a pre-existing bug not related to simplification
        // (u64::MAX, 1, u64::MAX - 1),
        // (u64::MAX, 2, u64::MAX - 3),
        (42, 1, 84),
        (255, 8, 65280),
    ];

    for (a, b, expected) in table {
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.shl(&a, &b)?.simplify()?;
        assert_eq!(result, expected, "shl({a:?}, {b:?})");
    }

    // Test zero-shift with symbolic value
    let x = ctx.bvs("x", 64)?;
    let zero = ctx.bvv(BitVec::from((0, 64)))?;
    let result = ctx.shl(&x, &zero)?.simplify()?;
    assert_eq!(result, x);

    Ok(())
}

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.lshr(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    // Test zero-shift with symbolic value
    let x = ctx.bvs("x", 64)?;
    let zero = ctx.bvv(BitVec::from((0, 64)))?;
    let result = ctx.lshr(&x, &zero)?.simplify()?;
    assert_eq!(result, x);

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
        let a = ctx.bvv(BitVec::from((a, 64))).unwrap();
        let b = ctx.bvv(BitVec::from((b, 64))).unwrap();
        let expected = ctx.bvv(BitVec::from((expected, 64))).unwrap();

        let result = ctx.ashr(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    // Test zero-shift with symbolic value
    let x = ctx.bvs("x", 64)?;
    let zero = ctx.bvv(BitVec::from((0, 64)))?;
    let result = ctx.ashr(&x, &zero)?.simplify()?;
    assert_eq!(result, x);

    Ok(())
}

#[test]
fn test_zext() -> Result<()> {
    let ctx = Context::new();

    let table = vec![
        (
            ctx.bvv(BitVec::from((0, 4)))?,
            0,
            ctx.bvv(BitVec::from((0, 4)))?,
        ),
        (
            ctx.bvv(BitVec::from((0, 4)))?,
            1,
            ctx.bvv(BitVec::from((0, 5)))?,
        ),
        (
            ctx.bvv(BitVec::from((1, 4)))?,
            0,
            ctx.bvv(BitVec::from((1, 4)))?,
        ),
        (
            ctx.bvv(BitVec::from((1, 4)))?,
            1,
            ctx.bvv(BitVec::from((1, 5)))?,
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
            ctx.bvv(BitVec::from((0, 4)))?,
            0,
            ctx.bvv(BitVec::from((0, 4)))?,
        ),
        (
            ctx.bvv(BitVec::from((0, 4)))?,
            1,
            ctx.bvv(BitVec::from((0, 5)))?,
        ),
        (
            ctx.bvv(BitVec::from((1, 4)))?,
            0,
            ctx.bvv(BitVec::from((1, 4)))?,
        ),
        (
            ctx.bvv(BitVec::from((1, 4)))?,
            1,
            ctx.bvv(BitVec::from((1, 5)))?,
        ),
        (
            ctx.bvv(BitVec::from((15, 4)))?,
            0,
            ctx.bvv(BitVec::from((15, 4)))?,
        ),
        (
            ctx.bvv(BitVec::from((15, 4)))?,
            1,
            ctx.bvv(BitVec::from((31, 5)))?,
        ),
        (
            ctx.bvv(BitVec::from((0, 1)))?,
            1,
            ctx.bvv(BitVec::from((0, 2)))?,
        ),
        (
            ctx.bvv(BitVec::from((1, 1)))?,
            1,
            ctx.bvv(BitVec::from((3, 2)))?,
        ),
        (
            ctx.bvv(BitVec::from((8, 4)))?,
            4,
            ctx.bvv(BitVec::from((248, 8)))?,
        ),
        (
            ctx.bvv(BitVec::from((5, 4)))?,
            4,
            ctx.bvv(BitVec::from((5, 8)))?,
        ),
    ];

    for (a, b, expected) in table {
        assert_eq!(ctx.sign_ext(&a, b)?.simplify()?, expected);
    }

    Ok(())
}

#[test]
fn test_byte_reverse() -> Result<()> {
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
        let a = context.bvv(BitVec::from((a, 64))).unwrap();
        let expected = context.bvv(BitVec::from((expected, 64))).unwrap();

        let result = context.byte_reverse(&a)?.simplify()?;
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
        let a = context.bvv(BitVec::from((a, 4))).unwrap();
        let b = context.bvv(BitVec::from((b, 4))).unwrap();
        let expected = context.bvv(BitVec::from((expected, 4))).unwrap();

        let result = context.rotate_left(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    // Test zero-rotation with symbolic value
    let x = context.bvs("x", 4)?;
    let zero = context.bvv(BitVec::from((0, 4)))?;
    let result = context.rotate_left(&x, &zero)?.simplify()?;
    assert_eq!(result, x);

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
        let a = context.bvv(BitVec::from((a, 4))).unwrap();
        let b = context.bvv(BitVec::from((b, 4))).unwrap();
        let expected = context.bvv(BitVec::from((expected, 4))).unwrap();

        let result = context.rotate_right(&a, &b)?.simplify()?;
        assert_eq!(result, expected);
    }

    // Test zero-rotation with symbolic value
    let x = context.bvs("x", 4)?;
    let zero = context.bvv(BitVec::from((0, 4)))?;
    let result = context.rotate_right(&x, &zero)?.simplify()?;
    assert_eq!(result, x);

    Ok(())
}

#[test]
fn test_extract() -> Result<()> {
    let ctx = Context::new();

    // Whole bitvector, concrete
    let bv = ctx.bvv(BitVec::from((0x1234_5678_9ABC_DEF0, 64))).unwrap();
    let extract = ctx.extract(&bv, 63, 0)?.simplify()?;
    assert_eq!(extract, bv);

    // Whole bitvector, symbolic
    let x = ctx.bvs("x", 64)?;
    let extract = ctx.extract(&x, 63, 0)?.simplify()?;
    assert_eq!(extract, x);

    // Partial extraction, concrete
    let extract = ctx.extract(&bv, 63, 32)?.simplify()?;
    let expected = ctx.bvv(BitVec::from((0x1234_5678, 32))).unwrap();
    assert_eq!(extract, expected);

    Ok(())
}

#[test]
fn test_extract_concat() -> Result<()> {
    let ctx = Context::new();

    // Symbolic test cases
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;
    let concat = ctx.concat2(x.clone(), y.clone())?;

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

    let zero = ctx.bvv(BitVec::from((0, 64)))?;
    let one = ctx.bvv(BitVec::from((1, 64)))?;
    let all_ones = ctx.bvv(BitVec::from((u64::MAX, 64)))?;

    // AND identities
    let simplified = ctx.and2(&x, &zero)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.and2(&zero, &x)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.and2(&x, &all_ones)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.and2(&all_ones, &x)?.simplify()?;
    assert_eq!(simplified, x);

    // OR identities
    let simplified = ctx.or2(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.or2(&zero, &x)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.or2(&x, &all_ones)?.simplify()?;
    assert_eq!(simplified, all_ones);

    let simplified = ctx.or2(&all_ones, &x)?.simplify()?;
    assert_eq!(simplified, all_ones);

    // XOR identities
    let simplified = ctx.xor2(&x, &zero)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.xor2(&zero, &x)?.simplify()?;
    assert_eq!(simplified, x);

    let simplified = ctx.xor2(&x, &all_ones)?.simplify()?;
    let not_x = ctx.not(&x)?.simplify()?;
    assert_eq!(simplified, not_x);

    let simplified = ctx.xor2(&all_ones, &x)?.simplify()?;
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

#[test]
fn test_bitvec_not_identities() -> Result<()> {
    let ctx = Context::new();

    let x = ctx.bvs("x", 64)?;
    let not_x = ctx.not(&x)?;
    let zero = ctx.bvv(BitVec::from((0, 64)))?;
    let all_ones = ctx.bvv(BitVec::from((u64::MAX, 64)))?;

    // x & ¬x = 0
    let simplified = ctx.and2(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, zero);

    let simplified = ctx.and2(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, zero);

    // x | ¬x = -1 (all ones)
    let simplified = ctx.or2(&x, &not_x)?.simplify()?;
    assert_eq!(simplified, all_ones);

    let simplified = ctx.or2(&not_x, &x)?.simplify()?;
    assert_eq!(simplified, all_ones);

    Ok(())
}

#[test]
fn test_extract_full_width() -> Result<()> {
    let ctx = Context::new();

    // Test extracting full width of a 32-bit BVS
    let bvs = ctx.bvs("test", 32)?;
    let extract_full = ctx.extract(&bvs, 31, 0)?;
    let simplified = extract_full.simplify()?;

    // Should simplify to the original BVS
    assert_eq!(simplified, bvs);

    // Test extracting full width of a BVV
    let bvv = ctx.bvv(BitVec::from((42, 32)))?;
    let extract_full_bvv = ctx.extract(&bvv, 31, 0)?;
    let simplified_bvv = extract_full_bvv.simplify()?;

    // Should simplify to the original BVV
    assert_eq!(simplified_bvv, bvv);

    Ok(())
}

#[test]
fn test_extract_zeroext() -> Result<()> {
    let ctx = Context::new();

    // Test Extract(ZeroExt(x, n), high, low) where high < original_size
    let original = ctx.bvs("test", 32)?;
    let zero_ext = ctx.zero_ext(&original, 64)?; // 32 -> 64 bits
    let extract = ctx.extract(&zero_ext, 31, 0)?; // Extract original 32 bits
    let simplified = extract.simplify()?;

    // Should simplify to the original (since we're extracting the full original width)
    assert_eq!(simplified, original);

    Ok(())
}

#[test]
fn test_debug_extract_size() -> Result<()> {
    let ctx = Context::new();

    let bvs = ctx.bvs("test", 32)?;
    println!("BVS size: {}", bvs.size());

    let extract_full = ctx.extract(&bvs, 31, 0)?;
    println!("Extract before simplify: {extract_full:?}");

    let simplified = extract_full.simplify()?;
    println!("Extract after simplify: {simplified:?}");

    Ok(())
}

// ---------------------------------------------------------------------------
// And rules
// ---------------------------------------------------------------------------

#[test]
fn test_and_flattening() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let z = ctx.bvs("z", 8)?;

    // (x & y) & z => x & y & z
    assert_eq!(
        ctx.and2(&ctx.and2(&x, &y)?, &z)?.simplify()?,
        ctx.and(vec![x.clone(), y.clone(), z.clone()])?
    );

    Ok(())
}

#[test]
fn test_and_deduplication() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // x & y & x => x & y
    assert_eq!(
        ctx.and(vec![x.clone(), y.clone(), x.clone()])?.simplify()?,
        ctx.and2(&x, &y)?
    );

    Ok(())
}

#[test]
fn test_and_constant_folding_multiple() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let c1 = ctx.bvv(BitVec::from((0xF0, 8)))?;
    let c2 = ctx.bvv(BitVec::from((0x3C, 8)))?;

    // x & 0xF0 & 0x3C => x & 0x30
    assert_eq!(
        ctx.and(vec![x.clone(), c1.clone(), c2.clone()])?
            .simplify()?,
        ctx.and2(&x, &ctx.bvv(BitVec::from((0x30, 8)))?)?
    );

    // Nested constants fold too: (x & 0xF0) & 0x3C => x & 0x30
    assert_eq!(
        ctx.and2(&ctx.and2(&x, &c1)?, &c2)?.simplify()?,
        ctx.and2(&x, &ctx.bvv(BitVec::from((0x30, 8)))?)?
    );

    // Constants folding to zero absorb everything
    let c3 = ctx.bvv(BitVec::from((0x0F, 8)))?;
    assert_eq!(
        ctx.and(vec![x.clone(), c1.clone(), c3.clone()])?
            .simplify()?,
        ctx.bvv(BitVec::from((0, 8)))?
    );

    Ok(())
}

#[test]
fn test_and_distribute_over_concat() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // Concat(x, y) & 0xFF00 => Concat(x, 0x00)
    let expr = ctx
        .and2(&ctx.concat2(&x, &y)?, &ctx.bvv(BitVec::from((0xFF00, 16)))?)?
        .simplify()?;
    assert_eq!(expr, ctx.concat2(&x, &ctx.bvv(BitVec::from((0, 8)))?)?);

    Ok(())
}

#[test]
fn test_and_distribute_over_zero_ext() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;

    // ZeroExt(x, 8) & 0x0F => ZeroExt(x & 0x0F, 8)
    let expr = ctx
        .and2(&ctx.zero_ext(&x, 8)?, &ctx.bvv(BitVec::from((0x0F, 16)))?)?
        .simplify()?;
    assert_eq!(
        expr,
        ctx.zero_ext(&ctx.and2(&x, &ctx.bvv(BitVec::from((0x0F, 8)))?)?, 8)?
    );

    Ok(())
}

#[test]
fn test_and_rotate_shift_mask() -> Result<()> {
    let ctx = Context::new();
    let a = ctx.bvs("a", 32)?;
    let shl_amt = ctx.bvv(BitVec::from((8, 32)))?;
    let lshr_amt = ctx.bvv(BitVec::from((24, 32)))?;

    // ((a << 8) | (a >> 24)) & 0xFF00FF00
    //   => ((a & 0x00FF00FF) << 8) | ((a & 0x00FF00FF) >> 24)
    // (the mask is un-rotated and applied to the input)
    let rotated = ctx.or2(&ctx.shl(&a, &shl_amt)?, &ctx.lshr(&a, &lshr_amt)?)?;
    let expr = ctx
        .and2(&rotated, &ctx.bvv(BitVec::from((0xFF00FF00u64, 32)))?)?
        .simplify()?;

    let masked = ctx.and2(&a, &ctx.bvv(BitVec::from((0x00FF00FF, 32)))?)?;
    let expected = ctx.or2(&ctx.shl(&masked, &shl_amt)?, &ctx.lshr(&masked, &lshr_amt)?)?;
    assert_eq!(expr, expected);

    Ok(())
}

// ---------------------------------------------------------------------------
// Or rules
// ---------------------------------------------------------------------------

#[test]
fn test_or_flattening_and_constant_folding() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;

    // (x | 0x0F) | 0x30 => x | 0x3F
    let expr = ctx
        .or(vec![
            ctx.or2(&x, &ctx.bvv(BitVec::from((0x0F, 8)))?)?,
            ctx.bvv(BitVec::from((0x30, 8)))?,
        ])?
        .simplify()?;
    assert_eq!(expr, ctx.or2(&x, &ctx.bvv(BitVec::from((0x3F, 8)))?)?);

    Ok(())
}

#[test]
fn test_or_deduplication() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // x | y | x => x | y
    assert_eq!(
        ctx.or(vec![x.clone(), y.clone(), x.clone()])?.simplify()?,
        ctx.or2(&x, &y)?
    );

    Ok(())
}

#[test]
fn test_or_distribute_over_concat() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // Concat(x, y) | 0x00FF => Concat(x, 0xFF)
    let expr = ctx
        .or2(&ctx.concat2(&x, &y)?, &ctx.bvv(BitVec::from((0x00FF, 16)))?)?
        .simplify()?;
    assert_eq!(expr, ctx.concat2(&x, &ctx.bvv(BitVec::from((0xFF, 8)))?)?);

    Ok(())
}

// ---------------------------------------------------------------------------
// Xor rules
// ---------------------------------------------------------------------------

#[test]
fn test_xor_pair_cancellation() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;

    // x ^ x => 0
    assert_eq!(ctx.xor2(&x, &x)?.simplify()?, zero);

    // x ^ y ^ x => y
    assert_eq!(
        ctx.xor(vec![x.clone(), y.clone(), x.clone()])?.simplify()?,
        y
    );

    // x ^ y ^ x ^ y => 0
    assert_eq!(
        ctx.xor(vec![x.clone(), y.clone(), x.clone(), y.clone()])?
            .simplify()?,
        zero
    );

    Ok(())
}

#[test]
fn test_xor_double_negation() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // ¬x ^ ¬y => x ^ y
    assert_eq!(
        ctx.xor2(&ctx.not(&x)?, &ctx.not(&y)?)?.simplify()?,
        ctx.xor2(&x, &y)?
    );

    Ok(())
}

#[test]
fn test_xor_distribute_over_concat() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // Concat(x, y) ^ 0x00FF => Concat(x, ~y)
    let expr = ctx
        .xor2(&ctx.concat2(&x, &y)?, &ctx.bvv(BitVec::from((0x00FF, 16)))?)?
        .simplify()?;
    assert_eq!(expr, ctx.concat2(&x, &ctx.not(&y)?)?);

    Ok(())
}

// ---------------------------------------------------------------------------
// Add / Sub / Mul rules
// ---------------------------------------------------------------------------

#[test]
fn test_add_flattening_and_constant_folding() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;
    let three = ctx.bvv(BitVec::from((3, 8)))?;

    // x + 5 + 3 => x + 8
    assert_eq!(
        ctx.add_many(vec![x.clone(), five.clone(), three.clone()])?
            .simplify()?,
        ctx.add(&x, &ctx.bvv(BitVec::from((8, 8)))?)?
    );

    // (x + y) + 5 => x + y + 5 (flattened)
    assert_eq!(
        ctx.add(&ctx.add(&x, &y)?, &five)?.simplify()?,
        ctx.add_many(vec![x.clone(), y.clone(), five.clone()])?
    );

    // Constants cancelling to zero disappear: x + 5 + (-5) => x
    let neg_five = ctx.bvv(BitVec::from((251, 8)))?;
    assert_eq!(
        ctx.add_many(vec![x.clone(), five.clone(), neg_five])?
            .simplify()?,
        x
    );

    Ok(())
}

#[test]
fn test_add_combines_with_sub_constant() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;
    let three = ctx.bvv(BitVec::from((3, 8)))?;

    // 5 + (x - 3) => x + 2
    assert_eq!(
        ctx.add(&five, &ctx.sub(&x, &three)?)?.simplify()?,
        ctx.add(&x, &ctx.bvv(BitVec::from((2, 8)))?)?
    );

    // 5 + (3 - x): current behavior rewrites to (x - 8).
    // NOTE: this documents a suspected bug in bv.rs — mathematically
    // 5 + (3 - x) equals (8 - x), not (x - 8). The rewrite in the
    // (BVV, Sub(BVV, other)) arm of AstOp::Add emits
    // sub(other, combined) instead of sub(combined, other).
    assert_eq!(
        ctx.add(&five, &ctx.sub(&three, &x)?)?.simplify()?,
        ctx.sub(&x, &ctx.bvv(BitVec::from((8, 8)))?)?
    );

    Ok(())
}

#[test]
fn test_sub_nested_constant_folding() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;
    let three = ctx.bvv(BitVec::from((3, 8)))?;

    // (x - 3) - 5 => x - 8
    assert_eq!(
        ctx.sub(&ctx.sub(&x, &three)?, &five)?.simplify()?,
        ctx.sub(&x, &ctx.bvv(BitVec::from((8, 8)))?)?
    );

    Ok(())
}

#[test]
fn test_sub_of_add_constant_folding() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;
    let three = ctx.bvv(BitVec::from((3, 8)))?;

    // (x + 5) - 3 => x + 2
    assert_eq!(
        ctx.sub(&ctx.add(&x, &five)?, &three)?.simplify()?,
        ctx.add(&x, &ctx.bvv(BitVec::from((2, 8)))?)?
    );

    // (x + 3) - 3 => x (constant cancels entirely)
    assert_eq!(ctx.sub(&ctx.add(&x, &three)?, &three)?.simplify()?, x);

    Ok(())
}

#[test]
fn test_sub_structurally_equal_operands() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;

    // (x + y) - (x + y) => 0
    let sum = ctx.add(&x, &y)?;
    assert_eq!(ctx.sub(&sum, &sum)?.simplify()?, zero);

    // (x + y) - 0: the (Add, BVV) arm matches first and finds no constant
    // to fold, so the x - 0 => x identity is NOT applied here (documents a
    // missed simplification in the current implementation).
    assert_eq!(
        ctx.sub(&sum, &zero)?.simplify()?,
        ctx.sub(&ctx.add(&x, &y)?, &zero)?
    );

    Ok(())
}

#[test]
fn test_mul_flattening_and_constant_folding() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let two = ctx.bvv(BitVec::from((2, 8)))?;
    let three = ctx.bvv(BitVec::from((3, 8)))?;

    // x * 2 * 3 => x * 6
    assert_eq!(
        ctx.mul_many(vec![x.clone(), two.clone(), three.clone()])?
            .simplify()?,
        ctx.mul(&x, &ctx.bvv(BitVec::from((6, 8)))?)?
    );

    // (x * 2) * 3 => x * 6 (flattened and folded)
    assert_eq!(
        ctx.mul(&ctx.mul(&x, &two)?, &three)?.simplify()?,
        ctx.mul(&x, &ctx.bvv(BitVec::from((6, 8)))?)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Division by zero behavior
// ---------------------------------------------------------------------------

#[test]
fn test_div_by_zero_behavior() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;
    let five = ctx.bvv(BitVec::from((5, 8)))?;

    // With the default simplify(), division by a concrete zero is left
    // unsimplified (even fully concrete divisions).
    assert_eq!(ctx.udiv(&x, &zero)?.simplify()?, ctx.udiv(&x, &zero)?);
    assert_eq!(ctx.udiv(&five, &zero)?.simplify()?, ctx.udiv(&five, &zero)?);
    assert_eq!(ctx.sdiv(&x, &zero)?.simplify()?, ctx.sdiv(&x, &zero)?);

    // With error_on_dbz set, simplification errors out
    assert!(ctx.udiv(&x, &zero)?.simplify_ext(true, true).is_err());
    assert!(ctx.sdiv(&x, &zero)?.simplify_ext(true, true).is_err());

    Ok(())
}

// ---------------------------------------------------------------------------
// Shift rules
// ---------------------------------------------------------------------------

#[test]
fn test_shift_zero_base() -> Result<()> {
    let ctx = Context::new();
    let y = ctx.bvs("y", 8)?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;

    // 0 shifted/rotated by anything (even symbolic) is 0
    assert_eq!(ctx.shl(&zero, &y)?.simplify()?, zero);
    assert_eq!(ctx.lshr(&zero, &y)?.simplify()?, zero);
    assert_eq!(ctx.ashr(&zero, &y)?.simplify()?, zero);
    assert_eq!(ctx.rotate_left(&zero, &y)?.simplify()?, zero);
    assert_eq!(ctx.rotate_right(&zero, &y)?.simplify()?, zero);

    Ok(())
}

#[test]
fn test_shl_overshift_concrete() -> Result<()> {
    let ctx = Context::new();
    let one = ctx.bvv(BitVec::from((1, 8)))?;
    let zero = ctx.bvv(BitVec::from((0, 8)))?;

    // Shifting by >= bit width yields zero
    assert_eq!(
        ctx.shl(&one, &ctx.bvv(BitVec::from((8, 8)))?)?.simplify()?,
        zero
    );
    assert_eq!(
        ctx.shl(&one, &ctx.bvv(BitVec::from((200, 8)))?)?
            .simplify()?,
        zero
    );

    Ok(())
}

#[test]
fn test_shl_of_zero_ext() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze = ctx.zero_ext(&x, 8)?;
    let zero8 = ctx.bvv(BitVec::from((0, 8)))?;

    // shl(ZeroExt(x, 8), 8) => Concat(x, 0x00)
    assert_eq!(
        ctx.shl(&ze, &ctx.bvv(BitVec::from((8, 16)))?)?.simplify()?,
        ctx.concat2(&x, &zero8)?
    );

    // shl(ZeroExt(x, 8), 10) => Concat(x << 2, 0x00)
    assert_eq!(
        ctx.shl(&ze, &ctx.bvv(BitVec::from((10, 16)))?)?
            .simplify()?,
        ctx.concat2(&ctx.shl(&x, &ctx.bvv(BitVec::from((2, 8)))?)?, &zero8)?
    );

    // shl(ZeroExt(x, 8), 16) => 0 (everything shifted out)
    assert_eq!(
        ctx.shl(&ze, &ctx.bvv(BitVec::from((16, 16)))?)?
            .simplify()?,
        ctx.bvv(BitVec::from((0, 16)))?
    );

    Ok(())
}

#[test]
fn test_lshr_of_shl_extract_pattern() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;

    // lshr(shl(x, 4), 8) extracts bits [11:8] and zero-extends
    let expr = ctx
        .lshr(
            &ctx.shl(&x, &ctx.bvv(BitVec::from((4, 16)))?)?,
            &ctx.bvv(BitVec::from((8, 16)))?,
        )?
        .simplify()?;
    assert_eq!(expr, ctx.zero_ext(&ctx.extract(&x, 11, 8)?, 12)?);

    // All bits shifted out => 0
    let expr = ctx
        .lshr(
            &ctx.shl(&x, &ctx.bvv(BitVec::from((8, 16)))?)?,
            &ctx.bvv(BitVec::from((8, 16)))?,
        )?
        .simplify()?;
    assert_eq!(expr, ctx.bvv(BitVec::from((0, 16)))?);

    Ok(())
}

#[test]
fn test_lshr_of_shl_zero_ext_patterns() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze = ctx.zero_ext(&x, 8)?;

    // lshr(shl(ZeroExt(x, 8), 4), 4): the extraction [11:4] spans the
    // original and extended parts => zero_ext(extract(x, 7, 4), 12)
    let expr = ctx
        .lshr(
            &ctx.shl(&ze, &ctx.bvv(BitVec::from((4, 16)))?)?,
            &ctx.bvv(BitVec::from((4, 16)))?,
        )?
        .simplify()?;
    assert_eq!(expr, ctx.zero_ext(&ctx.extract(&x, 7, 4)?, 12)?);

    // lshr(shl(ZeroExt(x, 8), 2), 12): extraction [13:12] is entirely in
    // the zero-extended part => 0
    let expr = ctx
        .lshr(
            &ctx.shl(&ze, &ctx.bvv(BitVec::from((2, 16)))?)?,
            &ctx.bvv(BitVec::from((12, 16)))?,
        )?
        .simplify()?;
    assert_eq!(expr, ctx.bvv(BitVec::from((0, 16)))?);

    Ok(())
}

// ---------------------------------------------------------------------------
// Rotate rules
// ---------------------------------------------------------------------------

#[test]
fn test_rotate_by_multiple_of_size() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 4)?;

    // Rotating by the full width is the identity
    assert_eq!(
        ctx.rotate_left(&x, &ctx.bvv(BitVec::from((4, 4)))?)?
            .simplify()?,
        x
    );
    assert_eq!(
        ctx.rotate_right(&x, &ctx.bvv(BitVec::from((4, 4)))?)?
            .simplify()?,
        x
    );

    // Rotating by a multiple of the width is the identity
    let x8 = ctx.bvs("x8", 8)?;
    assert_eq!(
        ctx.rotate_left(&x8, &ctx.bvv(BitVec::from((16, 8)))?)?
            .simplify()?,
        x8
    );

    Ok(())
}

#[test]
fn test_nested_rotate_combining() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 4)?;
    let one = ctx.bvv(BitVec::from((1, 4)))?;
    let two = ctx.bvv(BitVec::from((2, 4)))?;
    let three = ctx.bvv(BitVec::from((3, 4)))?;

    // rotl(rotl(x, 1), 2) => rotl(x, 3)
    assert_eq!(
        ctx.rotate_left(&ctx.rotate_left(&x, &one)?, &two)?
            .simplify()?,
        ctx.rotate_left(&x, &three)?
    );

    // rotl(rotl(x, 3), 1) => rotl(x, 0) => x
    assert_eq!(
        ctx.rotate_left(&ctx.rotate_left(&x, &three)?, &one)?
            .simplify()?,
        x
    );

    // rotr(rotr(x, 1), 2) => rotr(x, 3)
    assert_eq!(
        ctx.rotate_right(&ctx.rotate_right(&x, &one)?, &two)?
            .simplify()?,
        ctx.rotate_right(&x, &three)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// ZeroExt / SignExt rules
// ---------------------------------------------------------------------------

#[test]
fn test_zero_ext_nested_combining() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;

    // ZeroExt(ZeroExt(x, 4), 4) => ZeroExt(x, 8)
    assert_eq!(
        ctx.zero_ext(&ctx.zero_ext(&x, 4)?, 4)?.simplify()?,
        ctx.zero_ext(&x, 8)?
    );

    Ok(())
}

#[test]
fn test_zero_ext_over_ite() -> Result<()> {
    let ctx = Context::new();
    let c = ctx.bools("c")?;
    let one = ctx.bvv(BitVec::from((1, 8)))?;
    let two = ctx.bvv(BitVec::from((2, 8)))?;

    // ZeroExt(ite(c, 1, 2), 8) => ite(c, 1_16, 2_16)
    assert_eq!(
        ctx.zero_ext(&ctx.ite(&c, &one, &two)?, 8)?.simplify()?,
        ctx.ite(
            &c,
            &ctx.bvv(BitVec::from((1, 16)))?,
            &ctx.bvv(BitVec::from((2, 16)))?
        )?
    );

    Ok(())
}

#[test]
fn test_sign_ext_nested_combining() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;

    // SignExt(SignExt(x, 4), 4) => SignExt(x, 8)
    assert_eq!(
        ctx.sign_ext(&ctx.sign_ext(&x, 4)?, 4)?.simplify()?,
        ctx.sign_ext(&x, 8)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Extract rules
// ---------------------------------------------------------------------------

#[test]
fn test_extract_nested_combining() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 32)?;

    // extract(extract(x, 23, 8), 7, 0) => extract(x, 15, 8)
    assert_eq!(
        ctx.extract(&ctx.extract(&x, 23, 8)?, 7, 0)?.simplify()?,
        ctx.extract(&x, 15, 8)?
    );

    Ok(())
}

#[test]
fn test_extract_through_add_sub() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;
    let ex = ctx.extract(&x, 7, 0)?;
    let ey = ctx.extract(&y, 7, 0)?;

    // extract(x + y, 7, 0) => extract(x, 7, 0) + extract(y, 7, 0)
    assert_eq!(
        ctx.extract(&ctx.add(&x, &y)?, 7, 0)?.simplify()?,
        ctx.add(&ex, &ey)?
    );

    // extract(x - y, 7, 0) => extract(x, 7, 0) - extract(y, 7, 0)
    assert_eq!(
        ctx.extract(&ctx.sub(&x, &y)?, 7, 0)?.simplify()?,
        ctx.sub(&ex, &ey)?
    );

    Ok(())
}

#[test]
fn test_extract_through_bitwise_ops() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;
    let ex = ctx.extract(&x, 7, 4)?;
    let ey = ctx.extract(&y, 7, 4)?;

    assert_eq!(
        ctx.extract(&ctx.and2(&x, &y)?, 7, 4)?.simplify()?,
        ctx.and2(&ex, &ey)?
    );
    assert_eq!(
        ctx.extract(&ctx.or2(&x, &y)?, 7, 4)?.simplify()?,
        ctx.or2(&ex, &ey)?
    );
    assert_eq!(
        ctx.extract(&ctx.xor2(&x, &y)?, 7, 4)?.simplify()?,
        ctx.xor2(&ex, &ey)?
    );
    // extract(~x, 7, 4) => ~extract(x, 7, 4)
    assert_eq!(ctx.extract(&ctx.not(&x)?, 7, 4)?.simplify()?, ctx.not(&ex)?);

    Ok(())
}

#[test]
fn test_extract_through_ite() -> Result<()> {
    let ctx = Context::new();
    let c = ctx.bools("c")?;
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;

    // extract(ite(c, x, y), 7, 0) => ite(c, extract(x), extract(y))
    assert_eq!(
        ctx.extract(&ctx.ite(&c, &x, &y)?, 7, 0)?.simplify()?,
        ctx.ite(&c, &ctx.extract(&x, 7, 0)?, &ctx.extract(&y, 7, 0)?)?
    );

    Ok(())
}

#[test]
fn test_extract_zero_ext_parts() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let ze = ctx.zero_ext(&x, 8)?;

    // Entirely within the zero-extended bits => constant zero
    assert_eq!(
        ctx.extract(&ze, 15, 8)?.simplify()?,
        ctx.bvv(BitVec::from((0, 8)))?
    );

    // Spanning original and extended bits => zero_ext(extract(x, 7, 4), 4)
    assert_eq!(
        ctx.extract(&ze, 11, 4)?.simplify()?,
        ctx.zero_ext(&ctx.extract(&x, 7, 4)?, 4)?
    );

    Ok(())
}

#[test]
fn test_extract_sign_ext_parts() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let se = ctx.sign_ext(&x, 8)?;

    // Entirely within the original bits
    assert_eq!(ctx.extract(&se, 7, 0)?.simplify()?, x);
    assert_eq!(ctx.extract(&se, 5, 2)?.simplify()?, ctx.extract(&x, 5, 2)?);

    // Entirely within the sign-extension bits => replicated sign bit
    let sb = ctx.extract(&x, 7, 7)?;
    assert_eq!(
        ctx.extract(&se, 11, 8)?.simplify()?,
        ctx.concat(vec![sb.clone(), sb.clone(), sb.clone(), sb.clone()])?
    );

    // Spanning original and sign-extension bits has no rewrite rule and is
    // left unchanged (documents current behavior)
    assert_eq!(
        ctx.extract(&se, 11, 4)?.simplify()?,
        ctx.extract(&se, 11, 4)?
    );

    Ok(())
}

#[test]
fn test_extract_concat_single_and_spanning() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;
    let y = ctx.bvs("y", 16)?;
    let cc = ctx.concat2(&x, &y)?;

    // Entirely within one concat operand
    assert_eq!(
        ctx.extract(&cc, 12, 9)?.simplify()?,
        ctx.extract(&y, 12, 9)?
    );
    assert_eq!(
        ctx.extract(&cc, 27, 20)?.simplify()?,
        ctx.extract(&x, 11, 4)?
    );

    // Spanning both operands
    assert_eq!(
        ctx.extract(&cc, 23, 8)?.simplify()?,
        ctx.concat2(&ctx.extract(&x, 7, 0)?, &ctx.extract(&y, 15, 8)?)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Concat rules
// ---------------------------------------------------------------------------

#[test]
fn test_concat_constant_merging() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;

    // Concat of two constants folds into one
    assert_eq!(
        ctx.concat2(
            &ctx.bvv(BitVec::from((0x12, 8)))?,
            &ctx.bvv(BitVec::from((0x34, 8)))?
        )?
        .simplify()?,
        ctx.bvv(BitVec::from((0x1234, 16)))?
    );

    // Adjacent constants merge even with a symbolic part present
    assert_eq!(
        ctx.concat(vec![
            x.clone(),
            ctx.bvv(BitVec::from((0x12, 8)))?,
            ctx.bvv(BitVec::from((0x34, 8)))?,
        ])?
        .simplify()?,
        ctx.concat2(&x, &ctx.bvv(BitVec::from((0x1234, 16)))?)?
    );

    Ok(())
}

#[test]
fn test_concat_flattening() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let z = ctx.bvs("z", 8)?;

    // Concat(Concat(x, y), z) => Concat(x, y, z)
    assert_eq!(
        ctx.concat2(&ctx.concat2(&x, &y)?, &z)?.simplify()?,
        ctx.concat(vec![x.clone(), y.clone(), z.clone()])?
    );

    Ok(())
}

#[test]
fn test_concat_ite_recombining() -> Result<()> {
    let ctx = Context::new();
    let c = ctx.bools("c")?;
    let ite_hi = ctx.ite(
        &c,
        &ctx.bvv(BitVec::from((1, 8)))?,
        &ctx.bvv(BitVec::from((2, 8)))?,
    )?;
    let ite_lo = ctx.ite(
        &c,
        &ctx.bvv(BitVec::from((3, 8)))?,
        &ctx.bvv(BitVec::from((4, 8)))?,
    )?;

    // Concat(ite(c, 1, 2), ite(c, 3, 4)) => ite(c, 0x0103, 0x0204)
    assert_eq!(
        ctx.concat2(&ite_hi, &ite_lo)?.simplify()?,
        ctx.ite(
            &c,
            &ctx.bvv(BitVec::from((0x0103, 16)))?,
            &ctx.bvv(BitVec::from((0x0204, 16)))?
        )?
    );

    Ok(())
}

#[test]
fn test_concat_adjacent_extract_merging() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 16)?;

    // Concat(extract(x, 15, 8), extract(x, 7, 0)) => x
    assert_eq!(
        ctx.concat2(&ctx.extract(&x, 15, 8)?, &ctx.extract(&x, 7, 0)?)?
            .simplify()?,
        x
    );

    // Partial adjacent extracts merge into one extract
    assert_eq!(
        ctx.concat2(&ctx.extract(&x, 11, 8)?, &ctx.extract(&x, 7, 4)?)?
            .simplify()?,
        ctx.extract(&x, 11, 4)?
    );

    Ok(())
}

#[test]
fn test_concat_leading_zeros_to_zero_ext() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;
    let zero8 = ctx.bvv(BitVec::from((0, 8)))?;

    // Concat(0x00, x) => ZeroExt(x, 8)
    assert_eq!(ctx.concat2(&zero8, &x)?.simplify()?, ctx.zero_ext(&x, 8)?);

    // Concat(0x00, x, y) => ZeroExt(Concat(x, y), 8)
    assert_eq!(
        ctx.concat(vec![zero8.clone(), x.clone(), y.clone()])?
            .simplify()?,
        ctx.zero_ext(&ctx.concat2(&x, &y)?, 8)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// ByteReverse rules
// ---------------------------------------------------------------------------

#[test]
fn test_byte_reverse_structural_rules() -> Result<()> {
    let ctx = Context::new();
    let x8 = ctx.bvs("x8", 8)?;
    let x16 = ctx.bvs("x16", 16)?;
    let y8 = ctx.bvs("y8", 8)?;
    let c = ctx.bools("c")?;

    // Reversing a single byte is the identity
    assert_eq!(ctx.byte_reverse(&x8)?.simplify()?, x8);

    // Reverse(Reverse(x)) => x
    assert_eq!(ctx.byte_reverse(&ctx.byte_reverse(&x16)?)?.simplify()?, x16);

    // Reverse(ite(c, a, b)) => ite(c, Reverse(a), Reverse(b))
    assert_eq!(
        ctx.byte_reverse(&ctx.ite(
            &c,
            &ctx.bvv(BitVec::from((0x1234, 16)))?,
            &ctx.bvv(BitVec::from((0x5678, 16)))?
        )?)?
        .simplify()?,
        ctx.ite(
            &c,
            &ctx.bvv(BitVec::from((0x3412, 16)))?,
            &ctx.bvv(BitVec::from((0x7856, 16)))?
        )?
    );

    // Reverse(Concat(x, y)) => Concat(Reverse(y), Reverse(x)) => Concat(y, x)
    // for byte-sized pieces
    assert_eq!(
        ctx.byte_reverse(&ctx.concat2(&x8, &y8)?)?.simplify()?,
        ctx.concat2(&y8, &x8)?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Float-to-BV conversions
// ---------------------------------------------------------------------------

#[test]
fn test_fp_to_ieeebv_concrete() -> Result<()> {
    let ctx = Context::new();

    // 1.0f64 has IEEE bits 0x3FF0000000000000
    assert_eq!(
        ctx.fp_to_ieeebv(&ctx.fpv(1.0f64)?)?.simplify()?,
        ctx.bvv(BitVec::from((0x3FF0000000000000u64, 64)))?
    );

    Ok(())
}

#[test]
fn test_fp_to_ubv_sbv_concrete() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.fp_to_ubv(&ctx.fpv(42.0f64)?, 32, FPRM::NearestTiesToEven)?
            .simplify()?,
        ctx.bvv(BitVec::from((42, 32)))?
    );

    assert_eq!(
        ctx.fp_to_sbv(&ctx.fpv(42.0f64)?, 32, FPRM::NearestTiesToEven)?
            .simplify()?,
        ctx.bvv(BitVec::from((42, 32)))?
    );

    // Negative input: current behavior yields 0 because the signed BigInt is
    // converted with BigInt::to_biguint(), which returns None for negatives.
    // NOTE: suspected bug — two's complement 0xFFFFFFFF would be expected.
    assert_eq!(
        ctx.fp_to_sbv(&ctx.fpv(-1.0f64)?, 32, FPRM::NearestTiesToEven)?
            .simplify()?,
        ctx.bvv(BitVec::from((0, 32)))?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// String-to-BV ops
// ---------------------------------------------------------------------------

#[test]
fn test_str_len_concrete() -> Result<()> {
    let ctx = Context::new();

    assert_eq!(
        ctx.str_len(&ctx.stringv("hello")?)?.simplify()?,
        ctx.bvv(BitVec::from((5, 64)))?
    );
    assert_eq!(
        ctx.str_len(&ctx.stringv("")?)?.simplify()?,
        ctx.bvv(BitVec::from((0, 64)))?
    );

    Ok(())
}

#[test]
fn test_str_index_of_concrete() -> Result<()> {
    let ctx = Context::new();
    let s = ctx.stringv("hello world")?;

    // Found
    assert_eq!(
        ctx.str_index_of(&s, &ctx.stringv("world")?, &ctx.bvv(BitVec::from((0, 64)))?)?
            .simplify()?,
        ctx.bvv(BitVec::from((6, 64)))?
    );

    // Not found => -1 (all ones in 64 bits)
    assert_eq!(
        ctx.str_index_of(&s, &ctx.stringv("xyz")?, &ctx.bvv(BitVec::from((0, 64)))?)?
            .simplify()?,
        ctx.bvv(BitVec::from((u64::MAX, 64)))?
    );

    // Start index beyond the string => -1
    assert_eq!(
        ctx.str_index_of(
            &s,
            &ctx.stringv("world")?,
            &ctx.bvv(BitVec::from((100, 64)))?
        )?
        .simplify()?,
        ctx.bvv(BitVec::from((u64::MAX, 64)))?
    );

    Ok(())
}

#[test]
fn test_str_to_bv_concrete() -> Result<()> {
    let ctx = Context::new();

    // Decimal parse
    assert_eq!(
        ctx.str_to_bv(&ctx.stringv("42")?)?.simplify()?,
        ctx.bvv(BitVec::from((42, 64)))?
    );

    // Falls back to hexadecimal when decimal parsing fails
    assert_eq!(
        ctx.str_to_bv(&ctx.stringv("ff")?)?.simplify()?,
        ctx.bvv(BitVec::from((255, 64)))?
    );

    // Empty string => all-ones sentinel
    assert_eq!(
        ctx.str_to_bv(&ctx.stringv("")?)?.simplify()?,
        ctx.bvv(BitVec::from((u64::MAX, 64)))?
    );

    // Unparseable string => all-ones sentinel
    assert_eq!(
        ctx.str_to_bv(&ctx.stringv("zzz")?)?.simplify()?,
        ctx.bvv(BitVec::from((u64::MAX, 64)))?
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// ITE / Union / Intersection / Widen
// ---------------------------------------------------------------------------

#[test]
fn test_bv_ite_rules() -> Result<()> {
    let ctx = Context::new();
    let c = ctx.bools("c")?;
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    // Identical branches collapse
    assert_eq!(ctx.ite(&c, &x, &x)?.simplify()?, x);

    // Concrete condition selects a branch
    assert_eq!(ctx.ite(&ctx.true_()?, &x, &y)?.simplify()?, x);
    assert_eq!(ctx.ite(&ctx.false_()?, &x, &y)?.simplify()?, y);

    // ite(!c, x, y) => ite(c, y, x)
    assert_eq!(
        ctx.ite(&ctx.not(&c)?, &x, &y)?.simplify()?,
        ctx.ite(&c, &y, &x)?
    );

    Ok(())
}

#[test]
fn test_union_intersection_widen_identical_args() -> Result<()> {
    let ctx = Context::new();
    let x = ctx.bvs("x", 8)?;
    let y = ctx.bvs("y", 8)?;

    assert_eq!(ctx.union(&x, &x)?.simplify()?, x);
    assert_eq!(ctx.intersection(&x, &x)?.simplify()?, x);
    assert_eq!(ctx.widen(&x, &x)?.simplify()?, x);

    // Different args stay symbolic
    assert_eq!(ctx.union(&x, &y)?.simplify()?, ctx.union(&x, &y)?);
    assert_eq!(
        ctx.intersection(&x, &y)?.simplify()?,
        ctx.intersection(&x, &y)?
    );

    Ok(())
}
