use super::super::*;

#[test]
fn test_add() {
    // Basic addition
    let a = BitVec::from(42u64);
    let b = BitVec::from(58u64);
    let result = a + b;
    assert_eq!(result.to_u64().unwrap(), 100);

    // Addition with overflow within the same bitwidth
    let a = BitVec::from(0xFFFFFFFFu32);
    let b = BitVec::from(1u32);
    let result = a + b;
    assert_eq!(result.len(), 32);
    assert_eq!(result.to_u64().unwrap(), 0);

    // Addition with different bit widths
    let a = BitVec::from_prim_with_size(42u64, 32);
    let b = BitVec::from_prim_with_size(58u64, 32);
    let result = a + b;
    assert_eq!(result.to_u64().unwrap(), 100);
}

#[test]
fn test_sub() {
    // Basic subtraction
    let a = BitVec::from(100u64);
    let b = BitVec::from(58u64);
    let result = a - b;
    assert_eq!(result.to_u64().unwrap(), 42);

    // Subtraction with underflow
    let a = BitVec::from(0u64);
    let b = BitVec::from(1u64);
    let result = a - b;
    assert_eq!(result.to_u64().unwrap(), u64::MAX);

    // Subtraction with different bit widths
    let a = BitVec::from_prim_with_size(100u64, 32);
    let b = BitVec::from_prim_with_size(58u64, 32);
    let result = a - b;
    assert_eq!(result.to_u64().unwrap(), 42);
}

#[test]
fn test_mul() {
    // Basic multiplication
    let a = BitVec::from(7u64);
    let b = BitVec::from(6u64);
    let result = a * b;
    assert_eq!(result.to_u64().unwrap(), 42);

    // Multiplication with overflow
    let a = BitVec::from(0xFFFFFFFFu32);
    let b = BitVec::from(2u32);
    let result = a * b;
    assert_eq!(result.to_u64().unwrap(), 0xFFFFFFFE);

    // Multiplication with different bit widths
    let a = BitVec::from_prim_with_size(7u64, 32);
    let b = BitVec::from_prim_with_size(6u64, 32);
    let result = a * b;
    assert_eq!(result.to_u64().unwrap(), 42);
}

#[test]
fn test_div() {
    // Basic division
    let a = BitVec::from(42u64);
    let b = BitVec::from(6u64);
    let result = a / b;
    assert_eq!(result.to_u64().unwrap(), 7);

    // Division with remainder
    let a = BitVec::from(100u64);
    let b = BitVec::from(30u64);
    let result = a / b;
    assert_eq!(result.to_u64().unwrap(), 3);

    // Division with different bit widths
    let a = BitVec::from_prim_with_size(100u64, 32);
    let b = BitVec::from_prim_with_size(30u64, 32);
    let result = a / b;
    assert_eq!(result.to_u64().unwrap(), 3);

    // TODO: DBZ error handling
    // // Division by zero (should return the dividend)
    // let a = BitVec::from(42u64);
    // let b = BitVec::from(0u64);
    // let result = a / b;
    // assert_eq!(result.to_u64().unwrap(), 42);
}

#[test]
fn test_rem() {
    // Basic remainder
    let a = BitVec::from(42u64);
    let b = BitVec::from(6u64);
    let result = a % b;
    assert_eq!(result.to_u64().unwrap(), 0);

    // Remainder with non-zero result
    let a = BitVec::from(100u64);
    let b = BitVec::from(30u64);
    let result = a % b;
    assert_eq!(result.to_u64().unwrap(), 10);

    // Remainder with different bit widths
    let a = BitVec::from_prim_with_size(100u64, 32);
    let b = BitVec::from_prim_with_size(30u64, 32);
    let result = a % b;
    assert_eq!(result.to_u64().unwrap(), 10);

    // TODO: DBZ error handling
    // // Remainder by zero (should return the dividend)
    // let a = BitVec::from(42u64);
    // let b = BitVec::from(0u64);
    // let result = a % b;
    // assert_eq!(result.to_u64().unwrap(), 42);
}

#[test]
fn test_signed_arithmetic() {
    let neg_42 = BitVec::from(-42i64);
    let pos_6 = BitVec::from(6u64);

    // Signed division should give -7
    let result = neg_42.sdiv(&pos_6);
    assert!(result.sign()); // Should be negative
    assert_eq!(result, BitVec::from(-7i64));

    // Create -100 in 64-bit two's complement
    let neg_100 = BitVec::from(-100i64);
    let pos_30 = BitVec::from_prim_with_size(30u64, 64);

    // Signed remainder should give -10
    let result = neg_100.srem(&pos_30);
    assert!(result.sign()); // Should be negative
    assert_eq!(result, BitVec::from(-10i64));

    // Test division with different signs
    let pos_100 = BitVec::from_prim_with_size(100u64, 64);
    let neg_30 = BitVec::from(-30i64);

    // Signed division should give -3
    let result = pos_100.sdiv(&neg_30);
    assert!(result.sign()); // Should be negative
    assert_eq!(result, BitVec::from(-3i64));
}

#[test]
fn test_power() {
    // Basic power operation
    let base = BitVec::from(2u64);
    let exp = BitVec::from(3u64);
    let result = base.pow(&exp).unwrap();
    assert_eq!(result.to_u64().unwrap(), 8);

    // Power with zero exponent
    let base = BitVec::from(42u64);
    let exp = BitVec::from(0u64);
    let result = base.pow(&exp).unwrap();
    assert_eq!(result.to_u64().unwrap(), 1);

    // Power with one exponent
    let base = BitVec::from(42u64);
    let exp = BitVec::from(1u64);
    let result = base.pow(&exp).unwrap();
    assert_eq!(result.to_u64().unwrap(), 42);

    // Power with different bit widths
    let base = BitVec::from_prim_with_size(2u64, 32);
    let exp = BitVec::from_prim_with_size(4u64, 32);
    let result = base.pow(&exp).unwrap();
    assert_eq!(result.to_u64().unwrap(), 16);
}
