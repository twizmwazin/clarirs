use super::{BitVec, BitVecError};

use anyhow::Result;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use smallvec::SmallVec;

#[test]
fn test_leading_zeros() -> Result<(), BitVecError> {
    // Test all zeros
    let bv = BitVec::zeros(64);
    assert_eq!(bv.leading_zeros(), 64);

    // Test all ones (no leading zeros)
    let bv = BitVec::from_prim_with_size(0xFFu8, 8)?;
    assert_eq!(bv.leading_zeros(), 0);

    // Test single one at different positions
    let bv = BitVec::from_prim_with_size(0b00000001u8, 8)?;
    assert_eq!(bv.leading_zeros(), 7);
    let bv = BitVec::from_prim_with_size(0b00000100u8, 8)?;
    assert_eq!(bv.leading_zeros(), 5);
    let bv = BitVec::from_prim_with_size(0b10000000u8, 8)?;
    assert_eq!(bv.leading_zeros(), 0);

    // Test different widths
    let bv = BitVec::from_prim_with_size(0b00001111u8, 8)?;
    assert_eq!(bv.leading_zeros(), 4);
    let bv = BitVec::from_prim_with_size(0b0000111100001111u16, 16)?;
    assert_eq!(bv.leading_zeros(), 4);

    // Test zero-width vector
    let bv = BitVec::zeros(0);
    assert_eq!(bv.leading_zeros(), 0);

    // Test odd-sized vectors
    let bv = BitVec::from_prim_with_size(0b010u8, 3)?; // Only 3 bits: 010
    assert_eq!(bv.leading_zeros(), 1);

    // Test 72-bit vectors
    let mut words = SmallVec::new();
    words.push(0b1); // Single 1 in second word
    words.push(0);
    let bv = BitVec::new(words, 72)?;
    assert_eq!(bv.leading_zeros(), 71); // 64 zeros from first word + 7 zeros from second word before the 1

    let mut words = SmallVec::new();
    words.push(0);
    words.push(0b10000000); // 1 at MSB of second word
    let bv = BitVec::new(words, 72)?;
    assert_eq!(bv.leading_zeros(), 0); // 0 zeros before the 1

    Ok(())
}

#[test]
fn test_from_bigint() -> Result<(), BitVecError> {
    // Test positive values
    let value = BigInt::from(42i32);
    let bv = BitVec::from_bigint(&value, 32)?;
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 42);

    // Test zero
    let value = BigInt::zero();
    let bv = BitVec::from_bigint(&value, 32)?;
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 0);

    // Test negative values (2's complement representation)
    // -1 in 8-bit 2's complement is 11111111 (all ones)
    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0xFF);
    assert!(bv.is_all_ones());

    // -42 in 8-bit 2's complement is 256 - 42 = 214 (0xD6)
    let value = BigInt::from(-42i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0xD6);

    // -128 in 8-bit 2's complement is 10000000 (0x80)
    let value = BigInt::from(-128i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0x80);

    // Test different bit widths
    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint(&value, 16)?;
    assert_eq!(bv.len(), 16);
    assert_eq!(bv.to_u64().unwrap(), 0xFFFF);

    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint(&value, 32)?;
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 0xFFFFFFFF);

    // Test truncation with positive value
    let value = BigInt::from(256i32);
    let result = BitVec::from_bigint(&value, 8)?;
    assert_eq!(result.to_u64().unwrap(), 0); // 256 & 0xFF = 0

    // Test truncation with negative value
    let value = BigInt::from(-129i32);
    let result = BitVec::from_bigint(&value, 8)?;
    assert_eq!(result.to_u64().unwrap(), 127); // -129 mod 256 = 127 in two's complement

    Ok(())
}

#[test]
fn test_from_bigint_trunc() {
    // Test positive values
    let value = BigInt::from(42i32);
    let bv = BitVec::from_bigint_trunc(&value, 32);
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 42);

    // Test truncation of positive values
    let value = BigInt::from(0x12345678i32);
    let bv = BitVec::from_bigint_trunc(&value, 16); // Truncate to 16 bits
    assert_eq!(bv.len(), 16);
    assert_eq!(bv.to_u64().unwrap(), 0x5678); // Only lower 16 bits should remain

    // Test negative values (2's complement representation)
    // -1 in 8-bit 2's complement is 11111111 (all ones)
    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint_trunc(&value, 8);
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0xFF);
    assert!(bv.is_all_ones());

    // -42 in 8-bit 2's complement is 256 - 42 = 214 (0xD6)
    let value = BigInt::from(-42i32);
    let bv = BitVec::from_bigint_trunc(&value, 8);
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0xD6);

    // Test truncation of negative values
    let value = BigInt::from(-0x12345678i32);
    let bv = BitVec::from_bigint_trunc(&value, 16); // Truncate to 16 bits
    assert_eq!(bv.len(), 16);
    // In 2's complement, -0x12345678 truncated to 16 bits should be the 2's complement of 0x5678
    assert_eq!(bv.to_u64().unwrap(), 0xA988); // 2's complement of 0x5678 in 16 bits

    // Test different bit widths
    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint_trunc(&value, 16);
    assert_eq!(bv.len(), 16);
    assert_eq!(bv.to_u64().unwrap(), 0xFFFF);

    // Test zero
    let value = BigInt::zero();
    let bv = BitVec::from_bigint_trunc(&value, 32);
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 0);

    // Test with values larger than the specified width
    let value = BigInt::from(256i32);
    let bv = BitVec::from_bigint_trunc(&value, 8); // 256 doesn't fit in 8 bits
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0); // Should be truncated to 0

    let value = BigInt::from(257i32);
    let bv = BitVec::from_bigint_trunc(&value, 8); // 257 (0x101) truncated to 8 bits
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 1); // Should be truncated to 1
}

#[test]
fn test_from_biguint_trunc() {
    // Test values within bit width
    let value = BigUint::from(42u32);
    let bv = BitVec::from_biguint_trunc(&value, 32);
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 42);

    // Test truncation
    let value = BigUint::from(0x12345678u32);
    let bv = BitVec::from_biguint_trunc(&value, 16); // Truncate to 16 bits
    assert_eq!(bv.len(), 16);
    assert_eq!(bv.to_u64().unwrap(), 0x5678); // Only lower 16 bits should remain

    // Test different bit widths
    let value = BigUint::from(0xFFu32);
    let bv = BitVec::from_biguint_trunc(&value, 8);
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0xFF);

    // Test zero
    let value = BigUint::zero();
    let bv = BitVec::from_biguint_trunc(&value, 32);
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 0);

    // Test with values larger than the specified width
    let value = BigUint::from(256u32);
    let bv = BitVec::from_biguint_trunc(&value, 8); // 256 doesn't fit in 8 bits
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 0); // Should be truncated to 0

    let value = BigUint::from(257u32);
    let bv = BitVec::from_biguint_trunc(&value, 8); // 257 (0x101) truncated to 8 bits
    assert_eq!(bv.len(), 8);
    assert_eq!(bv.to_u64().unwrap(), 1); // Should be truncated to 1

    // Test with large values
    let value = (BigUint::from(1u32) << 64) - BigUint::from(1u32); // 2^64 - 1
    let bv = BitVec::from_biguint_trunc(&value, 32); // Truncate to 32 bits
    assert_eq!(bv.len(), 32);
    assert_eq!(bv.to_u64().unwrap(), 0xFFFFFFFF); // Should be all ones in 32 bits
}

#[test]
fn test_bigint_biguint_conversion() -> Result<(), BitVecError> {
    // Test conversion between BigInt and BitVec with 2's complement

    // Positive values should be the same in both representations
    let value = BigInt::from(42i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.to_u64().unwrap(), 42);

    // -1 in 8-bit 2's complement is 11111111 (all ones, or 255 unsigned)
    let value = BigInt::from(-1i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.to_u64().unwrap(), 0xFF);

    // -42 in 8-bit 2's complement is 256 - 42 = 214 (0xD6)
    let value = BigInt::from(-42i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv.to_u64().unwrap(), 0xD6);

    // Convert back to BigUint (should remain as 2's complement representation)
    let value = BigInt::from(-42i32);
    let bv = BitVec::from_bigint(&value, 8)?;
    let biguint: BigUint = bv.to_biguint();
    assert_eq!(biguint, BigUint::from(0xD6u32));

    // Test with different bit widths
    let value = BigInt::from(-42i32);

    // 8-bit: -42 = 214 (0xD6)
    let bv8 = BitVec::from_bigint(&value, 8)?;
    assert_eq!(bv8.to_u64().unwrap(), 0xD6);

    // 16-bit: -42 = 65494 (0xFFD6)
    let bv16 = BitVec::from_bigint(&value, 16)?;
    assert_eq!(bv16.to_u64().unwrap(), 0xFFD6);

    // 32-bit: -42 = 4294967254 (0xFFFFFFD6)
    let bv32 = BitVec::from_bigint(&value, 32)?;
    assert_eq!(bv32.to_u64().unwrap(), 0xFFFFFFD6);

    Ok(())
}

#[test]
fn test_valid_bv_from_length() {
    // Basic valid creation
    let bv = BitVec::from_prim_with_size(5u8, 8);
    let bv = bv.unwrap();
    assert_eq!(bv.length, 8);
    assert_eq!(bv.words[0], 5);

    // Creating a BitVec with a larger value and different size
    let bv = BitVec::from_prim_with_size(255u8, 8);
    let bv = bv.unwrap();
    assert_eq!(bv.length, 8);
    assert_eq!(bv.words[0], 255);

    // Creating a 16-bit BitVec from a u16
    let bv = BitVec::from_prim_with_size(1023u16, 16);
    let bv = bv.unwrap();
    assert_eq!(bv.length, 16);
    assert_eq!(bv.words[0], 1023);

    // Edge case - a zero value in a too-small size
    let result = BitVec::from_prim_with_size(0u8, 0);
    assert!(result.is_ok());
}

#[test]
fn test_invalid_bv_from_length() {
    // Value larger than bit width is truncated
    let bv = BitVec::from_prim_with_size(5u8, 1).unwrap();
    assert_eq!(bv.to_u64().unwrap(), 1); // 5 & 1 = 1

    // Value truncated to fit within bit width
    let bv = BitVec::from_prim_with_size(255u8, 4).unwrap();
    assert_eq!(bv.to_u64().unwrap(), 15); // 255 & 0xF = 15
}

#[test]
fn test_is_zero() -> Result<(), BitVecError> {
    // Test true case (all bits zero)
    let bv = BitVec::zeros(64);
    assert!(bv.is_zero());

    // Test false case (any bit one)
    let bv = BitVec::from_prim_with_size(1u64, 64)?;
    assert!(!bv.is_zero());
    let bv = BitVec::from_prim_with_size(1u64 << 63, 64)?; // Test highest bi?t
    assert!(!bv.is_zero());

    // Test different widths
    for width in [8, 16, 32] {
        let bv = BitVec::zeros(width);
        assert!(bv.is_zero());
        let bv = BitVec::from_prim_with_size(1u64, width)?;
        assert!(!bv.is_zero());
    }

    // Test zero-width vector
    let bv = BitVec::zeros(0);
    assert!(bv.is_zero());

    // Test single-bit vector
    let bv = BitVec::zeros(1);
    assert!(bv.is_zero());
    let bv = BitVec::from_prim_with_size(1u64, 1)?;
    assert!(!bv.is_zero());

    // Test odd-sized vectors
    let bv = BitVec::zeros(3);
    assert!(bv.is_zero());
    let bv = BitVec::from_prim_with_size(0b101u64, 3)?;
    assert!(!bv.is_zero());

    // Test 72-bit vectors
    let mut words = SmallVec::new();
    words.push(0);
    words.push(0);
    let bv = BitVec::new(words.clone(), 72)?;
    assert!(bv.is_zero());

    words[1] = 1; // Set a bit in the second word
    let bv = BitVec::new(words, 72)?;
    assert!(!bv.is_zero());

    Ok(())
}

#[test]
fn test_is_all_ones() -> Result<(), BitVecError> {
    // Test true case (all bits one)
    let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << 64) - 1u8), 64);
    assert!(bv.is_all_ones());

    // Test false case (any bit zero)
    let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << 64) - 2u8), 64); // All ones except last bit
    assert!(!bv.is_all_ones());
    let bv = BitVec::from_prim_with_size(0x7FFFFFFFFFFFFFFFu64, 64)?; // All ones except highest bit
    assert!(!bv.is_all_ones());

    // Test different widths
    for width in [8, 16, 32] {
        let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << width) - 1u8), width);
        assert!(bv.is_all_ones());
        let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << width) - 2u8), width);
        assert!(!bv.is_all_ones());
    }

    // Test zero-width vector
    let bv = BitVec::zeros(0);
    assert!(bv.is_all_ones()); // Empty bitvector should return true as there are no zero bits

    // Test single-bit vector
    let bv = BitVec::from_prim_with_size(1u64, 1)?;
    assert!(bv.is_all_ones());
    let bv = BitVec::from_prim_with_size(0u64, 1)?;
    assert!(!bv.is_all_ones());

    // Test odd-sized vectors
    let bv = BitVec::from_prim_with_size(0b111u64, 3)?;
    assert!(bv.is_all_ones());
    let bv = BitVec::from_prim_with_size(0b110u64, 3)?;
    assert!(!bv.is_all_ones());

    // Test 72-bit vectors
    let mut words = SmallVec::new();
    words.push(0xFFFFFFFFFFFFFFFF);
    words.push(0xFF); // All 72 bits set to 1
    let bv = BitVec::new(words.clone(), 72)?;
    assert!(bv.is_all_ones());

    words[1] = 0xFE; // Clear one bit in the second word
    let bv = BitVec::new(words, 72)?;
    assert!(!bv.is_all_ones());

    Ok(())
}

#[test]
fn test_reverse_bytes() -> Result<(), BitVecError> {
    // Test single byte
    let bv = BitVec::from_prim_with_size(0xA5u8, 8)?; // 10100101
    let reversed = bv.reverse_bytes()?;
    assert!(reversed.len() == 8);
    assert_eq!(reversed.to_u64().unwrap(), 0xA5); // Single byte should remain unchanged

    // Test multiple bytes
    let bv = BitVec::from_prim_with_size(0x1234u16, 16)?; // 0x12 0x34
    let reversed = bv.reverse_bytes()?;
    assert_eq!(reversed.to_u64().unwrap(), 0x3412); // Should be 0x34 0x12

    let bv = BitVec::from_prim_with_size(0x12345678u32, 32)?; // 0x12 0x34 0x56 0x78
    let reversed = bv.reverse_bytes()?;
    assert_eq!(reversed.to_u64().unwrap(), 0x78563412); // Should be 0x78 0x56 0x34 0x12

    // Test with non-byte-aligned width
    let bv = BitVec::from_prim_with_size(0b111100001111u16, 12)?; // Only use 12 bits
    assert!(bv.reverse_bytes().is_err()); // Should fail as width is not byte-aligned

    // Test zero-width vector
    let bv = BitVec::zeros(0);
    let reversed = bv.reverse_bytes()?;
    assert_eq!(reversed.len(), 0);
    assert!(reversed.is_zero());

    // Test odd number of bits
    let bv = BitVec::from_prim_with_size(0b10110u8, 5)?; // 5 bits
    assert!(bv.reverse_bytes().is_err()); // Should fail as width is not byte-aligned

    // Test patterns that would expose endianness issues
    let bv = BitVec::from_prim_with_size(0x0123456789ABCDEFu64, 64)?;
    let reversed = bv.reverse_bytes()?;
    assert_eq!(reversed.to_u64().unwrap(), 0xEFCDAB8967452301);

    // Test 72-bit vectors (9 bytes)
    let mut words = SmallVec::new();
    words.push(0x0123456789ABCDEFu64); // First 8 bytes
    words.push(0xAB); // Last byte
    let bv = BitVec::new(words, 72)?;
    let reversed = bv.reverse_bytes()?;

    // After reversal:
    // Original: [AB] [01 23 45 67 89 AB CD EF]
    // Reversed: [EF] [CD AB 89 67 45 23 01 AB]
    let result_words = reversed.words;
    assert_eq!(result_words[0], 0xCDAB8967452301AB);
    assert_eq!(result_words[1], 0xEF);

    Ok(())
}
