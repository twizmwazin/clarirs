#[cfg(test)]
mod tests {
    use crate::bitvec::BitVec;
    use anyhow::Result;
    use num_bigint::BigUint;
    use smallvec::SmallVec;

    #[test]
    fn test_leading_zeros() {
        // Test all zeros
        let bv = BitVec::zeros(64);
        assert_eq!(bv.leading_zeros(), 64);

        // Test all ones (no leading zeros)
        let bv = BitVec::from_prim_with_size(0xFFu8, 8);
        assert_eq!(bv.leading_zeros(), 0);

        // Test single one at different positions
        let bv = BitVec::from_prim_with_size(0b00000001u8, 8);
        assert_eq!(bv.leading_zeros(), 7);
        let bv = BitVec::from_prim_with_size(0b00000100u8, 8);
        assert_eq!(bv.leading_zeros(), 5);
        let bv = BitVec::from_prim_with_size(0b10000000u8, 8);
        assert_eq!(bv.leading_zeros(), 0);

        // Test different widths
        let bv = BitVec::from_prim_with_size(0b00001111u8, 8);
        assert_eq!(bv.leading_zeros(), 4);
        let bv = BitVec::from_prim_with_size(0b0000111100001111u16, 16);
        assert_eq!(bv.leading_zeros(), 4);

        // Test zero-width vector
        let bv = BitVec::zeros(0);
        assert_eq!(bv.leading_zeros(), 0);

        // Test odd-sized vectors
        let bv = BitVec::from_prim_with_size(0b010u8, 3); // Only 3 bits: 010
        assert_eq!(bv.leading_zeros(), 1);

        // Test 72-bit vectors
        let mut words = SmallVec::new();
        words.push(0b1); // Single 1 in second word
        words.push(0);
        let bv = BitVec::new(words, 72);
        assert_eq!(bv.leading_zeros(), 71); // 64 zeros from first word + 7 zeros from second word before the 1

        let mut words = SmallVec::new();
        words.push(0);
        words.push(0b10000000); // 1 at MSB of second word
        let bv = BitVec::new(words, 72);
        assert_eq!(bv.leading_zeros(), 0); // 0 zeros before the 1
    }

    #[test]
    fn test_is_zero() {
        // Test true case (all bits zero)
        let bv = BitVec::zeros(64);
        assert!(bv.is_zero());

        // Test false case (any bit one)
        let bv = BitVec::from_prim_with_size(1u64, 64);
        assert!(!bv.is_zero());
        let bv = BitVec::from_prim_with_size(1u64 << 63, 64); // Test highest bit
        assert!(!bv.is_zero());

        // Test different widths
        for width in [8, 16, 32] {
            let bv = BitVec::zeros(width);
            assert!(bv.is_zero());
            let bv = BitVec::from_prim_with_size(1u64, width);
            assert!(!bv.is_zero());
        }

        // Test zero-width vector
        let bv = BitVec::zeros(0);
        assert!(bv.is_zero());

        // Test single-bit vector
        let bv = BitVec::zeros(1);
        assert!(bv.is_zero());
        let bv = BitVec::from_prim_with_size(1u64, 1);
        assert!(!bv.is_zero());

        // Test odd-sized vectors
        let bv = BitVec::zeros(3);
        assert!(bv.is_zero());
        let bv = BitVec::from_prim_with_size(0b101u64, 3);
        assert!(!bv.is_zero());

        // Test 72-bit vectors
        let mut words = SmallVec::new();
        words.push(0);
        words.push(0);
        let bv = BitVec::new(words.clone(), 72);
        assert!(bv.is_zero());

        words[1] = 1; // Set a bit in the second word
        let bv = BitVec::new(words, 72);
        assert!(!bv.is_zero());
    }

    #[test]
    fn test_is_all_ones() {
        // Test true case (all bits one)
        let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << 64) - 1u8), 64);
        assert!(bv.is_all_ones());

        // Test false case (any bit zero)
        let bv = BitVec::from_biguint_trunc(&((BigUint::from(1u8) << 64) - 2u8), 64); // All ones except last bit
        assert!(!bv.is_all_ones());
        let bv = BitVec::from_prim_with_size(0x7FFFFFFFFFFFFFFFu64, 64); // All ones except highest bit
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
        let bv = BitVec::from_prim_with_size(1u64, 1);
        assert!(bv.is_all_ones());
        let bv = BitVec::from_prim_with_size(0u64, 1);
        assert!(!bv.is_all_ones());

        // Test odd-sized vectors
        let bv = BitVec::from_prim_with_size(0b111u64, 3);
        assert!(bv.is_all_ones());
        let bv = BitVec::from_prim_with_size(0b110u64, 3);
        assert!(!bv.is_all_ones());

        // Test 72-bit vectors
        let mut words = SmallVec::new();
        words.push(0xFFFFFFFFFFFFFFFF);
        words.push(0xFF); // All 72 bits set to 1
        let bv = BitVec::new(words.clone(), 72);
        assert!(bv.is_all_ones());

        words[1] = 0xFE; // Clear one bit in the second word
        let bv = BitVec::new(words, 72);
        assert!(!bv.is_all_ones());
    }

    #[test]
    fn test_reverse_bytes() -> Result<()> {
        // Test single byte
        let bv = BitVec::from_prim_with_size(0xA5u8, 8); // 10100101
        let reversed = bv.reverse_bytes()?;
        assert!(reversed.len() == 8);
        assert_eq!(reversed.to_u64().unwrap(), 0xA5); // Single byte should remain unchanged

        // Test multiple bytes
        let bv = BitVec::from_prim_with_size(0x1234u16, 16); // 0x12 0x34
        let reversed = bv.reverse_bytes()?;
        assert_eq!(reversed.to_u64().unwrap(), 0x3412); // Should be 0x34 0x12

        let bv = BitVec::from_prim_with_size(0x12345678u32, 32); // 0x12 0x34 0x56 0x78
        let reversed = bv.reverse_bytes()?;
        assert_eq!(reversed.to_u64().unwrap(), 0x78563412); // Should be 0x78 0x56 0x34 0x12

        // Test with non-byte-aligned width
        let bv = BitVec::from_prim_with_size(0b1010111100001111u16, 12); // Only use 12 bits
        assert!(bv.reverse_bytes().is_err()); // Should fail as width is not byte-aligned

        // Test zero-width vector
        let bv = BitVec::zeros(0);
        let reversed = bv.reverse_bytes()?;
        assert_eq!(reversed.len(), 0);
        assert!(reversed.is_zero());

        // Test odd number of bits
        let bv = BitVec::from_prim_with_size(0b10110u8, 5); // 5 bits
        assert!(bv.reverse_bytes().is_err()); // Should fail as width is not byte-aligned

        // Test patterns that would expose endianness issues
        let bv = BitVec::from_prim_with_size(0x0123456789ABCDEFu64, 64);
        let reversed = bv.reverse_bytes()?;
        assert_eq!(reversed.to_u64().unwrap(), 0xEFCDAB8967452301);

        // Test 72-bit vectors (9 bytes)
        let mut words = SmallVec::new();
        words.push(0x0123456789ABCDEFu64); // First 8 bytes
        words.push(0xAB); // Last byte
        let bv = BitVec::new(words, 72);
        let reversed = bv.reverse_bytes()?;

        // After reversal:
        // Original: [AB] [01 23 45 67 89 AB CD EF]
        // Reversed: [EF] [CD AB 89 67 45 23 01 AB]
        let result_words = reversed.words;
        assert_eq!(result_words[0], 0xCDAB8967452301AB);
        assert_eq!(result_words[1], 0xEF);

        Ok(())
    }
}
