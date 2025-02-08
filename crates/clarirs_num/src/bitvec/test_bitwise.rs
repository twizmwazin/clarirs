#[cfg(test)]
mod tests {
    use crate::bitvec::BitVec;

    #[test]
    fn test_not() {
        // Test 8-bit NOT
        let bv = BitVec::from_prim_with_size(0b10101010u8, 8);
        let result = !bv;
        assert_eq!(result.to_u64().unwrap(), 0b01010101);

        // Test with non-byte aligned length
        let bv = BitVec::from_prim_with_size(0b101u8, 3);
        let result = !bv;
        assert_eq!(result.to_u64().unwrap(), 0b010);

        // Test with multiple words
        let bv = BitVec::from_prim_with_size(u64::MAX, 64);
        let result = !bv;
        assert_eq!(result.to_u64().unwrap(), 0);
    }

    #[test]
    fn test_neg() {
        // Negation should be equivalent to NOT
        let bv = BitVec::from_prim_with_size(0b10101010u8, 8);
        let neg_result = -bv.clone();
        let not_result = !bv;
        assert_eq!(neg_result, not_result);
    }

    #[test]
    fn test_bitand() {
        // Test basic AND operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4);
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv1 & bv2;
        assert_eq!(result.to_u64().unwrap(), 0b1000);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11111111u8, 8);
        let bv2 = BitVec::from_prim_with_size(0b10101010u8, 8);
        let result = bv1 & bv2;
        assert_eq!(result.to_u64().unwrap(), 0b10101010);
    }

    #[test]
    fn test_bitor() {
        // Test basic OR operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4);
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv1 | bv2;
        assert_eq!(result.to_u64().unwrap(), 0b1110);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11110000u8, 8);
        let bv2 = BitVec::from_prim_with_size(0b00001111u8, 8);
        let result = bv1 | bv2;
        assert_eq!(result.to_u64().unwrap(), 0b11111111);
    }

    #[test]
    fn test_bitxor() {
        // Test basic XOR operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4);
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv1 ^ bv2;
        assert_eq!(result.to_u64().unwrap(), 0b0110);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11111111u8, 8);
        let bv2 = BitVec::from_prim_with_size(0b10101010u8, 8);
        let result = bv1 ^ bv2;
        assert_eq!(result.to_u64().unwrap(), 0b01010101);
    }

    #[test]
    fn test_shl() {
        // Test basic left shift
        let bv = BitVec::from_prim_with_size(0b1010u8, 8);
        let result = bv << 2;
        assert_eq!(result.to_u64().unwrap(), 0b101000);

        // Test shift with carry across word boundaries
        let bv = BitVec::from_prim_with_size(0b1u8, 64);
        let result = bv << 63;
        assert_eq!(result.to_u64().unwrap(), 1u64 << 63);

        // Test shift beyond bit length
        let bv = BitVec::from_prim_with_size(0b1010u8, 8);
        let result = bv << 4;
        assert_eq!(result.to_u64().unwrap(), 0b10100000);
    }

    #[test]
    fn test_shr() {
        // Test basic right shift
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv >> 2;
        assert_eq!(result.to_u64().unwrap(), 0b10);

        // Test shift with carry across word boundaries
        let bv = BitVec::from_prim_with_size(1u64 << 63, 64);
        let result = bv >> 63;
        assert_eq!(result.to_u64().unwrap(), 1);

        // Test shift that results in all zeros
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv >> 4;
        assert_eq!(result.to_u64().unwrap(), 0);
    }

    #[test]
    fn test_rotate_left() {
        // Test basic rotation
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_left(1).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        // Test full rotation (should be same as original)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_left(4).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1010);

        // Test rotation with amount larger than length
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_left(5).unwrap(); // Same as rotating left by 1
        assert_eq!(result.to_u64().unwrap(), 0b0101);
    }

    #[test]
    fn test_rotate_right() {
        // Test basic rotation
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_right(1).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        // Test full rotation (should be same as original)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_right(4).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1010);

        // Test rotation with amount larger than length
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.rotate_right(5).unwrap(); // Same as rotating right by 1
        assert_eq!(result.to_u64().unwrap(), 0b0101);
    }
}
