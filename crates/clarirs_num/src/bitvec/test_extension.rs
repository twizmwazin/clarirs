#[cfg(test)]
mod tests {
    use crate::bitvec::BitVec;

    #[test]
    fn test_concat() {
        // Test basic concatenation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4);
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv1.concat(&bv2);
        assert_eq!(result.to_u64().unwrap(), 0b11001010);
        assert_eq!(result.len(), 8);

        // Test concatenation with zero
        let bv1 = BitVec::from_prim_with_size(0b1111u8, 4);
        let bv2 = BitVec::from_prim_with_size(0b0000u8, 4);
        let result = bv1.concat(&bv2);
        assert_eq!(result.to_u64().unwrap(), 0b11110000);

        // Test concatenation of different widths
        let bv1 = BitVec::from_prim_with_size(0b111u8, 3);
        let bv2 = BitVec::from_prim_with_size(0b10u8, 2);
        let result = bv1.concat(&bv2);
        assert_eq!(result.to_u64().unwrap(), 0b11110);
        assert_eq!(result.len(), 5);

        // Test concatenation of single-bit vectors
        let bv1 = BitVec::from_prim_with_size(1u8, 1);
        let bv2 = BitVec::from_prim_with_size(0u8, 1);
        let result = bv1.concat(&bv2);
        assert_eq!(result.to_u64().unwrap(), 0b10);
        assert_eq!(result.len(), 2);

        // Test concatenation of odd-sized vectors
        let bv1 = BitVec::from_prim_with_size(0b10101u8, 5);
        let bv2 = BitVec::from_prim_with_size(0b111u8, 3);
        let result = bv1.concat(&bv2);
        assert_eq!(result.to_u64().unwrap(), 0b10101111);
        assert_eq!(result.len(), 8);

        // Test concatenation producing 72-bit vectors
        let bv1 = BitVec::from_prim_with_size(u64::MAX, 64);
        let bv2 = BitVec::from_prim_with_size(0b11111111u8, 8);
        let result = bv1.concat(&bv2);
        assert_eq!(result.len(), 72);
    }

    #[test]
    fn test_extract() {
        // Test basic extraction
        let bv = BitVec::from_prim_with_size(0b11001010u8, 8);
        let result = bv.extract(2, 5).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b0010);
        assert_eq!(result.len(), 4);

        // Test extraction of entire vector
        let bv = BitVec::from_prim_with_size(0b1111u8, 4);
        let result = bv.extract(0, 3).unwrap();
        assert_eq!(result.to_u64().unwrap() & 0b1111, 0b1111); // Mask to 4 bits
        assert_eq!(result.len(), 4);

        // Test extraction of single bit
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.extract(1, 1).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1);
        assert_eq!(result.len(), 1);

        // Test extraction with invalid range (should error)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        assert!(bv.extract(2, 1).is_err()); // from > to
        assert!(bv.extract(0, 4).is_err()); // to >= len

        // Test extraction from different widths
        let bv = BitVec::from_prim_with_size(0b110011u8, 6);
        let result = bv.extract(1, 4).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1001);
        assert_eq!(result.len(), 4);

        // Test extraction from odd-sized vectors
        let bv = BitVec::from_prim_with_size(0b10101u8, 5);
        let result = bv.extract(1, 3).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b010);
        assert_eq!(result.len(), 3);

        // Test extraction from 72-bit vectors
        let mut bv = BitVec::from_prim_with_size(u64::MAX, 64);
        bv = bv.concat(&BitVec::from_prim_with_size(0b11111111u8, 8));
        let result = bv.extract(60, 67).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b11111111);
        assert_eq!(result.len(), 8);
    }

    #[test]
    fn test_zero_extend() {
        // Test extending positive number
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.zero_extend(4);
        assert_eq!(result.to_u64().unwrap(), 0b00001010);
        assert_eq!(result.len(), 8);

        // Test extending zero
        let bv = BitVec::from_prim_with_size(0u8, 4);
        let result = bv.zero_extend(4);
        assert_eq!(result.to_u64().unwrap(), 0);
        assert_eq!(result.len(), 8);

        // Test extending to same width (no change)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.zero_extend(0);
        assert_eq!(result.to_u64().unwrap(), 0b1010);
        assert_eq!(result.len(), 4);

        // Test extending from odd-sized vector
        let bv = BitVec::from_prim_with_size(0b101u8, 3);
        let result = bv.zero_extend(5);
        assert_eq!(result.to_u64().unwrap(), 0b00000101);
        assert_eq!(result.len(), 8);

        // Test extending single-bit vector
        let bv = BitVec::from_prim_with_size(1u8, 1);
        let result = bv.zero_extend(7);
        assert_eq!(result.to_u64().unwrap(), 0b00000001);
        assert_eq!(result.len(), 8);

        // Test extending to 72-bit vectors
        let bv = BitVec::from_prim_with_size(0xFFFFFFFFu32, 32);
        let result = bv.zero_extend(40);
        assert_eq!(result.len(), 72);
    }

    #[test]
    fn test_sign_extend() {
        // Test extending positive number
        let bv = BitVec::from_prim_with_size(0b0010u8, 4);
        let result = bv.sign_extend(4);
        assert_eq!(result.to_u64().unwrap(), 0b00000010);
        assert_eq!(result.len(), 8);

        // Test extending negative number
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.sign_extend(4);
        assert_eq!(result.to_u64().unwrap(), 0b11111010);
        assert_eq!(result.len(), 8);

        // Test extending zero
        let bv = BitVec::from_prim_with_size(0u8, 4);
        let result = bv.sign_extend(4);
        assert_eq!(result.to_u64().unwrap(), 0);
        assert_eq!(result.len(), 8);

        // Test extending to same width (no change)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4);
        let result = bv.sign_extend(0);
        assert_eq!(result.to_u64().unwrap(), 0b1010);
        assert_eq!(result.len(), 4);

        // Test extending from odd-sized vector
        let bv = BitVec::from_prim_with_size(0b101u8, 3); // 101 is negative in 3 bits
        let result = bv.sign_extend(5);
        assert_eq!(result.to_u64().unwrap(), 0b11111101); // Sign extended to 8 bits
        assert_eq!(result.len(), 8);

        // Test extending single-bit vector
        let bv = BitVec::from_prim_with_size(1u8, 1);
        let result = bv.sign_extend(7);
        assert_eq!(result.to_u64().unwrap(), 0b11111111);
        assert_eq!(result.len(), 8);

        // Test extending to 72-bit vectors
        let bv = BitVec::from_prim_with_size(0xFFFFFFFFu32, 32);
        let result = bv.sign_extend(40);
        assert_eq!(result.len(), 72);
    }
}
