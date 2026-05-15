use std::ops::{BitAnd, BitOr, BitXor, Not, Shl, Shr};

use smallvec::SmallVec;

use super::{BitVec, BitVecError};

impl Not for BitVec {
    type Output = Result<Self, BitVecError>;

    fn not(self) -> Self::Output {
        let mut new_bv: SmallVec<[u64; 1]> = self.words.iter().map(|w| !w).collect();
        if !self.length.is_multiple_of(64)
            && let Some(w) = new_bv.last_mut()
        {
            *w &= self.final_word_mask();
        }
        BitVec::new(new_bv, self.length)
    }
}

impl BitAnd for BitVec {
    type Output = Result<Self, BitVecError>;

    fn bitand(self, rhs: Self) -> Self::Output {
        let new_bv = self
            .words
            .iter()
            .zip(rhs.words.iter())
            .map(|(l, r)| l & r)
            .collect();
        BitVec::new(new_bv, self.length)
    }
}

impl BitOr for BitVec {
    type Output = Result<Self, BitVecError>;

    fn bitor(self, rhs: Self) -> Self::Output {
        let new_bv = self
            .words
            .iter()
            .zip(rhs.words.iter())
            .map(|(l, r)| l | r)
            .collect();
        BitVec::new(new_bv, self.length)
    }
}

impl BitXor for BitVec {
    type Output = Result<Self, BitVecError>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let new_bv = self
            .words
            .iter()
            .zip(rhs.words.iter())
            .map(|(l, r)| l ^ r)
            .collect();
        BitVec::new(new_bv, self.length)
    }
}

impl Shl<u32> for BitVec {
    type Output = Result<Self, BitVecError>;

    fn shl(self, rhs: u32) -> Self::Output {
        let bit_length = self.length;
        if rhs >= bit_length {
            return BitVec::new(SmallVec::new(), bit_length);
        }

        let word_shift = (rhs / 64) as usize;
        let bit_shift = rhs % 64;
        let num_words = self.words.len();
        let mut result: SmallVec<[u64; 1]> = SmallVec::with_capacity(num_words);

        for _ in 0..word_shift {
            result.push(0);
        }

        if bit_shift == 0 {
            for i in 0..(num_words - word_shift) {
                result.push(self.words[i]);
            }
        } else {
            let mut carry = 0u64;
            for i in 0..(num_words - word_shift) {
                let w = self.words[i];
                result.push((w << bit_shift) | carry);
                carry = w >> (64 - bit_shift);
            }
        }

        BitVec::new(result, bit_length)
    }
}

impl Shr<u32> for BitVec {
    type Output = Result<Self, BitVecError>;

    fn shr(self, rhs: u32) -> Self::Output {
        let bit_length = self.length;
        if rhs >= bit_length {
            return BitVec::new(SmallVec::new(), bit_length);
        }

        let word_shift = (rhs / 64) as usize;
        let bit_shift = rhs % 64;
        let num_words = self.words.len();
        let mut result: SmallVec<[u64; 1]> = smallvec::smallvec![0u64; num_words];

        if bit_shift == 0 {
            for i in 0..(num_words - word_shift) {
                result[i] = self.words[i + word_shift];
            }
        } else {
            let mut carry = 0u64;
            for i in (0..(num_words - word_shift)).rev() {
                let w = self.words[i + word_shift];
                result[i] = (w >> bit_shift) | carry;
                carry = w << (64 - bit_shift);
            }
        }

        BitVec::new(result, bit_length)
    }
}

impl BitVec {
    pub fn rotate_left(&self, rotate_amount: u32) -> Result<Self, BitVecError> {
        use num_bigint::BigUint;
        use num_traits::One;

        let rotate = rotate_amount % self.len();
        let bit_length = self.len();
        let value_biguint = self.to_biguint();
        let mask = (BigUint::one() << bit_length) - BigUint::one();

        let left_shifted = (&value_biguint << rotate) & &mask;
        let right_shifted = &value_biguint >> (bit_length - rotate);
        let rotated_biguint = left_shifted | right_shifted;

        BitVec::from_biguint(&rotated_biguint, bit_length)
    }

    pub fn rotate_right(&self, rotate_amount: u32) -> Result<Self, BitVecError> {
        use num_bigint::BigUint;
        use num_traits::One;

        let rotate = rotate_amount % self.len();
        let bit_length = self.len();
        let value_biguint = self.to_biguint();
        let mask = (BigUint::one() << bit_length) - BigUint::one();

        let right_shifted = &value_biguint >> rotate;
        let left_shifted = (&value_biguint << (bit_length - rotate)) & &mask;
        let rotated_biguint = (right_shifted | left_shifted) & &mask;

        BitVec::from_biguint(&rotated_biguint, bit_length)
    }
}

#[cfg(test)]
mod tests {
    use super::{BitVec, BitVecError};

    #[test]
    fn test_not() -> Result<(), BitVecError> {
        // Test 8-bit NOT
        let bv = BitVec::from_prim_with_size(0b10101010u8, 8)?;
        let result = (!bv)?;
        assert_eq!(result.to_u64().unwrap(), 0b01010101);

        // Test with non-byte aligned length
        let bv = BitVec::from_prim_with_size(0b101u8, 3)?;
        let result = (!bv)?;
        assert_eq!(result.to_u64().unwrap(), 0b010);

        // Test with multiple words
        let bv = BitVec::from_prim_with_size(u64::MAX, 64)?;
        let result = (!bv)?;
        assert_eq!(result.to_u64().unwrap(), 0);

        Ok(())
    }

    #[test]
    fn test_neg() -> Result<(), BitVecError> {
        // Arithmatic negation
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (!bv)?;
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        Ok(())
    }

    #[test]
    fn test_bitand() -> Result<(), BitVecError> {
        // Test basic AND operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4)?;
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (bv1 & bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b1000);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11111111u8, 8)?;
        let bv2 = BitVec::from_prim_with_size(0b10101010u8, 8)?;
        let result = (bv1 & bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b10101010);

        Ok(())
    }

    #[test]
    fn test_bitor() -> Result<(), BitVecError> {
        // Test basic OR operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4)?;
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (bv1 | bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b1110);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11110000u8, 8)?;
        let bv2 = BitVec::from_prim_with_size(0b00001111u8, 8)?;
        let result = (bv1 | bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b11111111);

        Ok(())
    }

    #[test]
    fn test_bitxor() -> Result<(), BitVecError> {
        // Test basic XOR operation
        let bv1 = BitVec::from_prim_with_size(0b1100u8, 4)?;
        let bv2 = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (bv1 ^ bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b0110);

        // Test with different patterns
        let bv1 = BitVec::from_prim_with_size(0b11111111u8, 8)?;
        let bv2 = BitVec::from_prim_with_size(0b10101010u8, 8)?;
        let result = (bv1 ^ bv2)?;
        assert_eq!(result.to_u64().unwrap(), 0b01010101);

        Ok(())
    }

    #[test]
    fn test_shl() -> Result<(), BitVecError> {
        // Test basic left shift
        let bv = BitVec::from_prim_with_size(0b1010u8, 8)?;
        let result = (bv << 2)?;
        assert_eq!(result.to_u64().unwrap(), 0b101000);

        // Test shift with carry across word boundaries
        let bv = BitVec::from_prim_with_size(0b1u8, 64)?;
        let result = (bv << 63)?;
        assert_eq!(result.to_u64().unwrap(), 1u64 << 63);

        // Test shift beyond bit length
        let bv = BitVec::from_prim_with_size(0b1010u8, 8)?;
        let result = (bv << 4)?;
        assert_eq!(result.to_u64().unwrap(), 0b10100000);

        // Shift by 0 must not panic (previously triggered UB via `w >> 64`)
        let bv = BitVec::from_prim_with_size(0b1011u8, 8)?;
        let result = (bv << 0)?;
        assert_eq!(result.to_u64().unwrap(), 0b1011);

        // Shift by >= length must yield zero (previously UB / wrong)
        let bv = BitVec::from_prim_with_size(0b1011u8, 8)?;
        let result = (bv << 8)?;
        assert_eq!(result.to_u64().unwrap(), 0);
        let bv = BitVec::from_prim_with_size(0b1011u8, 8)?;
        let result = (bv << 100)?;
        assert_eq!(result.to_u64().unwrap(), 0);

        Ok(())
    }

    #[test]
    fn test_shl_multi_word() -> Result<(), BitVecError> {
        use num_bigint::BigUint;

        // 128-bit shift by 64 (exact word boundary)
        let bv = BitVec::from_biguint(&BigUint::from(3u64), 128)?;
        let result = (bv << 64)?;
        assert_eq!(result.to_biguint(), BigUint::from(3u64) << 64);

        // 128-bit shift by 65 (word + bits)
        let bv = BitVec::from_biguint(&BigUint::from(3u64), 128)?;
        let result = (bv << 65)?;
        assert_eq!(result.to_biguint(), BigUint::from(3u64) << 65);

        // 128-bit shift by 127 (just under width)
        let bv = BitVec::from_biguint(&BigUint::from(1u64), 128)?;
        let result = (bv << 127)?;
        assert_eq!(result.to_biguint(), BigUint::from(1u64) << 127);

        // 128-bit shift by 128 (== width) must be zero
        let bv = BitVec::from_biguint(&BigUint::from(0xffffu64), 128)?;
        let result = (bv << 128)?;
        assert_eq!(result.to_biguint(), BigUint::from(0u64));

        // Shifting in the LSB word into the high word with a cross-word carry
        let val = (BigUint::from(0xdeadbeefu64) << 32) | BigUint::from(0xcafef00du64);
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv << 40)?;
        let mask = (BigUint::from(1u8) << 128) - BigUint::from(1u8);
        assert_eq!(result.to_biguint(), (&val << 40) & &mask);

        Ok(())
    }

    #[test]
    fn test_shr() -> Result<(), BitVecError> {
        // Test basic right shift
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (bv >> 2)?;
        assert_eq!(result.to_u64().unwrap(), 0b10);

        // Test shift with carry across word boundaries
        let bv = BitVec::from_prim_with_size(1u64 << 63, 64)?;
        let result = (bv >> 63)?;
        assert_eq!(result.to_u64().unwrap(), 1);

        // Test shift that results in all zeros
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = (bv >> 4)?;
        assert_eq!(result.to_u64().unwrap(), 0);

        // Shift by 0 must not panic (previously triggered UB via `w << 64`)
        let bv = BitVec::from_prim_with_size(0b1011u8, 8)?;
        let result = (bv >> 0)?;
        assert_eq!(result.to_u64().unwrap(), 0b1011);

        // Shift by >= length must yield zero
        let bv = BitVec::from_prim_with_size(0xffu8, 8)?;
        let result = (bv >> 8)?;
        assert_eq!(result.to_u64().unwrap(), 0);
        let bv = BitVec::from_prim_with_size(0xffu8, 8)?;
        let result = (bv >> 100)?;
        assert_eq!(result.to_u64().unwrap(), 0);

        Ok(())
    }

    #[test]
    fn test_shr_multi_word() -> Result<(), BitVecError> {
        use num_bigint::BigUint;

        // 128-bit shift by 64 (exact word boundary)
        let val = BigUint::from(3u64) << 64;
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv >> 64)?;
        assert_eq!(result.to_biguint(), BigUint::from(3u64));

        // 128-bit shift by 65 (word + bits)
        let val = BigUint::from(6u64) << 64;
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv >> 65)?;
        assert_eq!(result.to_biguint(), BigUint::from(3u64));

        // 128-bit shift by 1 with high bit set (cross-word carry MSB->LSB)
        let val = BigUint::from(1u64) << 64;
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv >> 1)?;
        assert_eq!(result.to_biguint(), BigUint::from(1u64) << 63);

        // 128-bit shift by 128 (== width) must be zero
        let val = (BigUint::from(1u8) << 128) - BigUint::from(1u8);
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv >> 128)?;
        assert_eq!(result.to_biguint(), BigUint::from(0u64));

        // Check round-trip preserves bits with a complex value
        let val = (BigUint::from(0xdeadbeefu64) << 64) | BigUint::from(0xcafef00du64);
        let bv = BitVec::from_biguint(&val, 128)?;
        let result = (bv >> 40)?;
        assert_eq!(result.to_biguint(), &val >> 40);

        Ok(())
    }

    #[test]
    fn test_rotate_left() -> Result<(), BitVecError> {
        // Test basic rotation
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_left(1).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        // Test full rotation (should be same as original)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_left(4).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1010);

        // Test rotation with amount larger than length
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_left(5).unwrap(); // Same as rotating left by 1
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        Ok(())
    }

    #[test]
    fn test_rotate_right() -> Result<(), BitVecError> {
        // Test basic rotation
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_right(1).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        // Test full rotation (should be same as original)
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_right(4).unwrap();
        assert_eq!(result.to_u64().unwrap(), 0b1010);

        // Test rotation with amount larger than length
        let bv = BitVec::from_prim_with_size(0b1010u8, 4)?;
        let result = bv.rotate_right(5).unwrap(); // Same as rotating right by 1
        assert_eq!(result.to_u64().unwrap(), 0b0101);

        Ok(())
    }
}
