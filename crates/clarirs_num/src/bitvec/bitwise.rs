use std::ops::{BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr};

use smallvec::SmallVec;

use super::{BitVec, BitVecError};

impl Neg for BitVec {
    type Output = Result<Self, BitVecError>;

    fn neg(self) -> Self::Output {
        !self
    }
}

impl Not for BitVec {
    type Output = Result<Self, BitVecError>;

    fn not(self) -> Self::Output {
        let mut new_bv: SmallVec<[u64; 1]> = self.words.iter().map(|w| !w).collect();
        if self.length % 64 != 0 {
            if let Some(w) = new_bv.last_mut() {
                *w &= self.final_word_mask;
            }
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

impl Shl<usize> for BitVec {
    type Output = Result<Self, BitVecError>;

    fn shl(self, rhs: usize) -> Self::Output {
        BitVec::new(
            self.words
                .iter()
                .scan(0, |carry, w| {
                    let new_carry = w >> (64 - rhs);
                    let new_word = (w << rhs) | *carry;
                    *carry = new_carry;
                    Some(new_word)
                })
                .collect(),
            self.length,
        )
    }
}

impl Shr<usize> for BitVec {
    type Output = Result<Self, BitVecError>;

    fn shr(self, rhs: usize) -> Self::Output {
        BitVec::new(
            self.words
                .iter()
                .rev()
                .scan(0, |carry, w| {
                    let new_carry = w << (64 - rhs);
                    let new_word = (w >> rhs) | *carry;
                    *carry = new_carry;
                    Some(new_word)
                })
                .collect(),
            self.length,
        )
    }
}

impl BitVec {
    pub fn rotate_left(&self, rotate_amount: usize) -> Result<Self, BitVecError> {
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

    pub fn rotate_right(&self, rotate_amount: usize) -> Result<Self, BitVecError> {
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
    use crate::bitvec::BitVec;
    use crate::bitvec::BitVecError;

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
        // Negation should be equivalent to NOT
        let bv = BitVec::from_prim_with_size(0b10101010u8, 8)?;
        let neg_result = -bv.clone();
        let not_result = !bv;
        assert_eq!(neg_result, not_result);

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
