use std::ops::{BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr};

use smallvec::SmallVec;

use super::{BitVec, BitVecError};

impl Neg for BitVec {
    type Output = Self;

    fn neg(self) -> Self::Output {
        !self
    }
}

impl Not for BitVec {
    type Output = Self;

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
    type Output = Self;

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
    type Output = Self;

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
    type Output = Self;

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
    type Output = Self;

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
    type Output = Self;

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
