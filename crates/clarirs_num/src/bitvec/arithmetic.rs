use std::ops::{Add, Div, Mul, Rem, Sub};

use num_bigint::BigUint;
use num_traits::Zero;
use smallvec::SmallVec;

use super::BitVec;

impl Add for BitVec {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        // Ensure operands have the same length
        assert_eq!(
            self.length, rhs.length,
            "BitVec lengths must match for addition"
        );

        let mut result = SmallVec::with_capacity(self.words.len());
        let mut carry = 0u64;

        // Add corresponding words with carry
        for i in 0..self.words.len() {
            let lhs = self.words.get(i).copied().unwrap_or(0);
            let rhs = rhs.words.get(i).copied().unwrap_or(0);

            let (sum1, carry1) = lhs.overflowing_add(rhs);
            let (sum2, carry2) = sum1.overflowing_add(carry);

            carry = (carry1 as u64) + (carry2 as u64);
            result.push(sum2);
        }

        // Apply final word mask
        if let Some(last) = result.last_mut() {
            *last &= self.final_word_mask;
        }

        BitVec::new(result, self.length)
    }
}

impl Add<u64> for BitVec {
    type Output = Self;

    fn add(self, rhs: u64) -> Self::Output {
        BitVec::from_prim_with_size(rhs, self.length) + self
    }
}

impl Sub for BitVec {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs) + 1
    }
}

impl Mul for BitVec {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) * BigUint::from(&rhs)), self.length)
    }
}

impl Div for BitVec {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) / BigUint::from(&rhs)), self.length)
    }
}

impl Rem for BitVec {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) % BigUint::from(&rhs)), self.length)
    }
}

impl BitVec {
    pub fn urem(&self, other: &Self) -> Self {
        if other.is_zero() {
            return self.clone();
        }
        let bitwidth = self.len();
        let remainder = self.to_biguint() % other.to_biguint();
        BitVec::from_biguint_trunc(&remainder, bitwidth)
    }

    pub fn srem(&self, other: &Self) -> Self {
        if other.is_zero() {
            return self.clone();
        }
        let bitwidth = self.len();

        // Compute absolute values in BigUint space
        let abs_dividend = self.to_biguint_abs();
        let abs_divisor = other.to_biguint_abs();
        let unsigned_remainder = abs_dividend % abs_divisor;
        let raw_rem = BitVec::from_biguint_trunc(&unsigned_remainder, bitwidth);

        // If the original dividend is negative, apply two's complement (NOT + 1)
        if self.sign() {
            !raw_rem + BitVec::from_prim_with_size(1u64, bitwidth)
        } else {
            raw_rem
        }
    }

    pub fn sdiv(&self, other: &Self) -> Self {
        let bitwidth = self.len();
        let result_neg = self.sign() ^ other.sign();

        let abs_dividend = self.to_biguint_abs();
        let abs_divisor = other.to_biguint_abs();
        if abs_divisor.is_zero() {
            // Return self if divisor is zero
            return self.clone();
        }

        let abs_quotient = &abs_dividend / &abs_divisor;
        let mut quotient_bv = BitVec::from_biguint_trunc(&abs_quotient, bitwidth);

        if result_neg {
            quotient_bv = !quotient_bv + BitVec::from_prim_with_size(1u64, bitwidth);
        }

        quotient_bv
    }
}
