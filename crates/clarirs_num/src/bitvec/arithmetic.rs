use std::ops::{Add, Div, Mul, Rem, Sub};

use num_bigint::BigUint;
use num_traits::Zero;
use smallvec::SmallVec;

use super::{BitVec, BitVecError};

impl Add for BitVec {
    type Output = Result<Self, BitVecError>;

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
    type Output = Result<Self, BitVecError>;

    fn add(self, rhs: u64) -> Self::Output {
        BitVec::from_prim_with_size(rhs, self.length)? + self
    }
}

impl Sub for BitVec {
    type Output = Result<Self, BitVecError>;

    fn sub(self, rhs: Self) -> Self::Output {
        (self.clone() + (-rhs)?)? + BitVec::from_prim_with_size(1u8, self.length)?
    }
}

impl Mul for BitVec {
    type Output = Result<Self, BitVecError>;

    fn mul(self, rhs: Self) -> Result<Self, BitVecError> {
        Ok(BitVec::from_biguint_trunc(
            &(BigUint::from(&self) * BigUint::from(&rhs)),
            self.length,
        ))
    }
}

impl Div for BitVec {
    type Output = Result<Self, BitVecError>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok(BitVec::from_biguint_trunc(
            &(BigUint::from(&self) / BigUint::from(&rhs)),
            self.length,
        ))
    }
}

impl Rem for BitVec {
    type Output = Result<Self, BitVecError>;

    fn rem(self, rhs: Self) -> Self::Output {
        Ok(BitVec::from_biguint_trunc(
            &(BigUint::from(&self) % BigUint::from(&rhs)),
            self.length,
        ))
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

    pub fn srem(&self, other: &Self) -> Result<Self, BitVecError> {
        if other.is_zero() {
            return Ok(self.clone());
        }
        let bitwidth = self.len();

        // Compute absolute values in BigUint space
        let abs_dividend = self.to_biguint_abs();
        let abs_divisor = other.to_biguint_abs();
        let unsigned_remainder = abs_dividend % abs_divisor;
        let raw_rem = BitVec::from_biguint_trunc(&unsigned_remainder, bitwidth);

        // If the original dividend is negative, apply two's complement (NOT + 1)
        if self.sign() {
            (!raw_rem)? + BitVec::from_prim_with_size(1u64, bitwidth)?
        } else {
            Ok(raw_rem)
        }
    }

    pub fn sdiv(&self, other: &Self) -> Result<Self, BitVecError> {
        let bitwidth = self.len();
        let result_neg = self.sign() ^ other.sign();

        let abs_dividend = self.to_biguint_abs();
        let abs_divisor = other.to_biguint_abs();
        if abs_divisor.is_zero() {
            // Return self if divisor is zero
            return Ok(self.clone());
        }

        let abs_quotient = &abs_dividend / &abs_divisor;
        let mut quotient_bv = BitVec::from_biguint_trunc(&abs_quotient, bitwidth);

        if result_neg {
            quotient_bv = ((!quotient_bv)? + BitVec::from_prim_with_size(1u64, bitwidth)?)?;
        }

        Ok(quotient_bv)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::result::Result;

    #[test]
    fn test_add() -> Result<(), BitVecError> {
        // Basic addition
        let a = BitVec::from(42u64);
        let b = BitVec::from(58u64);
        let result = (a + b)?;
        assert_eq!(result.to_u64().unwrap(), 100);

        // Addition with overflow within the same bitwidth
        let a = BitVec::from(0xFFFFFFFFu32);
        let b = BitVec::from(1u32);
        let result = (a + b)?;
        assert_eq!(result.len(), 32);
        assert_eq!(result.to_u64().unwrap(), 0);

        // Addition with different bit widths
        let a = BitVec::from_prim_with_size(42u64, 32);
        let b = BitVec::from_prim_with_size(58u64, 32);
        let result = (a? + b?)?;
        assert_eq!(result.to_u64().unwrap(), 100);

        Ok(())
    }

    #[test]
    fn test_sub() -> Result<(), BitVecError> {
        // Basic subtraction
        let a = BitVec::from(100u64);
        let b = BitVec::from(58u64);
        let result = (a - b)?;
        assert_eq!(result.to_u64().unwrap(), 42);

        // Subtraction with underflow
        let a = BitVec::from(0u64);
        let b = BitVec::from(1u64);
        let result = (a - b)?;
        assert_eq!(result.to_u64().unwrap(), u64::MAX);

        // Subtraction with different bit widths
        let a = BitVec::from_prim_with_size(100u64, 32);
        let b = BitVec::from_prim_with_size(58u64, 32);
        let result = (a? - b?)?;
        assert_eq!(result.to_u64().unwrap(), 42);

        Ok(())
    }

    #[test]
    fn test_mul() -> Result<(), BitVecError> {
        // Basic multiplication
        let a = BitVec::from(7u64);
        let b = BitVec::from(6u64);
        let result = (a * b)?;
        assert_eq!(result.to_u64().unwrap(), 42);

        // Multiplication with overflow
        let a = BitVec::from(0xFFFFFFFFu32);
        let b = BitVec::from(2u32);
        let result = (a * b)?;
        assert_eq!(result.to_u64().unwrap(), 0xFFFFFFFE);

        // Multiplication with different bit widths
        let a = BitVec::from_prim_with_size(7u64, 32)?;
        let b = BitVec::from_prim_with_size(6u64, 32)?;
        let result = (a * b)?;
        assert_eq!(result.to_u64().unwrap(), 42);

        Ok(())
    }

    #[test]
    fn test_div() -> Result<(), BitVecError> {
        // Basic division
        let a = BitVec::from(42u64);
        let b = BitVec::from(6u64);
        let result = (a / b)?;
        assert_eq!(result.to_u64().unwrap(), 7);

        // Division with remainder
        let a = BitVec::from(100u64);
        let b = BitVec::from(30u64);
        let result = (a / b)?;
        assert_eq!(result.to_u64().unwrap(), 3);

        // Division with different bit widths
        let a = BitVec::from_prim_with_size(100u64, 32)?;
        let b = BitVec::from_prim_with_size(30u64, 32)?;
        let result = (a / b)?;
        assert_eq!(result.to_u64().unwrap(), 3);

        Ok(())
        // TODO: DBZ error handling
        // // Division by zero (should return the dividend)
        // let a = BitVec::from(42u64);
        // let b = BitVec::from(0u64);
        // let result = a / b;
        // assert_eq!(result.to_u64().unwrap(), 42);
    }

    #[test]
    fn test_rem() -> Result<(), BitVecError> {
        // Basic remainder
        let a = BitVec::from(42u64);
        let b = BitVec::from(6u64);
        let result = (a % b)?;
        assert_eq!(result.to_u64().unwrap(), 0);

        // Remainder with non-zero result
        let a = BitVec::from(100u64);
        let b = BitVec::from(30u64);
        let result = (a % b)?;
        assert_eq!(result.to_u64().unwrap(), 10);

        // Remainder with different bit widths
        let a = BitVec::from_prim_with_size(100u64, 32)?;
        let b = BitVec::from_prim_with_size(30u64, 32)?;
        let result = (a % b)?;
        assert_eq!(result.to_u64().unwrap(), 10);

        Ok(())

        // TODO: DBZ error handling
        // // Remainder by zero (should return the dividend)
        // let a = BitVec::from(42u64);
        // let b = BitVec::from(0u64);
        // let result = a % b;
        // assert_eq!(result.to_u64().unwrap(), 42);
    }

    #[test]
    fn test_signed_arithmetic() -> Result<(), BitVecError> {
        let neg_42 = BitVec::from(-42i64);
        let pos_6 = BitVec::from(6u64);

        // Signed division should give -7
        let result = neg_42.sdiv(&pos_6)?;
        assert!(result.sign()); // Should be negative
        assert_eq!(result, BitVec::from(-7i64));

        // Create -100 in 64-bit two's complement
        let neg_100 = BitVec::from(-100i64);
        let pos_30 = BitVec::from_prim_with_size(30u64, 64)?;

        // Signed remainder should give -10
        let result = neg_100.srem(&pos_30)?;
        assert!(result.sign()); // Should be negative
        assert_eq!(result, BitVec::from(-10i64));

        // Test division with different signs
        let pos_100 = BitVec::from_prim_with_size(100u64, 64)?;
        let neg_30 = BitVec::from(-30i64);

        // Signed division should give -3
        let result = pos_100.sdiv(&neg_30)?;
        assert!(result.sign()); // Should be negative
        assert_eq!(result, BitVec::from(-3i64));

        Ok(())
    }

    #[test]
    fn test_power() -> Result<(), BitVecError> {
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
        let base = BitVec::from_prim_with_size(2u64, 32)?;
        let exp = BitVec::from_prim_with_size(4u64, 32)?;
        let result = base.pow(&exp).unwrap();
        assert_eq!(result.to_u64().unwrap(), 16);

        Ok(())
    }
}
