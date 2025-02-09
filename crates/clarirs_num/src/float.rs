use serde::{Deserialize, Serialize};
use std::ops::{Add, Div, Mul, Sub};

use super::BitVec;
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FSort {
    exponent: u32,
    mantissa: u32,
}

impl FSort {
    pub fn new(exponent: u32, mantissa: u32) -> Self {
        Self { exponent, mantissa }
    }

    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    pub fn mantissa(&self) -> u32 {
        self.mantissa
    }

    pub fn size(&self) -> u32 {
        self.exponent + self.mantissa + 1
    }

    pub fn f32() -> Self {
        Self::new(8, 23)
    }

    pub fn f64() -> Self {
        Self::new(11, 52)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum FPRM {
    #[default]
    NearestTiesToEven,
    TowardPositive,
    TowardNegative,
    TowardZero,
    NearestTiesToAway,
}

/// A dynamic floating-point number representation. We follow the IEEE 754
/// standard wherever possible.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Float {
    sign: bool,
    exponent: BitVec,
    mantissa: BitVec,
}

impl Float {
    pub fn new(sign: bool, exponent: BitVec, mantissa: BitVec) -> Self {
        Self {
            sign,
            exponent,
            mantissa,
        }
    }

    pub fn sign(&self) -> bool {
        self.sign
    }

    pub fn exponent(&self) -> &BitVec {
        &self.exponent
    }

    pub fn mantissa(&self) -> &BitVec {
        &self.mantissa
    }

    pub fn fsort(&self) -> FSort {
        FSort::new(self.exponent.len() as u32, self.mantissa.len() as u32)
    }

    /// Constructs a `Float` from an `f64` with rounding and format adjustments
    pub fn from_f64_with_rounding(value: f64, _fprm: FPRM, fsort: FSort) -> Self {
        let sign = value.is_sign_negative();
        let abs_value = value.abs();

        let exp = abs_value.log2().floor() as u32;
        let mantissa_val = abs_value / 2f64.powf(exp as f64) - 1.0;

        let exponent = BitVec::from_prim_with_size(
            exp + ((1 << (fsort.exponent() - 1)) - 1),
            fsort.exponent() as usize,
        );
        let mantissa = BitVec::from_prim_with_size(
            (mantissa_val * (1 << fsort.mantissa()) as f64) as u64,
            fsort.mantissa() as usize,
        );

        Self::new(sign, exponent, mantissa)
    }

    pub fn to_fsort(&self, fsort: FSort, _rm: FPRM) -> Self {
        // TODO: This implementation only currently works for the same fsort

        let exponent = match fsort.exponent().cmp(&(self.exponent.len() as u32)) {
            std::cmp::Ordering::Less => todo!("to_fsort for smaller exponent"),
            std::cmp::Ordering::Equal => self.exponent.clone(),
            std::cmp::Ordering::Greater => todo!("to_fsort for larger exponent"),
        };

        let mantissa = match fsort.mantissa().cmp(&(self.mantissa.len() as u32)) {
            std::cmp::Ordering::Less => todo!("to_fsort for smaller mantissa"),
            std::cmp::Ordering::Equal => self.mantissa.clone(),
            std::cmp::Ordering::Greater => todo!("to_fsort for larger mantissa"),
        };

        Self::new(self.sign, exponent, mantissa)
    }

    pub fn compare_fp(&self, other: &Self) -> bool {
        self.sign == other.sign
            && self.exponent == other.exponent
            && self.mantissa == other.mantissa
    }

    pub fn lt(&self, other: &Self) -> bool {
        // Handle sign: If the signs differ, the positive number is greater.
        if self.sign() != other.sign() {
            return self.sign();
        }

        // If both numbers are positive, compare as usual; if negative, reverse the comparison.
        let both_negative = self.sign();

        // Compare exponents
        match self.exponent().cmp(other.exponent()) {
            std::cmp::Ordering::Less => return !both_negative,
            std::cmp::Ordering::Greater => return both_negative,
            std::cmp::Ordering::Equal => {}
        }

        // Exponents are equal, so compare mantissas
        match self.mantissa().cmp(other.mantissa()) {
            std::cmp::Ordering::Less => !both_negative,
            std::cmp::Ordering::Greater => both_negative,
            std::cmp::Ordering::Equal => false, // Numbers are equal
        }
    }

    pub fn leq(&self, other: &Self) -> bool {
        // Handle sign: If the signs differ, the positive number is greater.
        if self.sign() != other.sign() {
            return self.sign();
        }

        // If both numbers are positive, compare as usual; if negative, reverse the comparison.
        let both_negative = self.sign();

        // Compare exponents
        match self.exponent().cmp(other.exponent()) {
            std::cmp::Ordering::Less => return !both_negative,
            std::cmp::Ordering::Greater => return both_negative,
            std::cmp::Ordering::Equal => {}
        }

        // Exponents are equal, so compare mantissas
        match self.mantissa().cmp(other.mantissa()) {
            std::cmp::Ordering::Less => !both_negative,
            std::cmp::Ordering::Greater => both_negative,
            std::cmp::Ordering::Equal => true, // Numbers are equal, so return true
        }
    }

    pub fn gt(&self, other: &Self) -> bool {
        // Handle sign: If the signs differ, the positive number is greater.
        if self.sign() != other.sign() {
            return !self.sign();
        }

        // If both numbers are positive, compare as usual; if negative, reverse the comparison.
        let both_negative = self.sign();

        // Compare exponents
        match self.exponent().cmp(other.exponent()) {
            std::cmp::Ordering::Less => return both_negative,
            std::cmp::Ordering::Greater => return !both_negative,
            std::cmp::Ordering::Equal => {}
        }

        // Exponents are equal, so compare mantissas
        match self.mantissa().cmp(other.mantissa()) {
            std::cmp::Ordering::Less => both_negative,
            std::cmp::Ordering::Greater => !both_negative,
            std::cmp::Ordering::Equal => false, // Numbers are equal, so return false
        }
    }

    pub fn geq(&self, other: &Self) -> bool {
        // Handle sign: If the signs differ, the positive number is greater.
        if self.sign() != other.sign() {
            return !self.sign();
        }

        // If both numbers are positive, compare as usual; if negative, reverse the comparison.
        let both_negative = self.sign();

        // Compare exponents
        match self.exponent().cmp(other.exponent()) {
            std::cmp::Ordering::Less => return both_negative,
            std::cmp::Ordering::Greater => return !both_negative,
            std::cmp::Ordering::Equal => {}
        }

        // Exponents are equal, so compare mantissas
        match self.mantissa().cmp(other.mantissa()) {
            std::cmp::Ordering::Less => both_negative,
            std::cmp::Ordering::Greater => !both_negative,
            std::cmp::Ordering::Equal => true, // Numbers are equal, so return true
        }
    }

    pub fn is_nan(&self) -> bool {
        // The exponent should be all ones, and the mantissa should not be zero
        self.exponent.is_all_ones() && !self.mantissa.is_zero()
    }

    pub fn is_infinity(&self) -> bool {
        // The exponent should be all ones, and the mantissa should be zero
        self.exponent.is_all_ones() && self.mantissa.is_zero()
    }

    pub fn to_ieee_bits(&self) -> BigUint {
        // Construct IEEE 754 representation using sign, exponent, and mantissa
        let sign_bit = if self.sign {
            BigUint::from(1u8) << (self.fsort().size() as usize - 1)
        } else {
            BigUint::zero()
        };
        let exponent_bits = self.exponent.to_biguint() << self.mantissa.len();
        let mantissa_bits = self.mantissa.to_biguint();

        sign_bit | exponent_bits | mantissa_bits
    }

    /// Converts the float to an unsigned integer representation as BigUint
    pub fn to_unsigned_biguint(&self) -> Option<BigUint> {
        // Convert to f64 and then to BigUint for unsigned integer conversion
        self.to_f64().map(|value| BigUint::from(value as u64))
    }

    /// Converts the float to a signed integer representation as BigInt
    pub fn to_signed_bigint(&self) -> Option<BigInt> {
        // Convert to f64 and then to BigInt for signed integer conversion
        self.to_f64().map(|value| BigInt::from(value as i64))
    }

    /// Converts the float to an `f64` representation, if possible
    pub fn to_f64(&self) -> Option<f64> {
        // Check if the exponent or mantissa is too large to fit in `f64`
        if self.exponent.len() > 11 || self.mantissa.len() > 52 {
            return None; // Return None if it exceeds `f64` range
        }

        // Convert the exponent and mantissa from BitVec to integer values
        let exponent = self.exponent.to_biguint().to_u64()? as i64;
        let mantissa = self.mantissa.to_biguint().to_u64()?;

        // Bias adjustment for IEEE 754 format (for `f64`, the bias is 1023)
        let bias = 1023;
        let adjusted_exponent = (exponent - bias) as i32;

        // Reconstruct the `f64` value based on IEEE 754
        let mut value = (mantissa as f64) / (1u64 << 52) as f64; // Normalize mantissa
        value += 1.0; // Add the implicit leading 1 in IEEE 754

        // Apply the exponent by scaling the value
        value *= 2f64.powi(adjusted_exponent);

        // Apply the sign
        if self.sign {
            value = -value;
        }

        Some(value)
    }

    pub fn convert_to_format(&self, fsort: FSort, fprm: FPRM) -> Self {
        // Assuming `to_f64()` provides the current float as `f64`, convert it to the new format
        let f64_value = self.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(f64_value, fprm, fsort)
    }

    pub fn from_unsigned_biguint_with_rounding(value: &BigUint, fsort: FSort, fprm: FPRM) -> Self {
        // Convert BigUint to f64 for simplicity in this example
        let float_value = value.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }
}

impl Add for Float {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        // Ensure `self` is the larger exponent; if not, swap them
        let (larger, smaller) = if self.exponent > rhs.exponent {
            (self, rhs)
        } else {
            (rhs, self)
        };

        // Align mantissas by shifting the smaller mantissa
        let exponent_diff = larger.exponent.len() - smaller.exponent.len();
        let aligned_smaller_mantissa = smaller.mantissa.clone() >> exponent_diff;

        // Add or subtract mantissas based on the signs
        let (new_sign, new_mantissa) = if larger.sign == smaller.sign {
            // Same sign, add mantissas
            (larger.sign, larger.mantissa + aligned_smaller_mantissa)
        } else {
            // Different signs, subtract mantissas
            if larger.mantissa > aligned_smaller_mantissa {
                (larger.sign, larger.mantissa - aligned_smaller_mantissa)
            } else {
                (!larger.sign, aligned_smaller_mantissa - larger.mantissa)
            }
        };

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) = normalize(new_mantissa, larger.exponent);

        Float {
            sign: new_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        }
    }
}

impl Sub for Float {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        // Subtraction is addition with the opposite sign
        self + Float {
            sign: !rhs.sign,
            ..rhs
        }
    }
}

impl Mul for Float {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        // Multiply mantissas
        let mantissa_product = self.mantissa.clone() * rhs.mantissa.clone();

        // Add exponents
        let exponent_sum = self.exponent + rhs.exponent;

        // Determine resulting sign
        let result_sign = self.sign ^ rhs.sign;

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) = normalize(mantissa_product, exponent_sum);

        Float {
            sign: result_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        }
    }
}

impl Div for Float {
    type Output = Self;

    // TODO: Check for following cases:
    // Correct rounding modes.
    // Handling edge cases (e.g., NaNs, infinities).
    // Precision management and overflow/underflow handling.

    fn div(self, rhs: Self) -> Self::Output {
        // Divide mantissas
        let mantissa_quotient = self.mantissa.clone() / rhs.mantissa.clone();

        // Subtract exponents
        let exponent_diff = self.exponent - rhs.exponent;

        // Determine resulting sign
        let result_sign = self.sign ^ rhs.sign;

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) =
            normalize(mantissa_quotient, exponent_diff);

        Float {
            sign: result_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        }
    }
}

// Helper function to normalize the mantissa and adjust the exponent
fn normalize(mantissa: BitVec, exponent: BitVec) -> (BitVec, BitVec) {
    // Calculate the amount of shift required to normalize mantissa
    let shift_amount = mantissa.leading_zeros();

    // Shift mantissa and adjust exponent, using cloned values
    let normalized_mantissa = mantissa << shift_amount;
    let normalized_exponent =
        exponent.clone() - BitVec::from_prim_with_size(shift_amount as u32, exponent.len());

    (normalized_exponent, normalized_mantissa)
}

impl From<f32> for Float {
    fn from(value: f32) -> Self {
        let (sign, exponent, mantissa) = decompose_f32(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 8),
            mantissa: BitVec::from_prim_with_size(mantissa, 23),
        }
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        let (sign, exponent, mantissa) = decompose_f64(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 11),
            mantissa: BitVec::from_prim_with_size(mantissa, 52),
        }
    }
}

pub fn decompose_f32(value: f32) -> (u8, u8, u32) {
    let bits: u32 = value.to_bits();
    let sign: u8 = (bits >> 31) as u8;
    let exponent: u8 = ((bits >> 23) & 0xFF) as u8;
    let mantissa: u32 = bits & 0x7FFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f32(sign: u8, exponent: u8, mantissa: u32) -> f32 {
    let sign_bit: u32 = (sign as u32) << 31;
    let exponent_bits: u32 = ((exponent as u32) & 0xFF) << 23;
    let mantissa_bits: u32 = mantissa & 0x7FFFFF;
    let bits: u32 = sign_bit | exponent_bits | mantissa_bits;

    f32::from_bits(bits)
}

pub fn decompose_f64(value: f64) -> (u8, u16, u64) {
    let bits: u64 = value.to_bits();
    let sign: u8 = (bits >> 63) as u8;
    let exponent: u16 = ((bits >> 52) & 0x7FF) as u16;
    let mantissa: u64 = bits & 0xFFFFFFFFFFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f64(sign: u8, exponent: u16, mantissa: u64) -> f64 {
    let sign_bit: u64 = (sign as u64) << 63;
    let exponent_bits: u64 = ((exponent as u64) & 0x7FF) << 52;
    let mantissa_bits: u64 = mantissa & 0xFFFFFFFFFFFFF;
    let bits: u64 = sign_bit | exponent_bits | mantissa_bits;

    f64::from_bits(bits)
}

pub fn decompose_f64_big_endian(value: f64) -> (u8, u16, u64) {
    let bits: u64 = value.to_bits().to_be();
    let sign: u8 = (bits >> 63) as u8;
    let exponent: u16 = ((bits >> 52) & 0x7FF) as u16;
    let mantissa: u64 = bits & 0xFFFFFFFFFFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f64_big_endian(sign: u8, exponent: u16, mantissa: u64) -> f64 {
    let sign_bit: u64 = (sign as u64) << 63;
    let exponent_bits: u64 = ((exponent as u64) & 0x7FF) << 52;
    let mantissa_bits: u64 = mantissa & 0xFFFFFFFFFFFFF;
    let bits: u64 = sign_bit | exponent_bits | mantissa_bits;

    f64::from_bits(bits.to_be())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_decomposition() {
        // Test cases for decompose and recompose functions
        let values = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            42.0,
            -42.0,
            1.5,
            -1.5,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ];

        for &value in &values {
            let (sign, exponent, mantissa) = decompose_f64(value);
            let recomposed = recompose_f64(sign, exponent, mantissa);

            // Check for NaN explicitly as NaN != NaN
            if value.is_nan() {
                assert!(recomposed.is_nan());
            } else {
                assert_eq!(value, recomposed);
            }

            let (sign_be, exponent_be, mantissa_be) = decompose_f64_big_endian(value);
            let recomposed_be = recompose_f64_big_endian(sign_be, exponent_be, mantissa_be);

            // Check for NaN explicitly as NaN != NaN
            if value.is_nan() {
                assert!(recomposed_be.is_nan());
            } else {
                assert_eq!(value, recomposed_be);
            }
        }
    }
}
