use serde::{Deserialize, Serialize};
use std::ops::{Add, Div, Mul, Sub};

use super::BitVec;
use crate::bitvec::BitVecError;
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FSort {
    pub exponent: u32,
    pub mantissa: u32,
}

pub const F32_SORT: FSort = FSort {
    exponent: 8,
    mantissa: 23,
};
pub const F64_SORT: FSort = FSort {
    exponent: 11,
    mantissa: 52,
};

impl FSort {
    pub fn new(exponent: u32, mantissa: u32) -> Self {
        Self { exponent, mantissa }
    }

    pub fn size(&self) -> u32 {
        self.exponent + self.mantissa + 1
    }

    pub fn f32() -> Self {
        F32_SORT
    }

    pub fn f64() -> Self {
        F64_SORT
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

    pub fn is_zero(&self) -> bool {
        self.exponent.is_zero() && self.mantissa.is_zero()
    }

    pub fn is_subnormal(&self) -> bool {
        self.exponent.is_zero() && !self.mantissa.is_zero()
    }

    /// Constructs a `Float` from an `f64` with rounding and format adjustments
    pub fn from_f64_with_rounding(value: f64, rm: FPRM, fsort: FSort) -> Result<Self, BitVecError> {
        let (sign, exponent, mantissa) = decompose_f64(value);

        let float = Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, fsort.exponent as usize)?,
            mantissa: BitVec::from_prim_with_size(mantissa, fsort.mantissa as usize)?,
        };

        float.to_fsort(fsort, rm)
    }

    pub fn to_fsort(&self, fsort: FSort, rm: FPRM) -> Result<Self, BitVecError> {
        const BIAS_32: u32 = 127;
        const BIAS_64: u32 = 1023;

        match (self.fsort(), fsort) {
            (current, target) if current == target => Ok(self.clone()),
            (F32_SORT, F64_SORT) => {
                // Check for special values first
                if self.is_nan() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F64_SORT.exponent as usize),
                        BitVec::ones(F64_SORT.mantissa as usize),
                    ));
                } else if self.is_infinity() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F64_SORT.exponent as usize),
                        BitVec::zeros(F64_SORT.mantissa as usize)?,
                    ));
                } else if self.is_zero() || self.is_subnormal() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::zeros(F64_SORT.exponent as usize)?,
                        BitVec::zeros(F64_SORT.mantissa as usize)?,
                    ));
                }

                // For normal numbers:
                // 1. Keep the sign bit
                // 2. Adjust exponent: Remove f32 bias (127) and add f64 bias (1023)
                let f32_exp = self
                    .exponent
                    .to_biguint()
                    .to_u32()
                    .expect("exponent too big");
                let unbiased_exp = f32_exp.wrapping_sub(BIAS_32);
                let f64_exp = unbiased_exp.wrapping_add(BIAS_64);

                // 3. Extend mantissa from 23 to 52 bits by padding with zeros
                let extended_mantissa = BitVec::from_prim_with_size(
                    self.mantissa.to_u64().expect("mantissa too big")
                        << (F64_SORT.mantissa - F32_SORT.mantissa),
                    F64_SORT.mantissa as usize,
                );

                Ok(Self::new(
                    self.sign,
                    BitVec::from_prim_with_size(f64_exp, F64_SORT.exponent as usize)?,
                    extended_mantissa?,
                ))
            }
            (F64_SORT, F32_SORT) => {
                // Check for special values first
                if self.is_nan() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F32_SORT.exponent as usize),
                        BitVec::ones(F32_SORT.mantissa as usize),
                    ));
                } else if self.is_infinity() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F32_SORT.exponent as usize),
                        BitVec::zeros(F32_SORT.mantissa as usize)?,
                    ));
                } else if self.is_zero() || self.is_subnormal() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::zeros(F32_SORT.exponent as usize)?,
                        BitVec::zeros(F32_SORT.mantissa as usize)?,
                    ));
                }

                // For normal numbers:
                // 1. Keep the sign bit
                // 2. Adjust exponent: Remove f64 bias (1023) and add f32 bias (127)
                let f64_exp = self
                    .exponent
                    .to_biguint()
                    .to_u32()
                    .expect("exponent too big");
                let unbiased_exp = f64_exp.wrapping_sub(BIAS_64);
                let f32_exp = unbiased_exp.wrapping_add(BIAS_32);

                // 3. Truncate mantissa from 52 to 23 bits with rounding
                let mantissa_shift = F64_SORT.mantissa - F32_SORT.mantissa;
                let mantissa_value = self.mantissa.to_u64().expect("mantissa too big");
                let truncated_mantissa = match rm {
                    FPRM::NearestTiesToEven => {
                        let round_bit = (mantissa_value >> (mantissa_shift - 1)) & 1;
                        let truncated = mantissa_value >> mantissa_shift;
                        if round_bit == 1 {
                            // If exactly halfway, round to even
                            if mantissa_value & ((1 << (mantissa_shift - 1)) - 1) == 0 {
                                if truncated & 1 == 1 {
                                    truncated + 1
                                } else {
                                    truncated
                                }
                            } else {
                                truncated + 1
                            }
                        } else {
                            truncated
                        }
                    }
                    FPRM::TowardPositive => {
                        if !self.sign && (mantissa_value & ((1 << mantissa_shift) - 1)) != 0 {
                            (mantissa_value >> mantissa_shift) + 1
                        } else {
                            mantissa_value >> mantissa_shift
                        }
                    }
                    FPRM::TowardNegative => {
                        if self.sign && (mantissa_value & ((1 << mantissa_shift) - 1)) != 0 {
                            (mantissa_value >> mantissa_shift) + 1
                        } else {
                            mantissa_value >> mantissa_shift
                        }
                    }
                    FPRM::TowardZero => mantissa_value >> mantissa_shift,
                    FPRM::NearestTiesToAway => {
                        let round_bit = (mantissa_value >> (mantissa_shift - 1)) & 1;
                        if round_bit == 1 {
                            (mantissa_value >> mantissa_shift) + 1
                        } else {
                            mantissa_value >> mantissa_shift
                        }
                    }
                };

                Ok(Self::new(
                    self.sign,
                    BitVec::from_prim_with_size(f32_exp, F32_SORT.exponent as usize)?,
                    BitVec::from_prim_with_size(truncated_mantissa, F32_SORT.mantissa as usize)?,
                ))
            }
            _ => todo!("to_fsort for other cases"),
        }
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

    /// Converts the float to an `f32` representation, if possible
    pub fn to_f32(&self) -> Option<f32> {
        let self_f32 = self.to_fsort(F32_SORT, FPRM::NearestTiesToEven).ok()?;
        Some(recompose_f32(
            self.sign as u8,
            self_f32.exponent.as_biguint().to_u8()?,
            self_f32.mantissa.as_biguint().to_u32()?,
        ))
    }

    /// Converts the float to an `f64` representation, if possible
    pub fn to_f64(&self) -> Option<f64> {
        let self_f64 = self.to_fsort(F64_SORT, FPRM::NearestTiesToEven).ok()?;
        Some(recompose_f64(
            self.sign as u8,
            self_f64.exponent.as_biguint().to_u16()?,
            self_f64.mantissa.to_u64()?,
        ))
    }

    pub fn convert_to_format(&self, fsort: FSort, fprm: FPRM) -> Result<Self, BitVecError> {
        // Assuming `to_f64()` provides the current float as `f64`, convert it to the new format
        let f64_value = self.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(f64_value, fprm, fsort)
    }

    pub fn from_unsigned_biguint_with_rounding(
        value: &BigUint,
        fsort: FSort,
        fprm: FPRM,
    ) -> Result<Self, BitVecError> {
        // Convert BigUint to f64 for simplicity in this example
        let float_value = value.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }
}

impl Add for Float {
    type Output = Result<Self, BitVecError>;

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

        let aligned_smaller_mantissa_val = aligned_smaller_mantissa?;

        // Add or subtract mantissas based on the signs
        let (new_sign, new_mantissa) = if larger.sign == smaller.sign {
            // Same sign, add mantissas
            (larger.sign, larger.mantissa + aligned_smaller_mantissa_val)
        } else {
            // Different signs, subtract mantissas
            if larger.mantissa > aligned_smaller_mantissa_val {
                (larger.sign, larger.mantissa - aligned_smaller_mantissa_val)
            } else {
                (!larger.sign, aligned_smaller_mantissa_val - larger.mantissa)
            }
        };

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) = normalize(new_mantissa?, larger.exponent)?;

        Ok(Float {
            sign: new_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        })
    }
}

impl Sub for Float {
    type Output = Result<Self, BitVecError>;

    fn sub(self, rhs: Self) -> Self::Output {
        // Subtraction is addition with the opposite sign
        self + Float {
            sign: !rhs.sign,
            ..rhs
        }
    }
}

impl Mul for Float {
    type Output = Result<Self, BitVecError>;

    fn mul(self, rhs: Self) -> Self::Output {
        // Multiply mantissas
        let mantissa_product = self.mantissa.clone() * rhs.mantissa.clone();

        // Add exponents
        let exponent_sum = self.exponent + rhs.exponent;

        // Determine resulting sign
        let result_sign = self.sign ^ rhs.sign;

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) =
            normalize(mantissa_product?, exponent_sum?)?;

        Ok(Float {
            sign: result_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        })
    }
}

impl Div for Float {
    type Output = Result<Self, BitVecError>;
    // TODO: Check for following cases:
    // Correct rounding modes.
    // Handling edge cases (e.g., NaNs, infinities).
    // Precision management and overflow/underflow handling.

    fn div(self, rhs: Self) -> Self::Output {
        // Divide mantissas
        let mantissa_quotient = (self.mantissa.clone() / rhs.mantissa.clone())?;
        // Subtract exponents
        let exponent_diff = self.exponent - rhs.exponent;

        // Determine resulting sign
        let result_sign = self.sign ^ rhs.sign;

        // Normalize the result
        let (normalized_exponent, normalized_mantissa) =
            normalize(mantissa_quotient, exponent_diff?)?;

        Ok(Float {
            sign: result_sign,
            exponent: normalized_exponent,
            mantissa: normalized_mantissa,
        })
    }
}

// Helper function to normalize the mantissa and adjust the exponent
fn normalize(mantissa: BitVec, exponent: BitVec) -> Result<(BitVec, BitVec), BitVecError> {
    // Calculate the amount of shift required to normalize mantissa
    let shift_amount = mantissa.leading_zeros();

    // Clamp shift_amount so it never exceeds the mantissa length
    if shift_amount >= mantissa.len() {
        return Ok((exponent, mantissa));
    }

    // Otherwise, shift mantissa and adjust exponent
    let normalized_mantissa = mantissa << shift_amount;
    let shift_bitvec = BitVec::from_prim_with_size(shift_amount as u32, exponent.len())?;

    let normalized_exponent = exponent.clone() - shift_bitvec;

    Ok((normalized_exponent?, normalized_mantissa?))
}

impl TryFrom<f32> for Float {
    type Error = BitVecError;

    fn try_from(value: f32) -> Result<Self, Self::Error> {
        let (sign, exponent, mantissa) = decompose_f32(value);
        Ok(Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 8)?,
            mantissa: BitVec::from_prim_with_size(mantissa, 23)?,
        })
    }
}

impl TryFrom<f64> for Float {
    type Error = BitVecError;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        let (sign, exponent, mantissa) = decompose_f64(value);
        Ok(Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 11)?,
            mantissa: BitVec::from_prim_with_size(mantissa, 52)?,
        })
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

    #[test]
    fn test_float_construct_round_trip() {
        // Test cases for conversion to and from Float
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
            let start = Float::try_from(value).expect("Failed to create Float from f64");
            let recomposed = start.to_f64();

            // Check for NaN explicitly as NaN != NaN
            if value.is_nan() {
                assert!(recomposed.unwrap().is_nan());
            } else {
                assert_eq!(value, recomposed.unwrap());
            }
        }
    }

    #[test]
    fn test_to_fp_round_trip() -> Result<(), BitVecError> {
        // Test cases for conversion to and from Float
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
            let start = Float::try_from(value)?;
            let middle = start.to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
            let end = middle.to_fsort(F64_SORT, FPRM::NearestTiesToEven)?;

            let recomposed = end.to_f64().ok_or_else(|| BitVecError::BitVectorTooShort {
                value: BigUint::from(0u32),
                length: 0,
            })?;

            if value.is_nan() {
                assert!(recomposed.is_nan());
            } else {
                assert_eq!(value, recomposed);
            }
        }

        Ok(())
    }

    #[test]
    fn test_float_construct_f32_to_f64() -> Result<(), BitVecError> {
        let test_values: &[f32] = &[
            0.0,
            -0.0,
            1.0,
            -1.0,
            42.0,
            -42.0,
            1.5,
            -1.5,
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
            f32::MAX,
            f32::MIN,
            f32::MIN_POSITIVE,
        ];

        for &value in test_values {
            let float = Float::try_from(value)?;
            let converted = float.to_fsort(F64_SORT, FPRM::NearestTiesToEven)?;
            let result = converted
                .to_f64()
                .ok_or_else(|| BitVecError::BitVectorTooShort {
                    value: BigUint::from(0u32),
                    length: 0,
                })?;

            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                assert_eq!(value as f64, result);
            }
        }

        Ok(())
    }

    #[test]
    #[allow(clippy::excessive_precision)]
    fn test_float_construct_f64_to_f32() -> Result<(), BitVecError> {
        let test_values: &[f64] = &[
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
            3.4028234663852886e+38,
            -3.4028234663852886e+38,
            f32::MIN_POSITIVE as f64,
        ];

        for &value in test_values {
            let float = Float::try_from(value)?;
            let converted = float.to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
            let result = converted
                .to_f32()
                .ok_or_else(|| BitVecError::BitVectorTooShort {
                    value: BigUint::from(0u32),
                    length: 0,
                })?;

            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                // Compare with value converted to f32 to account for precision loss
                assert_eq!(value as f32, result);
            }
        }

        Ok(())
    }
}
