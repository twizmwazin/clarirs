use serde::{Deserialize, Serialize};
use std::ops::{Add, Div, Mul, Neg, Sub};

use super::{BitVec, BitVecError};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum FPRM {
    #[default]
    NearestTiesToEven,
    TowardPositive,
    TowardNegative,
    TowardZero,
    NearestTiesToAway,
}

/// A floating-point number that can be either f32 or f64.
#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub enum Float {
    F32(f32),
    F64(f64),
}

impl Eq for Float {}

impl std::hash::Hash for Float {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Float::F32(f) => {
                0u8.hash(state);
                f.to_bits().hash(state);
            }
            Float::F64(f) => {
                1u8.hash(state);
                f.to_bits().hash(state);
            }
        }
    }
}

impl Float {
    pub fn new(sign: bool, exponent: BitVec, mantissa: BitVec) -> Result<Self, BitVecError> {
        let fsort = FSort::new(exponent.len(), mantissa.len());

        match fsort {
            F32_SORT => {
                let sign_bit = if sign { 1u8 } else { 0u8 };
                let exp_val = exponent
                    .to_biguint()
                    .to_u8()
                    .ok_or(BitVecError::ConversionError)?;
                let mant_val = mantissa
                    .to_biguint()
                    .to_u32()
                    .ok_or(BitVecError::ConversionError)?;
                Ok(Float::F32(recompose_f32(sign_bit, exp_val, mant_val)))
            }
            F64_SORT => {
                let sign_bit = if sign { 1u8 } else { 0u8 };
                let exp_val = exponent
                    .to_biguint()
                    .to_u16()
                    .ok_or(BitVecError::ConversionError)?;
                let mant_val = mantissa.to_u64().ok_or(BitVecError::ConversionError)?;
                Ok(Float::F64(recompose_f64(sign_bit, exp_val, mant_val)))
            }
            _ => {
                // For other formats, convert through f64
                let sign_bit = if sign { 1u8 } else { 0u8 };
                let exp_val = exponent
                    .to_biguint()
                    .to_u16()
                    .ok_or(BitVecError::ConversionError)?;
                let mant_val = mantissa.to_u64().ok_or(BitVecError::ConversionError)?;
                Ok(Float::F64(recompose_f64(sign_bit, exp_val, mant_val)))
            }
        }
    }

    pub fn sign(&self) -> bool {
        match self {
            Float::F32(f) => f.is_sign_negative(),
            Float::F64(f) => f.is_sign_negative(),
        }
    }

    pub fn exponent(&self) -> BitVec {
        match self {
            Float::F32(f) => {
                let (_, exp, _) = decompose_f32(*f);
                BitVec::from((u64::from(exp), 8))
            }
            Float::F64(f) => {
                let (_, exp, _) = decompose_f64(*f);
                BitVec::from((u64::from(exp), 11))
            }
        }
    }

    pub fn mantissa(&self) -> BitVec {
        match self {
            Float::F32(f) => {
                let (_, _, mant) = decompose_f32(*f);
                BitVec::from((u64::from(mant), 23))
            }
            Float::F64(f) => {
                let (_, _, mant) = decompose_f64(*f);
                BitVec::from((mant, 52))
            }
        }
    }

    pub fn fsort(&self) -> FSort {
        match self {
            Float::F32(_) => F32_SORT,
            Float::F64(_) => F64_SORT,
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Float::F32(f) => *f == 0.0 || *f == -0.0,
            Float::F64(f) => *f == 0.0 || *f == -0.0,
        }
    }

    pub fn is_subnormal(&self) -> bool {
        match self {
            Float::F32(f) => f.is_subnormal(),
            Float::F64(f) => f.is_subnormal(),
        }
    }

    pub fn from_f64_with_rounding(
        value: f64,
        _rm: FPRM,
        fsort: FSort,
    ) -> Result<Self, BitVecError> {
        match fsort {
            F32_SORT => Ok(Float::F32(value as f32)),
            F64_SORT => Ok(Float::F64(value)),
            _ => Ok(Float::F64(value)), // Default to f64 for custom formats
        }
    }

    pub fn to_fsort(&self, fsort: FSort, _rm: FPRM) -> Result<Self, BitVecError> {
        match (self.fsort(), fsort) {
            (current, target) if current == target => Ok(*self),
            (F32_SORT, F64_SORT) => match self {
                Float::F32(f) => Ok(Float::F64(*f as f64)),
                _ => unreachable!(),
            },
            (F64_SORT, F32_SORT) => match self {
                Float::F64(f) => Ok(Float::F32(*f as f32)),
                _ => unreachable!(),
            },
            _ => {
                // For unsupported formats, return an error
                Err(BitVecError::InvalidExtractBounds {
                    upper: fsort.size(),
                    lower: 0,
                    length: self.fsort().size(),
                })
            }
        }
    }

    pub fn compare_fp(&self, other: &Self) -> bool {
        // IEEE 754 fpEQ comparison - distinguishes between +0.0 and -0.0
        // Also, NaN != NaN
        if self.is_nan() || other.is_nan() {
            return false;
        }

        // For zero values, check sign bit explicitly
        if self.is_zero() && other.is_zero() {
            return self.sign() == other.sign();
        }

        // For other values, use standard equality
        match (self, other) {
            (Float::F32(a), Float::F32(b)) => a.to_bits() == b.to_bits(),
            (Float::F64(a), Float::F64(b)) => a.to_bits() == b.to_bits(),
            (Float::F32(a), Float::F64(b)) => (*a as f64).to_bits() == b.to_bits(),
            (Float::F64(a), Float::F32(b)) => a.to_bits() == (*b as f64).to_bits(),
        }
    }

    pub fn lt(&self, other: &Self) -> bool {
        // Convert both to f64 for comparison
        let self_f64 = self.to_f64().unwrap_or(0.0);
        let other_f64 = other.to_f64().unwrap_or(0.0);

        // Handle NaN and zero cases
        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return false;
        }

        self_f64 < other_f64
    }

    pub fn leq(&self, other: &Self) -> bool {
        let self_f64 = self.to_f64().unwrap_or(0.0);
        let other_f64 = other.to_f64().unwrap_or(0.0);

        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return true;
        }

        self_f64 <= other_f64
    }

    pub fn gt(&self, other: &Self) -> bool {
        let self_f64 = self.to_f64().unwrap_or(0.0);
        let other_f64 = other.to_f64().unwrap_or(0.0);

        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return false;
        }

        self_f64 > other_f64
    }

    pub fn geq(&self, other: &Self) -> bool {
        let self_f64 = self.to_f64().unwrap_or(0.0);
        let other_f64 = other.to_f64().unwrap_or(0.0);

        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return true;
        }

        self_f64 >= other_f64
    }

    pub fn is_nan(&self) -> bool {
        match self {
            Float::F32(f) => f.is_nan(),
            Float::F64(f) => f.is_nan(),
        }
    }

    pub fn is_infinity(&self) -> bool {
        match self {
            Float::F32(f) => f.is_infinite(),
            Float::F64(f) => f.is_infinite(),
        }
    }

    /// Returns the IEEE 754 bit representation of this float as a [`BitVec`]
    /// whose width matches the float's sort (32 bits for f32, 64 bits for f64).
    pub fn to_ieee_bits(&self) -> BitVec {
        match self {
            Float::F32(f) => BitVec::from((u64::from(f.to_bits()), 32)),
            Float::F64(f) => BitVec::from((f.to_bits(), 64)),
        }
    }

    /// Reinterprets the bits of `bits` as an IEEE 754 float. The width of the
    /// bitvector selects the format: 32 bits yields an f32 and 64 bits an f64.
    /// Any other width returns [`BitVecError::ConversionError`].
    pub fn try_from_ieee_bits(bits: &BitVec) -> Result<Self, BitVecError> {
        match bits.len() {
            32 => {
                let value = bits.to_u64().ok_or(BitVecError::ConversionError)? as u32;
                Ok(Float::F32(f32::from_bits(value)))
            }
            64 => {
                let value = bits.to_u64().ok_or(BitVecError::ConversionError)?;
                Ok(Float::F64(f64::from_bits(value)))
            }
            _ => Err(BitVecError::ConversionError),
        }
    }

    pub fn to_unsigned_biguint(&self) -> Result<BigUint, BitVecError> {
        self.to_f64()
            .ok_or(BitVecError::ConversionError)
            .map(|value| BigUint::from(value as u64))
    }

    pub fn to_signed_bigint(&self) -> Result<BigInt, BitVecError> {
        self.to_f64()
            .ok_or(BitVecError::ConversionError)
            .map(|value| BigInt::from(value as i64))
    }

    pub fn to_f32(&self) -> Option<f32> {
        match self {
            Float::F32(f) => Some(*f),
            Float::F64(f) => Some(*f as f32),
        }
    }

    pub fn to_f64(&self) -> Option<f64> {
        match self {
            Float::F32(f) => Some(*f as f64),
            Float::F64(f) => Some(*f),
        }
    }

    pub fn convert_to_format(&self, fsort: FSort, fprm: FPRM) -> Result<Self, BitVecError> {
        self.to_fsort(fsort, fprm)
    }

    pub fn from_bigint_with_rounding(
        value: &BigInt,
        fsort: FSort,
        fprm: FPRM,
    ) -> Result<Self, BitVecError> {
        let float_value = value.to_f64().ok_or(BitVecError::ConversionError)?;
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }

    pub fn from_biguint_with_rounding(
        value: &BigUint,
        fsort: FSort,
        fprm: FPRM,
    ) -> Result<Self, BitVecError> {
        let float_value = value.to_f64().ok_or(BitVecError::ConversionError)?;
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }

    pub fn shift_with_grs(value: BigUint, shift: u32) -> (BigUint, bool, bool) {
        if shift == 0 {
            return (value, false, false);
        }

        let k = shift as usize;
        let mask = (&BigUint::one() << k) - BigUint::one();
        let shifted_out = &value & &mask;

        let guard = ((&shifted_out >> (k - 1)) & BigUint::one()) == BigUint::one();

        let sticky = if k > 1 {
            (&shifted_out & ((&BigUint::one() << (k - 1)) - BigUint::one())) != BigUint::zero()
        } else {
            false
        };

        (value >> k, guard, sticky)
    }

    pub fn sqrt(&self) -> Self {
        match self {
            Float::F32(f) => Float::F32(f.sqrt()),
            Float::F64(f) => Float::F64(f.sqrt()),
        }
    }

    pub fn abs(&self) -> Self {
        match self {
            Float::F32(f) => Float::F32(f.abs()),
            Float::F64(f) => Float::F64(f.abs()),
        }
    }
}

impl Neg for Float {
    type Output = Float;

    fn neg(self) -> Self::Output {
        match self {
            Float::F32(f) => Float::F32(-f),
            Float::F64(f) => Float::F64(-f),
        }
    }
}

impl Add for Float {
    type Output = Float;

    fn add(self, other: Float) -> Self::Output {
        match (self, other) {
            (Float::F32(a), Float::F32(b)) => Float::F32(a + b),
            (Float::F64(a), Float::F64(b)) => Float::F64(a + b),
            (Float::F32(a), Float::F64(b)) => Float::F64(a as f64 + b),
            (Float::F64(a), Float::F32(b)) => Float::F64(a + b as f64),
        }
    }
}

impl Sub for Float {
    type Output = Float;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Float::F32(a), Float::F32(b)) => Float::F32(a - b),
            (Float::F64(a), Float::F64(b)) => Float::F64(a - b),
            (Float::F32(a), Float::F64(b)) => Float::F64(a as f64 - b),
            (Float::F64(a), Float::F32(b)) => Float::F64(a - b as f64),
        }
    }
}

impl Mul for Float {
    type Output = Float;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Float::F32(a), Float::F32(b)) => Float::F32(a * b),
            (Float::F64(a), Float::F64(b)) => Float::F64(a * b),
            (Float::F32(a), Float::F64(b)) => Float::F64(a as f64 * b),
            (Float::F64(a), Float::F32(b)) => Float::F64(a * b as f64),
        }
    }
}

impl Div for Float {
    type Output = Float;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Float::F32(a), Float::F32(b)) => Float::F32(a / b),
            (Float::F64(a), Float::F64(b)) => Float::F64(a / b),
            (Float::F32(a), Float::F64(b)) => Float::F64(a as f64 / b),
            (Float::F64(a), Float::F32(b)) => Float::F64(a / b as f64),
        }
    }
}

impl From<f32> for Float {
    fn from(value: f32) -> Self {
        Float::F32(value)
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        Float::F64(value)
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

            if value.is_nan() {
                assert!(recomposed.is_nan());
            } else {
                assert_eq!(value, recomposed);
            }

            let (sign_be, exponent_be, mantissa_be) = decompose_f64_big_endian(value);
            let recomposed_be = recompose_f64_big_endian(sign_be, exponent_be, mantissa_be);

            if value.is_nan() {
                assert!(recomposed_be.is_nan());
            } else {
                assert_eq!(value, recomposed_be);
            }
        }
    }

    #[test]
    fn test_float_construct_round_trip() {
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
            let start = Float::from(value);
            let recomposed = start.to_f64();

            if value.is_nan() {
                assert!(recomposed.unwrap().is_nan());
            } else {
                assert_eq!(value, recomposed.unwrap());
            }
        }
    }

    #[test]
    fn test_to_fp_round_trip() -> Result<(), BitVecError> {
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
            let start = Float::from(value);
            let middle = start.to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
            let end = middle.to_fsort(F64_SORT, FPRM::NearestTiesToEven)?;

            let recomposed = end.to_f64().expect("Failed to convert to f64");

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
            let float = Float::from(value);
            let converted = float.to_fsort(F64_SORT, FPRM::NearestTiesToEven)?;
            let result = converted.to_f64().expect("Failed to convert to f64");

            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                assert_eq!(value as f64, result);
            }
        }

        Ok(())
    }

    #[test]
    fn test_zero_comparison() {
        let pos_zero = Float::F32(0.0);
        let neg_zero = Float::F32(-0.0);

        println!("pos_zero.sign(): {}", pos_zero.sign());
        println!("neg_zero.sign(): {}", neg_zero.sign());
        println!(
            "pos_zero.compare_fp(&neg_zero): {}",
            pos_zero.compare_fp(&neg_zero)
        );
        println!(
            "neg_zero.compare_fp(&pos_zero): {}",
            neg_zero.compare_fp(&pos_zero)
        );

        assert!(
            !pos_zero.compare_fp(&neg_zero),
            "fpEQ(+0.0, -0.0) should be false"
        );
        assert!(
            !neg_zero.compare_fp(&pos_zero),
            "fpEQ(-0.0, +0.0) should be false"
        );
        assert!(
            pos_zero.compare_fp(&pos_zero),
            "fpEQ(+0.0, +0.0) should be true"
        );
        assert!(
            neg_zero.compare_fp(&neg_zero),
            "fpEQ(-0.0, -0.0) should be true"
        );
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
            let float = Float::from(value);
            let converted = float.to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
            let result = converted.to_f32().expect("Failed to convert to f32");

            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                assert_eq!(value as f32, result);
            }
        }

        Ok(())
    }

    #[test]
    fn test_to_ieee_bits() {
        let f32_values: &[f32] = &[0.0, -0.0, 1.0, -1.0, 42.0, f32::INFINITY, f32::NAN];
        for &value in f32_values {
            let bits = Float::F32(value).to_ieee_bits();
            assert_eq!(bits.len(), 32);
            assert_eq!(bits.to_u64().unwrap() as u32, value.to_bits());
        }

        let f64_values: &[f64] = &[0.0, -0.0, 1.0, -1.0, 42.0, f64::INFINITY, f64::NAN];
        for &value in f64_values {
            let bits = Float::F64(value).to_ieee_bits();
            assert_eq!(bits.len(), 64);
            assert_eq!(bits.to_u64().unwrap(), value.to_bits());
        }
    }

    #[test]
    fn test_ieee_bits_round_trip() -> Result<(), BitVecError> {
        let f32_values: &[f32] = &[
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
            f32::MIN_POSITIVE,
        ];
        for &value in f32_values {
            let start = Float::F32(value);
            let round_trip = Float::try_from_ieee_bits(&start.to_ieee_bits())?;
            assert_eq!(round_trip.fsort(), F32_SORT);
            let result = round_trip.to_f32().unwrap();
            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                assert_eq!(result.to_bits(), value.to_bits());
            }
        }

        let f64_values: &[f64] = &[
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
            f64::MIN_POSITIVE,
        ];
        for &value in f64_values {
            let start = Float::F64(value);
            let round_trip = Float::try_from_ieee_bits(&start.to_ieee_bits())?;
            assert_eq!(round_trip.fsort(), F64_SORT);
            let result = round_trip.to_f64().unwrap();
            if value.is_nan() {
                assert!(result.is_nan());
            } else {
                assert_eq!(result.to_bits(), value.to_bits());
            }
        }

        Ok(())
    }

    #[test]
    fn test_try_from_ieee_bits_invalid_width() {
        // Only 32- and 64-bit widths map onto the supported float formats.
        assert!(Float::try_from_ieee_bits(&BitVec::zeros(16)).is_err());
        assert!(Float::try_from_ieee_bits(&BitVec::zeros(31)).is_err());
        assert!(Float::try_from_ieee_bits(&BitVec::zeros(128)).is_err());
    }

    #[test]
    fn test_fsort_accessors() {
        let f32_sort = FSort::f32();
        assert_eq!(f32_sort, F32_SORT);
        assert_eq!(f32_sort.exponent, 8);
        assert_eq!(f32_sort.mantissa, 23);
        assert_eq!(f32_sort.size(), 32);

        let f64_sort = FSort::f64();
        assert_eq!(f64_sort, F64_SORT);
        assert_eq!(f64_sort.exponent, 11);
        assert_eq!(f64_sort.mantissa, 52);
        assert_eq!(f64_sort.size(), 64);

        let f16_like = FSort::new(5, 10);
        assert_eq!(f16_like.exponent, 5);
        assert_eq!(f16_like.mantissa, 10);
        assert_eq!(f16_like.size(), 16);
    }

    #[test]
    fn test_fprm_default() {
        assert_eq!(FPRM::default(), FPRM::NearestTiesToEven);
    }

    #[test]
    fn test_new_f32_from_parts() -> Result<(), BitVecError> {
        // 1.0f32: sign=0, exponent=127, mantissa=0
        let one = Float::new(
            false,
            BitVec::from((127u64, 8)),
            BitVec::from((0u64, 23)),
        )?;
        assert_eq!(one, Float::F32(1.0));
        assert_eq!(one.fsort(), F32_SORT);

        // -1.5f32: sign=1, exponent=127, mantissa=0x400000
        let neg_one_and_half = Float::new(
            true,
            BitVec::from((127u64, 8)),
            BitVec::from((0x400000u64, 23)),
        )?;
        assert_eq!(neg_one_and_half, Float::F32(-1.5));

        // +infinity: exponent all ones, mantissa zero
        let inf = Float::new(false, BitVec::from((255u64, 8)), BitVec::from((0u64, 23)))?;
        assert!(inf.is_infinity());
        assert!(!inf.sign());

        // NaN: exponent all ones, non-zero mantissa
        let nan = Float::new(false, BitVec::from((255u64, 8)), BitVec::from((1u64, 23)))?;
        assert!(nan.is_nan());

        // Smallest positive subnormal: exponent 0, mantissa 1
        let subnormal = Float::new(false, BitVec::from((0u64, 8)), BitVec::from((1u64, 23)))?;
        assert!(subnormal.is_subnormal());
        assert_eq!(subnormal.to_f32().unwrap().to_bits(), 1u32);

        // Signed zero: all fields zero, sign set
        let neg_zero = Float::new(true, BitVec::from((0u64, 8)), BitVec::from((0u64, 23)))?;
        assert!(neg_zero.is_zero());
        assert!(neg_zero.sign());
        assert_eq!(neg_zero.to_f32().unwrap().to_bits(), 0x8000_0000u32);

        Ok(())
    }

    #[test]
    fn test_new_f64_from_parts() -> Result<(), BitVecError> {
        // 1.0f64: sign=0, exponent=1023, mantissa=0
        let one = Float::new(
            false,
            BitVec::from((1023u64, 11)),
            BitVec::from((0u64, 52)),
        )?;
        assert_eq!(one, Float::F64(1.0));
        assert_eq!(one.fsort(), F64_SORT);

        // -2.0f64: sign=1, exponent=1024, mantissa=0
        let neg_two = Float::new(
            true,
            BitVec::from((1024u64, 11)),
            BitVec::from((0u64, 52)),
        )?;
        assert_eq!(neg_two, Float::F64(-2.0));

        // NaN: exponent all ones, non-zero mantissa
        let nan = Float::new(
            false,
            BitVec::from((0x7FFu64, 11)),
            BitVec::from((1u64, 52)),
        )?;
        assert!(nan.is_nan());

        // -infinity
        let neg_inf = Float::new(
            true,
            BitVec::from((0x7FFu64, 11)),
            BitVec::from((0u64, 52)),
        )?;
        assert!(neg_inf.is_infinity());
        assert!(neg_inf.sign());

        // Smallest positive subnormal
        let subnormal = Float::new(false, BitVec::from((0u64, 11)), BitVec::from((1u64, 52)))?;
        assert!(subnormal.is_subnormal());
        assert_eq!(subnormal.to_f64().unwrap().to_bits(), 1u64);

        Ok(())
    }

    #[test]
    fn test_new_custom_format_from_parts() -> Result<(), BitVecError> {
        // A 16-bit (5-exponent, 10-mantissa) format falls into the catch-all
        // branch: the raw exponent and mantissa field values are re-packed
        // directly into f64 fields without rebiasing. This documents current
        // behavior: an f16-style 1.0 (exp=15, mant=0) does NOT become 1.0; it
        // becomes f64::from_bits(15 << 52) = 2^-1008.
        let custom = Float::new(false, BitVec::from((15u64, 5)), BitVec::from((0u64, 10)))?;
        assert_eq!(custom.fsort(), F64_SORT);
        assert_eq!(custom.to_f64().unwrap().to_bits(), 15u64 << 52);

        // Error path: an exponent field wider than 16 bits whose value does
        // not fit in a u16 yields a ConversionError.
        let result = Float::new(
            false,
            BitVec::from((0x1FFFFu64, 20)),
            BitVec::from((0u64, 10)),
        );
        assert_eq!(result, Err(BitVecError::ConversionError));

        Ok(())
    }

    #[test]
    fn test_sign_exponent_mantissa_accessors() {
        // f32 accessors
        let f = Float::F32(-1.5);
        assert!(f.sign());
        assert_eq!(f.exponent().len(), 8);
        assert_eq!(f.exponent().to_u64().unwrap(), 127);
        assert_eq!(f.mantissa().len(), 23);
        assert_eq!(f.mantissa().to_u64().unwrap(), 0x400000);

        let f = Float::F32(1.0);
        assert!(!f.sign());
        assert_eq!(f.exponent().to_u64().unwrap(), 127);
        assert_eq!(f.mantissa().to_u64().unwrap(), 0);

        // f64 accessors
        let d = Float::F64(-1.5);
        assert!(d.sign());
        assert_eq!(d.exponent().len(), 11);
        assert_eq!(d.exponent().to_u64().unwrap(), 1023);
        assert_eq!(d.mantissa().len(), 52);
        assert_eq!(d.mantissa().to_u64().unwrap(), 1u64 << 51);

        // Signed zeros: sign bit is preserved
        assert!(!Float::F32(0.0).sign());
        assert!(Float::F32(-0.0).sign());
        assert!(!Float::F64(0.0).sign());
        assert!(Float::F64(-0.0).sign());

        // NaN sign follows the sign bit
        assert!(Float::F64(-f64::NAN).sign() != Float::F64(f64::NAN).sign());
    }

    #[test]
    fn test_special_value_predicates() {
        // is_zero
        assert!(Float::F32(0.0).is_zero());
        assert!(Float::F32(-0.0).is_zero());
        assert!(Float::F64(0.0).is_zero());
        assert!(Float::F64(-0.0).is_zero());
        assert!(!Float::F32(1.0).is_zero());
        assert!(!Float::F64(f64::MIN_POSITIVE).is_zero());
        assert!(!Float::F32(f32::NAN).is_zero());

        // is_nan
        assert!(Float::F32(f32::NAN).is_nan());
        assert!(Float::F64(f64::NAN).is_nan());
        assert!(!Float::F32(f32::INFINITY).is_nan());
        assert!(!Float::F64(0.0).is_nan());

        // is_infinity
        assert!(Float::F32(f32::INFINITY).is_infinity());
        assert!(Float::F32(f32::NEG_INFINITY).is_infinity());
        assert!(Float::F64(f64::INFINITY).is_infinity());
        assert!(Float::F64(f64::NEG_INFINITY).is_infinity());
        assert!(!Float::F32(f32::MAX).is_infinity());
        assert!(!Float::F64(f64::NAN).is_infinity());

        // is_subnormal
        assert!(Float::F32(f32::from_bits(1)).is_subnormal());
        assert!(Float::F64(f64::from_bits(1)).is_subnormal());
        assert!(!Float::F32(f32::MIN_POSITIVE).is_subnormal());
        assert!(!Float::F64(f64::MIN_POSITIVE).is_subnormal());
        assert!(!Float::F32(0.0).is_subnormal());
        assert!(!Float::F64(0.0).is_subnormal());
    }

    #[test]
    fn test_from_f64_with_rounding() -> Result<(), BitVecError> {
        // Target f64: value passes through unchanged for every rounding mode.
        for rm in [
            FPRM::NearestTiesToEven,
            FPRM::TowardPositive,
            FPRM::TowardNegative,
            FPRM::TowardZero,
            FPRM::NearestTiesToAway,
        ] {
            let f = Float::from_f64_with_rounding(1.5, rm, F64_SORT)?;
            assert_eq!(f, Float::F64(1.5));
        }

        // Target f32: exactly representable values convert exactly.
        let f = Float::from_f64_with_rounding(1.5, FPRM::NearestTiesToEven, F32_SORT)?;
        assert_eq!(f, Float::F32(1.5));

        // NOTE (documented current behavior / suspected bug): the rounding
        // mode parameter is ignored. 1.0 + 2^-24 lies exactly halfway between
        // 1.0 and the next f32; every mode currently rounds ties-to-even
        // (down to 1.0), including TowardPositive which per IEEE 754 should
        // round up to 1.0 + 2^-23.
        let halfway = 1.0f64 + 2.0f64.powi(-24);
        for rm in [
            FPRM::NearestTiesToEven,
            FPRM::TowardPositive,
            FPRM::TowardNegative,
            FPRM::TowardZero,
            FPRM::NearestTiesToAway,
        ] {
            let f = Float::from_f64_with_rounding(halfway, rm, F32_SORT)?;
            assert_eq!(f, Float::F32(1.0));
        }

        // Overflow to infinity when narrowing to f32.
        let f = Float::from_f64_with_rounding(1e300, FPRM::NearestTiesToEven, F32_SORT)?;
        assert_eq!(f, Float::F32(f32::INFINITY));

        // NOTE (documented current behavior): custom formats fall back to
        // f64, so the resulting fsort is F64_SORT, not the requested sort.
        let f = Float::from_f64_with_rounding(1.5, FPRM::NearestTiesToEven, FSort::new(5, 10))?;
        assert_eq!(f, Float::F64(1.5));
        assert_eq!(f.fsort(), F64_SORT);

        Ok(())
    }

    #[test]
    fn test_to_fsort_identity_and_errors() -> Result<(), BitVecError> {
        // Same-sort conversion is the identity.
        let f = Float::F32(3.25);
        assert_eq!(f.to_fsort(F32_SORT, FPRM::TowardZero)?, f);
        let d = Float::F64(-7.5);
        assert_eq!(d.to_fsort(F64_SORT, FPRM::TowardPositive)?, d);

        // Unsupported target formats produce InvalidExtractBounds carrying
        // the target size and the source size.
        let err = Float::F32(1.0)
            .to_fsort(FSort::new(5, 10), FPRM::NearestTiesToEven)
            .unwrap_err();
        assert_eq!(
            err,
            BitVecError::InvalidExtractBounds {
                upper: 16,
                lower: 0,
                length: 32,
            }
        );

        // convert_to_format delegates to to_fsort.
        let widened = Float::F32(1.5).convert_to_format(F64_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(widened, Float::F64(1.5));

        Ok(())
    }

    #[test]
    fn test_to_fsort_narrowing_rounds_inexact_values() -> Result<(), BitVecError> {
        // 0.1f64 is not representable in f32; narrowing rounds to the nearest
        // f32 (which is bit-identical to the 0.1f32 literal).
        let narrowed = Float::F64(0.1).to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(narrowed.to_f32().unwrap().to_bits(), 0.1f32.to_bits());

        // Values below the smallest f32 subnormal flush to zero.
        let narrowed = Float::F64(1e-300).to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(narrowed.to_f32().unwrap().to_bits(), 0.0f32.to_bits());
        let narrowed = Float::F64(-1e-300).to_fsort(F32_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(narrowed.to_f32().unwrap().to_bits(), (-0.0f32).to_bits());

        Ok(())
    }

    #[test]
    fn test_compare_fp_mixed_widths() {
        // Same value across widths compares equal after widening.
        assert!(Float::F32(1.5).compare_fp(&Float::F64(1.5)));
        assert!(Float::F64(1.5).compare_fp(&Float::F32(1.5)));

        // 0.1f32 widened is not the same f64 as 0.1f64.
        assert!(!Float::F32(0.1).compare_fp(&Float::F64(0.1)));
        assert!(!Float::F64(0.1).compare_fp(&Float::F32(0.1)));

        // NaN never compares equal, in any width combination.
        assert!(!Float::F32(f32::NAN).compare_fp(&Float::F32(f32::NAN)));
        assert!(!Float::F64(f64::NAN).compare_fp(&Float::F64(f64::NAN)));
        assert!(!Float::F32(f32::NAN).compare_fp(&Float::F64(1.0)));
        assert!(!Float::F64(1.0).compare_fp(&Float::F32(f32::NAN)));

        // Mixed-width zeros go through the sign-aware zero branch.
        assert!(Float::F32(0.0).compare_fp(&Float::F64(0.0)));
        assert!(Float::F32(-0.0).compare_fp(&Float::F64(-0.0)));
        assert!(!Float::F32(0.0).compare_fp(&Float::F64(-0.0)));
        assert!(!Float::F64(-0.0).compare_fp(&Float::F32(0.0)));

        // Infinities compare equal only with matching sign.
        assert!(Float::F32(f32::INFINITY).compare_fp(&Float::F64(f64::INFINITY)));
        assert!(!Float::F32(f32::INFINITY).compare_fp(&Float::F64(f64::NEG_INFINITY)));
    }

    #[test]
    fn test_ordering_comparisons() {
        let one = Float::F64(1.0);
        let two = Float::F64(2.0);

        // lt
        assert!(one.lt(&two));
        assert!(!two.lt(&one));
        assert!(!one.lt(&one));

        // leq
        assert!(one.leq(&two));
        assert!(one.leq(&one));
        assert!(!two.leq(&one));

        // gt
        assert!(two.gt(&one));
        assert!(!one.gt(&two));
        assert!(!one.gt(&one));

        // geq
        assert!(two.geq(&one));
        assert!(one.geq(&one));
        assert!(!one.geq(&two));

        // Mixed widths compare through f64.
        assert!(Float::F32(1.5).lt(&Float::F64(2.5)));
        assert!(Float::F64(2.5).gt(&Float::F32(1.5)));
        assert!(Float::F32(1.5).leq(&Float::F32(1.5)));
        assert!(Float::F32(1.5).geq(&Float::F32(1.5)));

        // Negative ordering and infinities.
        assert!(Float::F64(f64::NEG_INFINITY).lt(&Float::F64(f64::MIN)));
        assert!(Float::F64(f64::INFINITY).gt(&Float::F64(f64::MAX)));
        assert!(Float::F64(-1.0).lt(&Float::F64(-0.5)));
    }

    #[test]
    fn test_ordering_comparisons_nan_and_zero() {
        let nan = Float::F64(f64::NAN);
        let one = Float::F64(1.0);

        // All ordered comparisons involving NaN are false.
        assert!(!nan.lt(&one));
        assert!(!one.lt(&nan));
        assert!(!nan.leq(&one));
        assert!(!one.leq(&nan));
        assert!(!nan.gt(&one));
        assert!(!one.gt(&nan));
        assert!(!nan.geq(&one));
        assert!(!one.geq(&nan));

        // Zeros of either sign are equal for ordering purposes: strict
        // comparisons are false, non-strict comparisons are true.
        let pz = Float::F64(0.0);
        let nz = Float::F64(-0.0);
        assert!(!pz.lt(&nz));
        assert!(!nz.lt(&pz));
        assert!(!pz.gt(&nz));
        assert!(!nz.gt(&pz));
        assert!(pz.leq(&nz));
        assert!(nz.leq(&pz));
        assert!(pz.geq(&nz));
        assert!(nz.geq(&pz));

        // Mixed-width zeros hit the same branch.
        assert!(Float::F32(-0.0).leq(&Float::F64(0.0)));
        assert!(!Float::F32(-0.0).lt(&Float::F64(0.0)));
    }

    #[test]
    fn test_add() {
        // Same-width results stay in that width.
        assert_eq!(Float::F32(1.5) + Float::F32(2.25), Float::F32(3.75));
        assert_eq!(Float::F64(1.5) + Float::F64(2.25), Float::F64(3.75));

        // Mixed widths widen to f64.
        assert_eq!(Float::F32(1.5) + Float::F64(2.25), Float::F64(3.75));
        assert_eq!(Float::F64(1.5) + Float::F32(2.25), Float::F64(3.75));

        // Special values.
        assert!((Float::F64(f64::INFINITY) + Float::F64(f64::NEG_INFINITY)).is_nan());
        assert_eq!(
            Float::F64(f64::INFINITY) + Float::F64(1.0),
            Float::F64(f64::INFINITY)
        );
        assert!((Float::F32(f32::NAN) + Float::F32(1.0)).is_nan());

        // Overflow saturates to infinity.
        assert_eq!(
            Float::F32(f32::MAX) + Float::F32(f32::MAX),
            Float::F32(f32::INFINITY)
        );

        // -0 + +0 == +0 under round-to-nearest.
        let sum = Float::F64(-0.0) + Float::F64(0.0);
        assert_eq!(sum.to_f64().unwrap().to_bits(), 0.0f64.to_bits());
    }

    #[test]
    fn test_sub() {
        assert_eq!(Float::F32(5.0) - Float::F32(1.5), Float::F32(3.5));
        assert_eq!(Float::F64(5.0) - Float::F64(1.5), Float::F64(3.5));
        assert_eq!(Float::F32(5.0) - Float::F64(1.5), Float::F64(3.5));
        assert_eq!(Float::F64(5.0) - Float::F32(1.5), Float::F64(3.5));

        // x - x is +0 under round-to-nearest.
        let diff = Float::F64(1.5) - Float::F64(1.5);
        assert_eq!(diff.to_f64().unwrap().to_bits(), 0.0f64.to_bits());

        // inf - inf is NaN.
        assert!((Float::F64(f64::INFINITY) - Float::F64(f64::INFINITY)).is_nan());
        assert!((Float::F32(1.0) - Float::F32(f32::NAN)).is_nan());
    }

    #[test]
    fn test_mul() {
        assert_eq!(Float::F32(3.0) * Float::F32(0.5), Float::F32(1.5));
        assert_eq!(Float::F64(3.0) * Float::F64(0.5), Float::F64(1.5));
        assert_eq!(Float::F32(3.0) * Float::F64(0.5), Float::F64(1.5));
        assert_eq!(Float::F64(3.0) * Float::F32(0.5), Float::F64(1.5));

        // 0 * inf is NaN.
        assert!((Float::F64(0.0) * Float::F64(f64::INFINITY)).is_nan());

        // Sign rules.
        assert_eq!(Float::F64(-2.0) * Float::F64(3.0), Float::F64(-6.0));
        let prod = Float::F64(-2.0) * Float::F64(0.0);
        assert_eq!(prod.to_f64().unwrap().to_bits(), (-0.0f64).to_bits());

        // Overflow and underflow.
        assert_eq!(
            Float::F32(f32::MAX) * Float::F32(2.0),
            Float::F32(f32::INFINITY)
        );
        let underflow = Float::F32(f32::MIN_POSITIVE) * Float::F32(0.5);
        assert!(underflow.is_subnormal());
        assert_eq!(
            underflow.to_f32().unwrap().to_bits(),
            (f32::MIN_POSITIVE / 2.0).to_bits()
        );
    }

    #[test]
    fn test_div() {
        assert_eq!(Float::F32(7.0) / Float::F32(2.0), Float::F32(3.5));
        assert_eq!(Float::F64(7.0) / Float::F64(2.0), Float::F64(3.5));
        assert_eq!(Float::F32(7.0) / Float::F64(2.0), Float::F64(3.5));
        assert_eq!(Float::F64(7.0) / Float::F32(2.0), Float::F64(3.5));

        // Division by zero gives a signed infinity.
        assert_eq!(
            Float::F64(1.0) / Float::F64(0.0),
            Float::F64(f64::INFINITY)
        );
        assert_eq!(
            Float::F64(1.0) / Float::F64(-0.0),
            Float::F64(f64::NEG_INFINITY)
        );
        assert_eq!(
            Float::F32(-1.0) / Float::F32(0.0),
            Float::F32(f32::NEG_INFINITY)
        );

        // 0/0 and inf/inf are NaN.
        assert!((Float::F64(0.0) / Float::F64(0.0)).is_nan());
        assert!((Float::F64(f64::INFINITY) / Float::F64(f64::INFINITY)).is_nan());
    }

    #[test]
    fn test_neg_and_abs() {
        assert_eq!(-Float::F32(1.5), Float::F32(-1.5));
        assert_eq!(-Float::F64(-2.5), Float::F64(2.5));

        // Negating zero flips the sign bit.
        let neg_zero = -Float::F64(0.0);
        assert_eq!(neg_zero.to_f64().unwrap().to_bits(), (-0.0f64).to_bits());
        let pos_zero = -Float::F32(-0.0);
        assert_eq!(pos_zero.to_f32().unwrap().to_bits(), 0.0f32.to_bits());

        // Negating infinity and NaN.
        assert_eq!(
            -Float::F64(f64::INFINITY),
            Float::F64(f64::NEG_INFINITY)
        );
        assert!((-Float::F32(f32::NAN)).is_nan());

        // abs
        assert_eq!(Float::F32(-1.5).abs(), Float::F32(1.5));
        assert_eq!(Float::F32(1.5).abs(), Float::F32(1.5));
        assert_eq!(Float::F64(-2.5).abs(), Float::F64(2.5));
        assert_eq!(
            Float::F64(f64::NEG_INFINITY).abs(),
            Float::F64(f64::INFINITY)
        );
        let abs_zero = Float::F64(-0.0).abs();
        assert_eq!(abs_zero.to_f64().unwrap().to_bits(), 0.0f64.to_bits());
        assert!(Float::F32(f32::NAN).abs().is_nan());
    }

    #[test]
    fn test_sqrt() {
        assert_eq!(Float::F32(4.0).sqrt(), Float::F32(2.0));
        assert_eq!(Float::F64(9.0).sqrt(), Float::F64(3.0));
        assert_eq!(Float::F64(2.0).sqrt(), Float::F64(2.0f64.sqrt()));

        // sqrt of a negative number is NaN.
        assert!(Float::F32(-1.0).sqrt().is_nan());
        assert!(Float::F64(-4.0).sqrt().is_nan());

        // IEEE 754: sqrt preserves signed zero.
        assert_eq!(Float::F64(0.0).sqrt().to_f64().unwrap().to_bits(), 0.0f64.to_bits());
        assert_eq!(
            Float::F64(-0.0).sqrt().to_f64().unwrap().to_bits(),
            (-0.0f64).to_bits()
        );

        // sqrt(+inf) = +inf, sqrt(NaN) = NaN.
        assert_eq!(
            Float::F64(f64::INFINITY).sqrt(),
            Float::F64(f64::INFINITY)
        );
        assert!(Float::F32(f32::NAN).sqrt().is_nan());
    }

    #[test]
    fn test_to_f32_to_f64_cross_width() {
        assert_eq!(Float::F32(1.5).to_f32(), Some(1.5f32));
        assert_eq!(Float::F64(1.5).to_f32(), Some(1.5f32));
        assert_eq!(Float::F32(1.5).to_f64(), Some(1.5f64));
        assert_eq!(Float::F64(1.5).to_f64(), Some(1.5f64));

        // Narrowing rounds; widening is exact.
        assert_eq!(Float::F64(0.1).to_f32(), Some(0.1f32));
        assert_eq!(Float::F32(0.1).to_f64(), Some(0.1f32 as f64));

        // Narrowing an out-of-range f64 saturates to infinity.
        assert_eq!(Float::F64(1e300).to_f32(), Some(f32::INFINITY));
        assert_eq!(Float::F64(-1e300).to_f32(), Some(f32::NEG_INFINITY));
    }

    #[test]
    fn test_to_unsigned_biguint() -> Result<(), BitVecError> {
        assert_eq!(
            Float::F64(42.0).to_unsigned_biguint()?,
            BigUint::from(42u64)
        );
        // Fractional part truncates toward zero.
        assert_eq!(
            Float::F64(42.9).to_unsigned_biguint()?,
            BigUint::from(42u64)
        );
        assert_eq!(Float::F32(7.0).to_unsigned_biguint()?, BigUint::from(7u64));

        // Documented current behavior: the f64 -> u64 cast saturates, so
        // negative values become 0, NaN becomes 0, and +inf becomes u64::MAX.
        assert_eq!(
            Float::F64(-5.0).to_unsigned_biguint()?,
            BigUint::from(0u64)
        );
        assert_eq!(
            Float::F64(f64::NAN).to_unsigned_biguint()?,
            BigUint::from(0u64)
        );
        assert_eq!(
            Float::F64(f64::INFINITY).to_unsigned_biguint()?,
            BigUint::from(u64::MAX)
        );

        Ok(())
    }

    #[test]
    fn test_to_signed_bigint() -> Result<(), BitVecError> {
        assert_eq!(Float::F64(42.0).to_signed_bigint()?, BigInt::from(42i64));
        assert_eq!(Float::F64(-42.9).to_signed_bigint()?, BigInt::from(-42i64));
        assert_eq!(Float::F32(-7.0).to_signed_bigint()?, BigInt::from(-7i64));

        // Documented current behavior: the f64 -> i64 cast saturates, so NaN
        // becomes 0 and infinities clamp to the i64 extremes.
        assert_eq!(
            Float::F64(f64::NAN).to_signed_bigint()?,
            BigInt::from(0i64)
        );
        assert_eq!(
            Float::F64(f64::INFINITY).to_signed_bigint()?,
            BigInt::from(i64::MAX)
        );
        assert_eq!(
            Float::F64(f64::NEG_INFINITY).to_signed_bigint()?,
            BigInt::from(i64::MIN)
        );

        Ok(())
    }

    #[test]
    fn test_from_bigint_with_rounding() -> Result<(), BitVecError> {
        let f = Float::from_bigint_with_rounding(
            &BigInt::from(42),
            F64_SORT,
            FPRM::NearestTiesToEven,
        )?;
        assert_eq!(f, Float::F64(42.0));

        let f = Float::from_bigint_with_rounding(
            &BigInt::from(-42),
            F32_SORT,
            FPRM::NearestTiesToEven,
        )?;
        assert_eq!(f, Float::F32(-42.0));

        // A value too large for f32 saturates to infinity when narrowed.
        let big = BigInt::from(1u8) << 200;
        let f = Float::from_bigint_with_rounding(&big, F32_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(f, Float::F32(f32::INFINITY));

        // The same value fits in f64.
        let f = Float::from_bigint_with_rounding(&big, F64_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(f, Float::F64(2.0f64.powi(200)));

        Ok(())
    }

    #[test]
    fn test_from_biguint_with_rounding() -> Result<(), BitVecError> {
        let f = Float::from_biguint_with_rounding(
            &BigUint::from(42u32),
            F64_SORT,
            FPRM::NearestTiesToEven,
        )?;
        assert_eq!(f, Float::F64(42.0));

        let f = Float::from_biguint_with_rounding(
            &BigUint::from(7u32),
            F32_SORT,
            FPRM::NearestTiesToEven,
        )?;
        assert_eq!(f, Float::F32(7.0));

        // 2^53 + 1 is not exactly representable in f64; it rounds to 2^53.
        let above_53 = (BigUint::one() << 53) + BigUint::one();
        let f = Float::from_biguint_with_rounding(&above_53, F64_SORT, FPRM::NearestTiesToEven)?;
        assert_eq!(f, Float::F64(2.0f64.powi(53)));

        Ok(())
    }

    #[test]
    fn test_shift_with_grs() {
        // Zero shift returns the value untouched with clear guard/sticky.
        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1011u32), 0);
        assert_eq!(v, BigUint::from(0b1011u32));
        assert!(!g);
        assert!(!s);

        // Shift by 1: guard is the single shifted-out bit, sticky is always
        // false (there are no bits below the guard).
        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1011u32), 1);
        assert_eq!(v, BigUint::from(0b101u32));
        assert!(g);
        assert!(!s);

        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1010u32), 1);
        assert_eq!(v, BigUint::from(0b101u32));
        assert!(!g);
        assert!(!s);

        // Shift by 2: guard = bit 1, sticky = OR of bit 0.
        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1011u32), 2);
        assert_eq!(v, BigUint::from(0b10u32));
        assert!(g);
        assert!(s);

        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1001u32), 2);
        assert_eq!(v, BigUint::from(0b10u32));
        assert!(!g);
        assert!(s);

        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1110u32), 2);
        assert_eq!(v, BigUint::from(0b11u32));
        assert!(g);
        assert!(!s);

        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b1100u32), 2);
        assert_eq!(v, BigUint::from(0b11u32));
        assert!(!g);
        assert!(!s);

        // Shifting out everything leaves zero; sticky picks up low set bits.
        let (v, g, s) = Float::shift_with_grs(BigUint::from(0b0111u32), 4);
        assert_eq!(v, BigUint::zero());
        assert!(!g);
        assert!(s);
    }

    #[test]
    fn test_hash_and_eq_semantics() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_of(f: &Float) -> u64 {
            let mut hasher = DefaultHasher::new();
            f.hash(&mut hasher);
            hasher.finish()
        }

        // Identical values hash identically.
        assert_eq!(hash_of(&Float::F32(1.5)), hash_of(&Float::F32(1.5)));
        assert_eq!(hash_of(&Float::F64(1.5)), hash_of(&Float::F64(1.5)));

        // The width is part of the hash: F32(1.0) and F64(1.0) differ.
        assert_ne!(hash_of(&Float::F32(1.0)), hash_of(&Float::F64(1.0)));

        // Hashing is bit-based, so +0.0 and -0.0 hash differently...
        assert_ne!(hash_of(&Float::F64(0.0)), hash_of(&Float::F64(-0.0)));
        // ...and a NaN hashes consistently with itself.
        assert_eq!(
            hash_of(&Float::F64(f64::NAN)),
            hash_of(&Float::F64(f64::NAN))
        );

        // Documented current behavior: PartialEq is derived from the float
        // payloads, so NaN != NaN even though Float implements Eq (and the
        // Hash impl above treats equal-bit NaNs as identical). This is an
        // Eq-contract inconsistency worth knowing about.
        assert_ne!(Float::F64(f64::NAN), Float::F64(f64::NAN));
        // And +0.0 == -0.0 under derived PartialEq even though they hash
        // differently.
        assert_eq!(Float::F64(0.0), Float::F64(-0.0));
    }

    #[test]
    fn test_from_primitive_impls() {
        let f: Float = 1.5f32.into();
        assert_eq!(f, Float::F32(1.5));
        assert_eq!(f.fsort(), F32_SORT);

        let d: Float = 1.5f64.into();
        assert_eq!(d, Float::F64(1.5));
        assert_eq!(d.fsort(), F64_SORT);
    }

    #[test]
    fn test_decompose_recompose_f32() {
        // Exact field values for known constants.
        assert_eq!(decompose_f32(1.0), (0, 127, 0));
        assert_eq!(decompose_f32(-1.5), (1, 127, 0x400000));
        assert_eq!(decompose_f32(0.0), (0, 0, 0));
        assert_eq!(decompose_f32(-0.0), (1, 0, 0));
        assert_eq!(decompose_f32(f32::INFINITY), (0, 255, 0));
        assert_eq!(decompose_f32(f32::NEG_INFINITY), (1, 255, 0));
        assert_eq!(decompose_f32(f32::MIN_POSITIVE), (0, 1, 0));
        assert_eq!(decompose_f32(f32::from_bits(1)), (0, 0, 1));

        // Round trip across a spread of values.
        let values = [
            0.0f32,
            -0.0,
            1.0,
            -1.0,
            42.0,
            -42.0,
            1.5,
            f32::MAX,
            f32::MIN,
            f32::MIN_POSITIVE,
            f32::INFINITY,
            f32::NEG_INFINITY,
        ];
        for &value in &values {
            let (sign, exponent, mantissa) = decompose_f32(value);
            let recomposed = recompose_f32(sign, exponent, mantissa);
            assert_eq!(recomposed.to_bits(), value.to_bits());
        }

        // NaN round-trips to a NaN.
        let (sign, exponent, mantissa) = decompose_f32(f32::NAN);
        assert!(recompose_f32(sign, exponent, mantissa).is_nan());

        // recompose_f32 masks the mantissa to 23 bits.
        let masked = recompose_f32(0, 127, 0xFFFF_FFFF);
        assert_eq!(masked.to_bits(), (127u32 << 23) | 0x7FFFFF);
    }

    #[test]
    fn test_recompose_f64_masks_fields() {
        // recompose_f64 masks the exponent to 11 bits and mantissa to 52 bits.
        let masked = recompose_f64(0, 0xFFFF, u64::MAX);
        assert_eq!(masked.to_bits(), (0x7FFu64 << 52) | 0xFFFFFFFFFFFFF);

        // Exact field values for known f64 constants.
        assert_eq!(decompose_f64(1.0), (0, 1023, 0));
        assert_eq!(decompose_f64(-1.5), (1, 1023, 1u64 << 51));
        assert_eq!(decompose_f64(f64::INFINITY), (0, 2047, 0));
        assert_eq!(decompose_f64(f64::MIN_POSITIVE), (0, 1, 0));
    }
}
