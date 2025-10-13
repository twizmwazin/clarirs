use serde::{Deserialize, Serialize};
use std::ops::{Add, Div, Mul, Sub};

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
        FSort::new(self.exponent.len(), self.mantissa.len())
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

        // Create 64-bit FPV and later convert to the desired format.
        let float = Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 11)?,
            mantissa: BitVec::from_prim_with_size(mantissa, 52)?,
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
                        BitVec::ones(F64_SORT.exponent),
                        BitVec::ones(F64_SORT.mantissa),
                    ));
                } else if self.is_infinity() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F64_SORT.exponent),
                        BitVec::zeros(F64_SORT.mantissa),
                    ));
                } else if self.is_zero() || self.is_subnormal() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::zeros(F64_SORT.exponent),
                        BitVec::zeros(F64_SORT.mantissa),
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
                    F64_SORT.mantissa,
                );

                Ok(Self::new(
                    self.sign,
                    BitVec::from_prim_with_size(f64_exp, F64_SORT.exponent)?,
                    extended_mantissa?,
                ))
            }
            (F64_SORT, F32_SORT) => {
                // Check for special values first
                if self.is_nan() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F32_SORT.exponent),
                        BitVec::ones(F32_SORT.mantissa),
                    ));
                } else if self.is_infinity() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::ones(F32_SORT.exponent),
                        BitVec::zeros(F32_SORT.mantissa),
                    ));
                } else if self.is_zero() || self.is_subnormal() {
                    return Ok(Self::new(
                        self.sign,
                        BitVec::zeros(F32_SORT.exponent),
                        BitVec::zeros(F32_SORT.mantissa),
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
                    BitVec::from_prim_with_size(f32_exp, F32_SORT.exponent)?,
                    BitVec::from_prim_with_size(truncated_mantissa, F32_SORT.mantissa)?,
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
        // Positive and negative zeros
        if self.is_zero() && other.is_zero() {
            return false; // Both are zero, so they are equal
        }

        // NaNs
        if self.is_nan() || other.is_nan() {
            return false; // NaN is not comparable
        }

        // If the signs differ, the positive number is greater.
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
        // Positive and negative zeros
        if self.is_zero() && other.is_zero() {
            return true; // Both are zero, so they are equal
        }

        // NaNs
        if self.is_nan() || other.is_nan() {
            return false; // NaN is not comparable
        }

        // If the signs differ, the positive number is greater.
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
        // Handle positive and negative zeros
        if self.is_zero() && other.is_zero() {
            return false; // Both are zero, so they are equal
        }

        // Handle NaNs
        if self.is_nan() || other.is_nan() {
            return false; // NaN is not comparable
        }

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
        // Positive and negative zeros
        if self.is_zero() && other.is_zero() {
            return true; // Both are zero, so they are equal
        }

        // NaNs
        if self.is_nan() || other.is_nan() {
            return false; // NaN is not comparable
        }

        // If the signs differ, the positive number is greater.
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
            self_f32.exponent.to_biguint().to_u8()?,
            self_f32.mantissa.to_biguint().to_u32()?,
        ))
    }

    /// Converts the float to an `f64` representation, if possible
    pub fn to_f64(&self) -> Option<f64> {
        let self_f64 = self.to_fsort(F64_SORT, FPRM::NearestTiesToEven).ok()?;
        Some(recompose_f64(
            self.sign as u8,
            self_f64.exponent.to_biguint().to_u16()?,
            self_f64.mantissa.to_u64()?,
        ))
    }

    pub fn convert_to_format(&self, fsort: FSort, fprm: FPRM) -> Result<Self, BitVecError> {
        // Assuming `to_f64()` provides the current float as `f64`, convert it to the new format
        let f64_value = self.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(f64_value, fprm, fsort)
    }

    pub fn from_bigint_with_rounding(
        value: &BigInt,
        fsort: FSort,
        fprm: FPRM,
    ) -> Result<Self, BitVecError> {
        // Convert BigUint to f64 for simplicity in this example
        let float_value = value.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }

    pub fn from_biguint_with_rounding(
        value: &BigUint,
        fsort: FSort,
        fprm: FPRM,
    ) -> Result<Self, BitVecError> {
        // Convert BigUint to f64 for simplicity in this example
        let float_value = value.to_f64().unwrap_or(0.0); // Fallback to 0.0 if conversion fails
        Float::from_f64_with_rounding(float_value, fprm, fsort)
    }

    pub fn shift_with_grs(mut value: BigUint, shift: u32) -> (BigUint, bool, bool) {
        // Right-shifts an unsigned significand exactly as IEEE-754 alignment logic does
        // and reports the extra information needed for correct rounding.

        //  Parameters
        // `value` – significand treated as an unsigned `BigUint`.
        // `shift` – number of bits to shift _right_; must be ≤ value.bit_len().

        //  Returns
        //`(shifted, guard, sticky)` where
        // guard – the bit immediately _below_ the kept LSB (bit `shift − 1` of the original value),
        // shifted – `value >> shift` (the bits that remain after alignment),
        // sticky – logical-OR of all bits further to the right (bits `shift − 2` … 0).

        if shift == 0 {
            return (value, false, false);
        }

        let k = shift as usize;

        let mask = (&BigUint::one() << k) - BigUint::one();
        let shifted_out = &value & &mask;

        // Guard  = the highest of the shifted-out bits (bit k-1)
        let guard = ((&shifted_out >> (k - 1)) & BigUint::one()) == BigUint::one();

        // Sticky = OR of any lower shifted-out bit (k-2 .. 0)
        let sticky = if k > 1 {
            // (1 << (k-1)) − 1 isolates the lower (k-1) bits
            (&shifted_out & ((&BigUint::one() << (k - 1)) - BigUint::one())) != BigUint::zero()
        } else {
            false
        };

        value >>= k; // the actual arithmetic shift
        (value, guard, sticky)
    }
}

impl Add for Float {
    type Output = Result<Float, BitVecError>;

    fn add(self, other: Float) -> Self::Output {
        let mantissa_bits = self.mantissa.len();
        let exponent_bits = self.exponent.len();

        let self_exp = self.exponent.to_biguint().to_u32().unwrap();
        let other_exp = other.exponent.to_biguint().to_u32().unwrap();

        let one = BigUint::one();

        // Effective significands (With implicit 1 for normal numbers)
        let self_eff = if self_exp == 0 {
            self.mantissa.to_biguint()
        } else {
            (&one << mantissa_bits) | self.mantissa.to_biguint()
        };
        let other_eff = if other_exp == 0 {
            other.mantissa.to_biguint()
        } else {
            (&one << mantissa_bits) | other.mantissa.to_biguint()
        };

        let mut guard;
        let mut sticky;

        let result_exp;
        let mut sum;
        let result_sign;

        if self.sign == other.sign {
            // Same Signs:  Add Magnitudes
            if self_exp >= other_exp {
                result_exp = self_exp;
                let (aligned_other, g, s) = Float::shift_with_grs(other_eff, self_exp - other_exp);
                guard = g;
                sticky = s;
                sum = self_eff + aligned_other;
            } else {
                result_exp = other_exp;
                let (aligned_self, g, s) = Float::shift_with_grs(self_eff, other_exp - self_exp);
                guard = g;
                sticky = s;
                sum = aligned_self + other_eff;
            }
            result_sign = self.sign;
        } else {
            // Opposite Signs:  Subtract Smaller Magnitude
            result_exp = self_exp.max(other_exp);

            let (aligned_self, _g1, s1) =
                Float::shift_with_grs(self_eff.clone(), result_exp - self_exp);
            let (aligned_other, g2, s2) =
                Float::shift_with_grs(other_eff.clone(), result_exp - other_exp);

            guard = g2; // guard from the last shift
            sticky = s1 || s2; // OR of everything shifted out

            if aligned_self == aligned_other {
                // Exact cancellation gives +0
                return Ok(Float {
                    sign: false,
                    exponent: BitVec::zeros(exponent_bits),
                    mantissa: BitVec::zeros(mantissa_bits),
                });
            }

            if aligned_self > aligned_other {
                sum = aligned_self - aligned_other;
                result_sign = self.sign;
            } else {
                sum = aligned_other - aligned_self;
                result_sign = other.sign;
            }
        }

        // Normalization
        let lower = &one << mantissa_bits; // 1 << 23
        let upper = &one << (mantissa_bits + 1); // 1 << 24
        let mut exp = result_exp;

        while sum < lower && exp > 0 {
            sum <<= 1;
            exp -= 1;
        }
        if sum >= upper {
            guard = (&sum & &one) == one;
            sticky |= guard;
            sum >>= 1;
            exp = exp.checked_add(1).unwrap();
        }

        // IEEE-754 Round to Nearest
        let lsb_is_one = (&sum & &one) == one;
        if guard && (sticky || lsb_is_one) {
            sum += &one;
            if sum >= upper {
                sum >>= 1;
                exp = exp.checked_add(1).unwrap();
            }
        }

        let stored_mant = if exp > 0 { &sum - &lower } else { sum.clone() };

        let new_exponent = BitVec::from_prim_with_size(exp, exponent_bits)?;
        let mantissa_u32 = stored_mant.to_u32().unwrap();
        let new_mantissa = BitVec::from_prim_with_size(mantissa_u32, mantissa_bits)?;

        Ok(Float {
            sign: result_sign,
            exponent: new_exponent,
            mantissa: new_mantissa,
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
        if self.is_zero() || rhs.is_zero() {
            return Ok(Float {
                sign: self.sign ^ rhs.sign,
                exponent: BitVec::zeros(self.exponent.len()),
                mantissa: BitVec::zeros(self.mantissa.len()),
            });
        }

        let mantissa_bits = self.mantissa.len();
        let exponent_bits = self.exponent.len();
        let bias = (1u32 << (exponent_bits - 1)) - 1;

        let one = (BitVec::ones(32) >> 31)?.to_biguint();

        // Extract & un‑bias exponents
        let self_exp = self.exponent.to_biguint().to_u32().unwrap();
        let rhs_exp = rhs.exponent.to_biguint().to_u32().unwrap();
        let mut result_exp = self_exp.saturating_sub(bias) + rhs_exp.saturating_sub(bias);

        // Effective significands
        let self_eff = if self_exp == 0 {
            self.mantissa.to_biguint()
        } else {
            (one.clone() << mantissa_bits) | self.mantissa.to_biguint()
        };
        let rhs_eff = if rhs_exp == 0 {
            rhs.mantissa.to_biguint()
        } else {
            (one.clone() << mantissa_bits) | rhs.mantissa.to_biguint()
        };

        // Multiply significands
        let mut product = self_eff * rhs_eff;
        let sign = self.sign ^ rhs.sign;

        // Shift back down by mantissa_bits to get a [1.0,4.0) range
        product >>= mantissa_bits;

        // Normalization
        let implicit = one.clone() << mantissa_bits;
        if product >= (implicit.clone() << 1) {
            product >>= 1;
            result_exp = result_exp.checked_add(1).unwrap();
        }

        // Subtract implicit leading‑1 to form the stored mantissa
        let stored = &product - &implicit;

        // Re‑bias exponent
        let biased = result_exp + bias;
        let new_exponent = BitVec::from_prim_with_size(biased, exponent_bits)?;
        let mask = (BigUint::from(1u32) << mantissa_bits) - 1u32;
        let new_mantissa = BitVec::from_biguint(&(&stored & &mask), mantissa_bits)?;

        Ok(Float {
            sign,
            exponent: new_exponent,
            mantissa: new_mantissa,
        })
    }
}

impl Div for Float {
    type Output = Result<Self, BitVecError>;

    fn div(self, rhs: Self) -> Self::Output {
        let exp_bits = self.exponent.len();
        let man_bits = self.mantissa.len();
        let bias = (1u32 << (exp_bits - 1)) - 1;
        let one = (BitVec::ones(32) >> 31)?.to_biguint();

        //  Special cases
        // 0/0 or ∞/∞ → NaN
        if (self.is_zero() && rhs.is_zero()) || (self.is_infinity() && rhs.is_infinity()) {
            return Ok(Float {
                sign: false,
                exponent: BitVec::ones(exp_bits),
                mantissa: BitVec::ones(man_bits),
            });
        }
        // 0/x → ±0
        if self.is_zero() {
            return Ok(Float {
                sign: self.sign ^ rhs.sign,
                exponent: BitVec::zeros(exp_bits),
                mantissa: BitVec::zeros(man_bits),
            });
        }
        // x/0 → ±∞
        if rhs.is_zero() {
            return Ok(Float {
                sign: self.sign ^ rhs.sign,
                exponent: BitVec::ones(exp_bits),
                mantissa: BitVec::zeros(man_bits),
            });
        }
        // ∞/x → ±∞
        if self.is_infinity() {
            return Ok(Float {
                sign: self.sign ^ rhs.sign,
                exponent: BitVec::ones(exp_bits),
                mantissa: BitVec::zeros(man_bits),
            });
        }
        // x/∞ → ±0
        if rhs.is_infinity() {
            return Ok(Float {
                sign: self.sign ^ rhs.sign,
                exponent: BitVec::zeros(exp_bits),
                mantissa: BitVec::zeros(man_bits),
            });
        }

        // Extract unbiased exponents
        let a_exp = self.exponent.to_biguint().to_u32().unwrap();
        let b_exp = rhs.exponent.to_biguint().to_u32().unwrap();
        let a_ub = if a_exp == 0 {
            1u32.wrapping_sub(bias)
        } else {
            a_exp.saturating_sub(bias)
        };
        let b_ub = if b_exp == 0 {
            1u32.wrapping_sub(bias)
        } else {
            b_exp.saturating_sub(bias)
        };

        // Build effective significands (with implicit leading‑1 for normals)
        let a_sig = if a_exp == 0 {
            self.mantissa.to_biguint()
        } else {
            (one.clone() << man_bits) | self.mantissa.to_biguint()
        };
        let b_sig = if b_exp == 0 {
            rhs.mantissa.to_biguint()
        } else {
            (one.clone() << man_bits) | rhs.mantissa.to_biguint()
        };

        //  Fixed‑point divide: shift numerator left by man_bits, then integer‑divide
        let mut quot = (a_sig << man_bits) / b_sig;
        let mut res_ub = a_ub as i64 - b_ub as i64;
        let sign = self.sign ^ rhs.sign;

        //  Normalize to [1<<man_bits, 1<<(man_bits+1))
        let lower = one.clone() << man_bits;
        let upper = one.clone() << (man_bits + 1);

        if quot >= upper {
            quot >>= 1;
            res_ub += 1;
        } else {
            while quot < lower {
                quot <<= 1;
                res_ub -= 1;
            }
        }

        //  Re‑bias exponent
        let rebias = (res_ub + bias as i64).max(0).min((1i64 << exp_bits) - 1) as u32;

        //  Extract stored mantissa (drop implicit 1 if normalized)
        let stored = if rebias == 0 {
            // subnormal or underflow-to-zero
            quot
        } else {
            quot - lower
        };

        let new_exponent = BitVec::from_prim_with_size(rebias, exp_bits)?;
        let mask = (BigUint::from(1u32) << man_bits) - 1u32;
        let new_mantissa = BitVec::from_biguint(&(&stored & &mask), man_bits)?;

        Ok(Float {
            sign,
            exponent: new_exponent,
            mantissa: new_mantissa,
        })
    }
}

impl From<f32> for Float {
    fn from(value: f32) -> Self {
        let (sign, exponent, mantissa) = decompose_f32(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 8)
                .expect("Failed to create BitVec from exponent"),
            mantissa: BitVec::from_prim_with_size(mantissa, 23)
                .expect("Failed to create BitVec from mantissa"),
        }
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        let (sign, exponent, mantissa) = decompose_f64(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 11)
                .expect("Failed to create BitVec from exponent"),
            mantissa: BitVec::from_prim_with_size(mantissa, 52)
                .expect("Failed to create BitVec from mantissa"),
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
            let start = Float::from(value);
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
                // Compare with value converted to f32 to account for precision loss
                assert_eq!(value as f32, result);
            }
        }

        Ok(())
    }
}
