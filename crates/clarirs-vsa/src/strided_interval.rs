use num_bigint::{BigInt, BigUint, ToBigInt, ToBigUint};
use num_traits::{One, ToPrimitive, Zero};
use std::cmp::{max, min};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Shl, Shr, Sub};

use clarirs_core::prelude::*;

/// A StridedInterval represents a set of integers in the form:
/// `<bits> stride[lower_bound, upper_bound]`
///
/// It can represent values within a range that follow a specific stride pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StridedInterval {
    Empty {
        bits: u32,
    },
    Normal {
        bits: u32,
        stride: BigUint,
        lower_bound: BigUint,
        upper_bound: BigUint,
    },
}

/// Represents the result of a comparison operation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComparisonResult {
    True,
    False,
    Maybe,
}

impl ComparisonResult {
    /// Returns true if the result is True
    pub fn is_true(&self) -> bool {
        matches!(self, ComparisonResult::True)
    }

    /// Returns true if the result is False
    pub fn is_false(&self) -> bool {
        matches!(self, ComparisonResult::False)
    }

    /// Returns true if the result is Maybe
    pub fn is_maybe(&self) -> bool {
        matches!(self, ComparisonResult::Maybe)
    }

    pub fn eq_(self, other: ComparisonResult) -> ComparisonResult {
        if self.is_maybe() || other.is_maybe() {
            ComparisonResult::Maybe
        } else if self == other {
            ComparisonResult::True
        } else {
            ComparisonResult::False
        }
    }
}

impl Not for ComparisonResult {
    type Output = ComparisonResult;

    fn not(self) -> ComparisonResult {
        match self {
            ComparisonResult::True => ComparisonResult::False,
            ComparisonResult::False => ComparisonResult::True,
            ComparisonResult::Maybe => ComparisonResult::Maybe,
        }
    }
}

impl BitAnd for ComparisonResult {
    type Output = ComparisonResult;

    fn bitand(self, other: ComparisonResult) -> ComparisonResult {
        match (self, other) {
            (ComparisonResult::True, ComparisonResult::True) => ComparisonResult::True,
            (ComparisonResult::False, _) | (_, ComparisonResult::False) => ComparisonResult::False,
            _ => ComparisonResult::Maybe,
        }
    }
}

impl BitOr for ComparisonResult {
    type Output = ComparisonResult;

    fn bitor(self, other: ComparisonResult) -> ComparisonResult {
        match (self, other) {
            (ComparisonResult::True, _) | (_, ComparisonResult::True) => ComparisonResult::True,
            (ComparisonResult::False, ComparisonResult::False) => ComparisonResult::False,
            _ => ComparisonResult::Maybe,
        }
    }
}

impl BitXor for ComparisonResult {
    type Output = ComparisonResult;

    fn bitxor(self, other: ComparisonResult) -> ComparisonResult {
        match (self, other) {
            (ComparisonResult::True, ComparisonResult::False) => ComparisonResult::True,
            (ComparisonResult::False, ComparisonResult::True) => ComparisonResult::True,
            (ComparisonResult::True, ComparisonResult::True)
            | (ComparisonResult::False, ComparisonResult::False) => ComparisonResult::False,
            _ => ComparisonResult::Maybe,
        }
    }
}

impl StridedInterval {
    /// Check if the interval contains a specific value
    pub fn contains_value(&self, value: &BigUint) -> bool {
        match self {
            StridedInterval::Empty { .. } => false,
            StridedInterval::Normal {
                stride,
                lower_bound,
                ..
            } => {
                let (min, max) = self.get_unsigned_bounds();
                if value < &min || value > &max {
                    return false;
                }
                if stride.is_zero() {
                    return lower_bound == value;
                }
                (&(value - lower_bound) % stride).is_zero()
            }
        }
    }

    /// Creates a new StridedInterval with the given parameters
    pub fn new(bits: u32, stride: BigUint, lower_bound: BigUint, upper_bound: BigUint) -> Self {
        let mut si = StridedInterval::Normal {
            bits,
            stride,
            lower_bound,
            upper_bound,
        };
        si.normalize();
        si
    }

    /// Creates a StridedInterval representing a single concrete value
    pub fn constant(bits: u32, value: impl ToBigUint) -> Self {
        let value = value.to_biguint().unwrap();
        Self::new(bits, BigUint::zero(), value.clone(), value)
    }

    /// Creates a StridedInterval representing the entire range of values for the given bit width
    pub fn top(bits: u32) -> Self {
        Self::new(bits, BigUint::one(), BigUint::zero(), Self::max_int(bits))
    }

    /// Creates an empty StridedInterval (bottom)
    pub fn empty(bits: u32) -> Self {
        StridedInterval::Empty { bits }
    }

    /// Creates a StridedInterval from a range with stride 1
    pub fn range(bits: u32, lower: impl ToBigUint, upper: impl ToBigUint) -> Self {
        Self::new(
            bits,
            BigUint::one(),
            lower.to_biguint().unwrap(),
            upper.to_biguint().unwrap(),
        )
    }

    /// Normalizes the StridedInterval
    pub fn normalize(&mut self) {
        match self {
            StridedInterval::Empty { .. } => (),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                // Ensure bounds are within the bit range
                let max_value = Self::max_int(*bits);
                *lower_bound = &*lower_bound & &max_value;
                *upper_bound = &*upper_bound & &max_value;

                // If lower_bound == upper_bound, stride should be 0
                if *lower_bound == *upper_bound {
                    *stride = BigUint::zero();
                } else if stride.is_zero() {
                    // Defensive: zero stride but not singleton is invalid, set stride to 1
                    *stride = BigUint::one();
                }

                // Normalize top value
                if *stride == BigUint::one()
                    && Self::modular_add(&*upper_bound, &BigUint::one(), *bits) == *lower_bound
                    && *lower_bound == BigUint::zero()
                    && *upper_bound == Self::max_int(*bits)
                {
                    *lower_bound = BigUint::zero();
                    *upper_bound = Self::max_int(*bits);
                }
            }
        }
    }

    /// Returns the maximum unsigned integer representable with the given bits
    pub fn max_int(bits: u32) -> BigUint {
        (BigUint::one() << bits) - BigUint::one()
    }

    /// Returns the minimum signed integer representable with the given bits
    pub fn min_int(bits: u32) -> BigUint {
        BigUint::one() << (bits - 1)
    }

    /// Returns the maximum signed integer representable with the given bits
    pub fn signed_max_int(bits: u32) -> BigUint {
        (BigUint::one() << (bits - 1)) - BigUint::one()
    }

    /// Performs modular addition of two BigUint values with the given bit width
    pub fn modular_add(a: &BigUint, b: &BigUint, bits: u32) -> BigUint {
        let mask = Self::max_int(bits);
        (a + b) & mask
    }

    /// Performs modular subtraction of two BigUint values with the given bit width
    pub fn modular_sub(a: &BigUint, b: &BigUint, bits: u32) -> BigUint {
        let modulus = BigUint::one() << bits;
        if a >= b {
            (a - b) & Self::max_int(bits)
        } else {
            (modulus + a - b) & Self::max_int(bits)
        }
    }

    /// Performs modular multiplication of two BigUint values with the given bit width
    pub fn modular_mul(a: &BigUint, b: &BigUint, bits: u32) -> BigUint {
        (a * b) & Self::max_int(bits)
    }

    /// Checks if the StridedInterval is empty (bottom)
    pub fn is_empty(&self) -> bool {
        matches!(self, StridedInterval::Empty { .. })
    }

    /// Checks if the StridedInterval represents a single concrete value
    pub fn is_integer(&self) -> bool {
        match self {
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                ..
            } => lower_bound == upper_bound,
            _ => false,
        }
    }

    /// Checks if the StridedInterval represents the entire range of values
    pub fn is_top(&self) -> bool {
        match self {
            StridedInterval::Normal {
                stride,
                lower_bound,
                upper_bound,
                bits,
            } => {
                !self.is_empty()
                    && *stride == BigUint::one()
                    && *lower_bound == BigUint::zero()
                    && *upper_bound == Self::max_int(*bits)
            }
            _ => false,
        }
    }

    /// Returns the cardinality (number of values) in the StridedInterval
    pub fn cardinality(&self) -> BigUint {
        match self {
            StridedInterval::Empty { .. } => BigUint::zero(),
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                stride,
                ..
            } => {
                if lower_bound == upper_bound {
                    return BigUint::one();
                }
                if stride.is_zero() {
                    if lower_bound == upper_bound {
                        return BigUint::one();
                    } else {
                        return BigUint::zero();
                    }
                }
                let range = if upper_bound >= lower_bound {
                    upper_bound - lower_bound + BigUint::one()
                } else {
                    let max_val = Self::max_int(self.bits());
                    &max_val - lower_bound + upper_bound + BigUint::one()
                };
                (range + stride - BigUint::one()) / stride
            }
        }
    }

    /// Finds the intersection of two StridedIntervals
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::empty(max(self.bits(), other.bits()));
        }

        if self.bits() != other.bits() {
            // Create a copy with matching bits
            match other {
                StridedInterval::Normal {
                    stride,
                    lower_bound,
                    upper_bound,
                    ..
                } => {
                    let extended_other = Self::new(
                        self.bits(),
                        stride.clone(),
                        lower_bound.clone(),
                        upper_bound.clone(),
                    );
                    return self.intersection(&extended_other);
                }
                StridedInterval::Empty { .. } => {
                    return self.intersection(&Self::empty(self.bits()));
                }
            }
        }

        // Check if ranges overlap
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        // Simple case: one interval is contained within the other
        if let (
            StridedInterval::Normal {
                stride: s_stride, ..
            },
            StridedInterval::Normal {
                stride: o_stride, ..
            },
        ) = (self, other)
        {
            if self_min >= other_min
                && self_max <= other_max
                && (s_stride.is_zero()
                    || o_stride.is_zero()
                    || s_stride % o_stride == BigUint::zero())
            {
                return self.clone();
            }
            if other_min >= self_min
                && other_max <= self_max
                && (s_stride.is_zero()
                    || o_stride.is_zero()
                    || o_stride % s_stride == BigUint::zero())
            {
                return other.clone();
            }
        }

        // Handle non-overlapping case
        if (self_min > other_max && self_max > other_max)
            || (other_min > self_max && other_max > self_max)
        {
            return Self::empty(self.bits());
        }

        // Robust handling of zero strides to avoid division by zero
        if let (
            StridedInterval::Normal {
                stride: s_stride,
                lower_bound: s_lb,
                ..
            },
            StridedInterval::Normal {
                stride: o_stride,
                lower_bound: o_lb,
                ..
            },
        ) = (self, other)
        {
            if s_stride.is_zero() && o_stride.is_zero() {
                if s_lb == o_lb {
                    return self.clone();
                } else {
                    return Self::empty(self.bits());
                }
            }
            if s_stride.is_zero() {
                if other.contains(self) {
                    return self.clone();
                } else {
                    return Self::empty(self.bits());
                }
            }
            if o_stride.is_zero() {
                if self.contains(other) {
                    return other.clone();
                } else {
                    return Self::empty(self.bits());
                }
            }
        }

        let (gcd, s_stride, o_stride) = match (self, other) {
            (
                StridedInterval::Normal {
                    stride: s_stride, ..
                },
                StridedInterval::Normal {
                    stride: o_stride, ..
                },
            ) => {
                let gcd = Self::gcd(s_stride, o_stride);
                (gcd, s_stride, o_stride)
            }
            _ => (BigUint::zero(), &BigUint::zero(), &BigUint::zero()),
        };
        let new_stride = if gcd.is_zero() {
            BigUint::zero()
        } else {
            (s_stride * o_stride) / &gcd
        };

        // Find the smallest value >= lower_bound that satisfies both intervals
        let new_lower = max(self_min, other_min);
        let new_upper = min(self_max, other_max);

        Self::new(self.bits(), new_stride, new_lower, new_upper)
    }

    /// Finds the union of two StridedIntervals
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        if self.bits() != other.bits() {
            // Create a copy with matching bits
            match other {
                StridedInterval::Normal {
                    stride,
                    lower_bound,
                    upper_bound,
                    ..
                } => {
                    let extended_other = Self::new(
                        self.bits(),
                        stride.clone(),
                        lower_bound.clone(),
                        upper_bound.clone(),
                    );
                    return self.union(&extended_other);
                }
                StridedInterval::Empty { .. } => {
                    return self.union(&Self::empty(self.bits()));
                }
            }
        }

        // Simple case: one interval is contained within the other
        if self.contains(other) {
            return self.clone();
        }
        if other.contains(self) {
            return other.clone();
        }

        // Calculate the new bounds
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        let new_lower = min(self_min, other_min);
        let new_upper = max(self_max, other_max);

        // For union, handle special cases to avoid GCD(0,0) and division by zero
        let new_stride = match (self, other) {
            (
                StridedInterval::Normal {
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    stride: o_stride,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                if s_stride.is_zero() && o_stride.is_zero() {
                    if s_lb == o_lb && s_ub == o_ub {
                        BigUint::zero()
                    } else if s_lb > o_lb {
                        s_lb - o_lb
                    } else {
                        o_lb - s_lb
                    }
                } else if s_stride.is_zero() {
                    o_stride.clone()
                } else if o_stride.is_zero() {
                    s_stride.clone()
                } else {
                    Self::gcd(s_stride, o_stride)
                }
            }
            _ => BigUint::one(),
        };

        Self::new(self.bits(), new_stride, new_lower, new_upper)
    }

    /// Checks if this StridedInterval contains another
    pub fn contains(&self, other: &Self) -> bool {
        if self.is_empty() {
            return false;
        }
        if other.is_empty() {
            return true;
        }

        if self.bits() != other.bits() {
            return false;
        }

        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        // Check if bounds are contained
        let bounds_contained = self_min <= other_min && self_max >= other_max;

        // Check if stride is compatible
        let stride_compatible = match (self, other) {
            (
                StridedInterval::Normal {
                    stride: s_stride,
                    lower_bound: s_lb,
                    ..
                },
                StridedInterval::Normal {
                    stride: o_stride,
                    lower_bound: o_lb,
                    ..
                },
            ) => {
                if s_stride.is_zero() {
                    s_lb == o_lb && o_stride.is_zero()
                } else {
                    o_stride % s_stride == BigUint::zero()
                }
            }
            _ => false,
        };

        bounds_contained && stride_compatible
    }

    /// Returns the bit width of the interval
    pub fn bits(&self) -> u32 {
        match self {
            StridedInterval::Empty { bits } => *bits,
            StridedInterval::Normal { bits, .. } => *bits,
        }
    }

    /// Gets the unsigned bounds as a tuple (min, max)
    pub fn get_unsigned_bounds(&self) -> (BigUint, BigUint) {
        match self {
            StridedInterval::Empty { .. } => (BigUint::zero(), BigUint::zero()),
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                bits,
                ..
            } => {
                if upper_bound >= lower_bound {
                    (lower_bound.clone(), upper_bound.clone())
                } else if self.is_top() {
                    (BigUint::zero(), Self::max_int(*bits))
                } else {
                    (lower_bound.clone(), Self::max_int(*bits))
                }
            }
        }
    }

    /// Gets the signed bounds as a tuple (min, max) considering two's complement
    pub fn get_signed_bounds(&self) -> (BigInt, BigInt) {
        match self {
            StridedInterval::Empty { .. } => (BigInt::zero(), BigInt::zero()),
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                bits,
                ..
            } => {
                let msb_mask = BigUint::one() << (*bits - 1);
                let to_signed = |v: &BigUint| -> BigInt {
                    if (v & &msb_mask) != BigUint::zero() {
                        v.to_bigint().unwrap() - (BigInt::one() << *bits)
                    } else {
                        v.to_bigint().unwrap()
                    }
                };
                if upper_bound >= lower_bound {
                    (to_signed(lower_bound), to_signed(upper_bound))
                } else if self.is_top() {
                    (BigInt::zero(), (BigInt::one() << *bits) - BigInt::one())
                } else {
                    // For wrap-around intervals, we need to consider the signed interpretation
                    // of the bounds. The minimum is the signed value of lower_bound,
                    // and the maximum is the signed value of upper_bound.
                    (to_signed(lower_bound), to_signed(upper_bound))
                }
            }
        }
    }

    /// Compute the greatest common divisor of two BigUint values
    fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
        if a.is_zero() && b.is_zero() {
            BigUint::one()
        } else if b.is_zero() {
            a.clone()
        } else {
            Self::gcd(b, &(a % b))
        }
    }

    /// Check if the interval contains zero
    pub fn contains_zero(&self) -> bool {
        match self {
            StridedInterval::Empty { .. } => false,
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                ..
            } => {
                if lower_bound <= upper_bound {
                    BigUint::zero() >= *lower_bound && BigUint::zero() <= *upper_bound
                } else {
                    // Wrap-around case
                    // 0 is contained if it's >= lower_bound or <= upper_bound
                    BigUint::zero() >= *lower_bound || BigUint::zero() <= *upper_bound
                }
            }
        }
    }

    /// Check if this interval is definitely less than another (unsigned comparison)
    pub fn is_less_than(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get the maximum of self and minimum of other
        let (_, self_max) = self.get_unsigned_bounds();
        let (other_min, _) = other.get_unsigned_bounds();

        match (self, other) {
            (
                StridedInterval::Normal {
                    upper_bound: self_ub,
                    ..
                },
                StridedInterval::Normal {
                    lower_bound: other_lb,
                    ..
                },
            ) => {
                if self_max < other_min || self_ub < other_lb {
                    ComparisonResult::True
                } else if let StridedInterval::Normal {
                    lower_bound: self_lb,
                    ..
                } = self
                {
                    if self_lb > other_lb {
                        ComparisonResult::False
                    } else {
                        ComparisonResult::Maybe
                    }
                } else {
                    ComparisonResult::Maybe
                }
            }
            _ => ComparisonResult::Maybe,
        }
    }

    /// Check if this interval is definitely less than or equal to another (unsigned comparison)
    pub fn is_less_than_or_equal(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get the maximum of self and minimum of other
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        if self_max <= other_min {
            ComparisonResult::True
        } else if self_min > other_max {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
        }
    }

    /// Check if this interval is definitely equal to another, returning a ComparisonResult
    pub fn eq_(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        let self_lb = match self {
            StridedInterval::Normal { lower_bound, .. } => lower_bound,
            _ => return ComparisonResult::False,
        };
        let other_lb = match other {
            StridedInterval::Normal { lower_bound, .. } => lower_bound,
            _ => return ComparisonResult::False,
        };

        if self.is_integer() && other.is_integer() && self_lb == other_lb {
            return ComparisonResult::True;
        }

        // If intervals don't overlap, they can't be equal
        let intersection = self.intersection(other);
        if intersection.is_empty() {
            return ComparisonResult::False;
        }

        if self.is_integer() && other.is_integer() && self_lb == other_lb {
            return ComparisonResult::True;
        }

        // Otherwise, maybe
        ComparisonResult::Maybe
    }

    /// Check if this interval is definitely not equal to another, returning a ComparisonResult
    pub fn ne_(&self, other: &Self) -> ComparisonResult {
        // Using the logical not of equality
        !self.eq_(other)
    }

    /// Check if this interval is definitely less than another in unsigned comparison
    pub fn ult(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get unsigned bounds
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        if self_max < other_min {
            ComparisonResult::True
        } else if self_min >= other_max {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
        }
    }

    /// Check if this interval is definitely less than or equal to another in unsigned comparison
    pub fn ule(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get unsigned bounds
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        if self_max <= other_min {
            ComparisonResult::True
        } else if self_min > other_max {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
        }
    }

    /// Check if this interval is definitely greater than another in unsigned comparison
    pub fn ugt(&self, other: &Self) -> ComparisonResult {
        // Reverse the comparison
        other.ult(self)
    }

    /// Check if this interval is definitely greater than or equal to another in unsigned comparison
    pub fn uge(&self, other: &Self) -> ComparisonResult {
        // Reverse the comparison
        other.ule(self)
    }

    /// Check if this interval is definitely less than another in signed comparison
    pub fn slt(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get signed bounds
        let (self_min, self_max) = self.get_signed_bounds();
        let (other_min, other_max) = other.get_signed_bounds();

        if self_max < other_min {
            ComparisonResult::True
        } else if self_min >= other_max {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
        }
    }

    /// Check if this interval is definitely less than or equal to another in signed comparison
    pub fn sle(&self, other: &Self) -> ComparisonResult {
        if self.is_empty() || other.is_empty() {
            return ComparisonResult::False;
        }

        // Get signed bounds
        let (self_min, self_max) = self.get_signed_bounds();
        let (other_min, other_max) = other.get_signed_bounds();

        if self_max <= other_min {
            ComparisonResult::True
        } else if self_min > other_max {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
        }
    }

    /// Check if this interval is definitely greater than another in signed comparison
    pub fn sgt(&self, other: &Self) -> ComparisonResult {
        // Reverse the comparison
        other.slt(self)
    }

    /// Check if this interval is definitely greater than or equal to another in signed comparison
    pub fn sge(&self, other: &Self) -> ComparisonResult {
        // Reverse the comparison
        other.sle(self)
    }

    /// Evaluates the interval to get a set of concrete values
    /// Returns at most `limit` values
    pub fn eval(&self, limit: u32) -> Vec<BigUint> {
        if self.is_empty() {
            return vec![];
        }

        match self {
            StridedInterval::Normal {
                lower_bound,
                upper_bound,
                stride,
                bits,
            } => {
                if lower_bound == upper_bound || stride.is_zero() {
                    return vec![lower_bound.clone()];
                }

                let mut results = Vec::new();

                if lower_bound <= upper_bound {
                    // No wrap-around
                    let mut value = lower_bound.clone();
                    while value <= *upper_bound && results.len() < limit as usize {
                        results.push(value.clone());
                        value += stride;
                    }
                } else {
                    // Wrap-around case
                    let max_value = Self::max_int(*bits);

                    // First part: from lower_bound to max_value
                    let mut value = lower_bound.clone();
                    while value <= max_value && results.len() < limit as usize {
                        results.push(value.clone());
                        value += stride;
                    }

                    // Second part: from 0 to upper_bound
                    if results.len() < limit as usize {
                        // Start from 0 and check if it's part of the stride pattern
                        let mut value = BigUint::zero();

                        // Check if 0 is aligned with the stride pattern
                        let distance_from_lower = Self::modular_sub(&value, lower_bound, *bits);

                        if (&distance_from_lower % stride) == BigUint::zero() {
                            // 0 is part of the pattern
                            while value <= *upper_bound && results.len() < limit as usize {
                                results.push(value.clone());
                                value += stride;
                            }
                        } else {
                            // Find the first value >= 0 that's part of the pattern
                            let remainder = &distance_from_lower % stride;
                            let offset = stride - remainder;
                            value = offset;
                            while value <= *upper_bound && results.len() < limit as usize {
                                results.push(value.clone());
                                value += stride;
                            }
                        }
                    }
                }

                results
            }
            StridedInterval::Empty { .. } => vec![],
        }
    }

    /// Creates a StridedInterval representing a range from 0 to 2^bits - 1 with the specified stride
    pub fn strided_range(bits: u32, stride: impl ToBigUint) -> Self {
        Self::new(
            bits,
            stride.to_biguint().unwrap(),
            BigUint::zero(),
            Self::max_int(bits),
        )
    }

    /// Creates a StridedInterval from a custom range with a specified stride
    pub fn strided_bounds(
        bits: u32,
        stride: impl ToBigUint,
        lower: impl ToBigUint,
        upper: impl ToBigUint,
    ) -> Self {
        Self::new(
            bits,
            stride.to_biguint().unwrap(),
            lower.to_biguint().unwrap(),
            upper.to_biguint().unwrap(),
        )
    }

    /// Return the complement of the interval (all values not in the interval)
    pub fn complement(&self) -> Self {
        if self.is_empty() {
            return Self::top(self.bits());
        }

        if self.is_top() {
            return Self::empty(self.bits());
        }

        // Handle the case of a singleton value
        if self.is_integer() {
            if let StridedInterval::Normal {
                lower_bound,
                upper_bound,
                bits,
                ..
            } = self
            {
                let lower = Self::modular_add(upper_bound, &BigUint::one(), *bits);
                let upper = Self::modular_sub(lower_bound, &BigUint::one(), *bits);
                return Self::new(*bits, BigUint::one(), lower, upper);
            }
        }

        // For the general case
        match self {
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                if *stride > BigUint::one() {
                    // Complex case: we need to calculate the values between the intervals
                    // For simplicity, we'll return a conservative approximation
                    // A more precise implementation could return a set of intervals
                    let lower = Self::modular_add(upper_bound, &BigUint::one(), *bits);
                    let upper = Self::modular_sub(lower_bound, &BigUint::one(), *bits);
                    return Self::new(*bits, BigUint::one(), lower, upper);
                }
                // For stride 1, simply invert the range
                let lower = Self::modular_add(upper_bound, &BigUint::one(), *bits);
                let upper = Self::modular_sub(lower_bound, &BigUint::one(), *bits);
                Self::new(*bits, BigUint::one(), lower, upper)
            }
            _ => Self::empty(self.bits()),
        }
    }

    /// Test if this interval has an empty intersection with another
    pub fn is_disjoint_from(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }

    /// Create a widened interval by extending bounds
    pub fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (StridedInterval::Empty { .. }, _) => other.clone(),
            (_, StridedInterval::Empty { .. }) => self.clone(),
            (
                StridedInterval::Normal {
                    bits: bits1,
                    stride: stride1,
                    lower_bound: lb1,
                    upper_bound: ub1,
                },
                StridedInterval::Normal {
                    bits: bits2,
                    stride: stride2,
                    lower_bound: lb2,
                    upper_bound: ub2,
                },
            ) => {
                // If the intervals have different bit widths, normalize
                if bits1 != bits2 {
                    return self.widen(&StridedInterval::Normal {
                        bits: *bits1,
                        stride: stride2.clone(),
                        lower_bound: lb2.clone(),
                        upper_bound: ub2.clone(),
                    });
                }

                let new_lower = if lb2 < lb1 { lb2.clone() } else { lb1.clone() };
                let new_upper = if ub2 > ub1 { ub2.clone() } else { ub1.clone() };
                let new_stride = Self::gcd(stride1, stride2);

                StridedInterval::new(*bits1, new_stride, new_lower, new_upper)
            }
        }
    }

    /// Extract bits from the interval (similar to bitslice)
    pub fn extract(&self, high_bit: u32, low_bit: u32) -> Self {
        if self.is_empty() {
            return Self::empty(high_bit - low_bit + 1);
        }

        if low_bit >= self.bits() || high_bit >= self.bits() || high_bit < low_bit {
            return Self::empty(high_bit - low_bit + 1);
        }

        match self {
            StridedInterval::Normal {
                stride,
                lower_bound,
                upper_bound,
                ..
            } => {
                // First shift right by low_bit
                let shifted_lower = lower_bound >> low_bit;
                let shifted_upper = upper_bound >> low_bit;

                // Then mask to only keep the bits we want
                let mask = (BigUint::one() << (high_bit - low_bit + 1)) - BigUint::one();
                let new_lower = &shifted_lower & &mask;
                let new_upper = &shifted_upper & &mask;

                // Compute new stride - preserve if possible
                let new_stride = if stride.is_zero() {
                    BigUint::zero()
                } else {
                    // Check if stride is preserved after extraction
                    let shift_divisor = BigUint::one() << low_bit;
                    
                    // If stride is divisible by 2^low_bit, we can preserve it
                    if stride % &shift_divisor == BigUint::zero() {
                        let preserved_stride = stride / &shift_divisor;
                        // Make sure the preserved stride doesn't exceed the new range
                        let range = if &new_upper >= &new_lower {
                            &new_upper - &new_lower
                        } else {
                            BigUint::zero()
                        };
                        if &preserved_stride <= &range {
                            preserved_stride
                        } else {
                            BigUint::one()
                        }
                    } else {
                        // Find GCD to get the best stride we can preserve
                        let gcd = Self::gcd(stride, &shift_divisor);
                        if gcd > BigUint::one() {
                            let candidate = &gcd / &shift_divisor;
                            if candidate.is_zero() {
                                BigUint::one()
                            } else {
                                candidate
                            }
                        } else {
                            BigUint::one()
                        }
                    }
                };

                Self::new(high_bit - low_bit + 1, new_stride, new_lower, new_upper)
            }
            StridedInterval::Empty { .. } => Self::empty(high_bit - low_bit + 1),
        }
    }

    /// Concatenate two intervals (high bits from self, low bits from other)
    pub fn concat(&self, other: &Self) -> Self {
        match (self, other) {
            (StridedInterval::Empty { bits: bits1 }, StridedInterval::Empty { bits: bits2 }) => {
                Self::empty(bits1 + bits2)
            }
            (
                StridedInterval::Empty { bits },
                StridedInterval::Normal {
                    bits: other_bits, ..
                },
            ) => Self::empty(bits + other_bits),
            (StridedInterval::Normal { bits, .. }, StridedInterval::Empty { bits: other_bits }) => {
                Self::empty(bits + other_bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    stride: stride1,
                    lower_bound: lb1,
                    upper_bound: ub1,
                },
                StridedInterval::Normal {
                    bits: bits2,
                    stride: stride2,
                    lower_bound: lb2,
                    upper_bound: ub2,
                },
            ) => {
                // Simple case: if both are constants
                if lb1 == ub1 && lb2 == ub2 {
                    let new_value = (lb1 << bits2) | lb2;
                    return Self::constant(bits1 + bits2, new_value);
                }

                // Improved stride computation
                let new_stride = if stride1.is_zero() && stride2.is_zero() {
                    BigUint::zero()
                } else if stride1.is_zero() {
                    // High bits constant, low bits have stride
                    stride2.clone()
                } else if stride2.is_zero() {
                    // Low bits constant, high bits have stride
                    stride1 << bits2
                } else {
                    // Both have strides - use GCD of their contribution
                    let high_contribution = stride1 << bits2;
                    Self::gcd(&high_contribution, stride2)
                };

                // General case - compute all corner combinations
                let a = lb1 << bits2;
                let b = ub1 << bits2;
                let c = lb2;
                let d = ub2;

                let ac = &a | c;
                let ad = &a | d;
                let bc = &b | c;
                let bd = &b | d;

                let new_lower = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
                let new_upper = ac.max(ad).max(bc).max(bd);

                Self::new(bits1 + bits2, new_stride, new_lower, new_upper)
            }
        }
    }

    /// Zero-extend the interval to a new bit width
    pub fn zero_extend(&self, new_bits: u32) -> Self {
        match self {
            StridedInterval::Empty { .. } => Self::empty(new_bits),
            StridedInterval::Normal {
                stride,
                lower_bound,
                upper_bound,
                ..
            } => {
                if new_bits <= self.bits() {
                    return self.clone();
                }
                Self::new(
                    new_bits,
                    stride.clone(),
                    lower_bound.clone(),
                    upper_bound.clone(),
                )
            }
        }
    }

    /// Sign-extend the interval to a new bit width
    pub fn sign_extend(&self, new_bits: u32) -> Self {
        match self {
            StridedInterval::Empty { .. } => Self::empty(new_bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                if new_bits <= *bits {
                    return self.clone();
                }

                let sign_bit_mask = BigUint::one() << (*bits - 1);
                let extension_bits = new_bits - *bits;
                let extension_mask = (BigUint::one() << extension_bits) - BigUint::one();

                let new_lower = if lower_bound & &sign_bit_mask != BigUint::zero() {
                    lower_bound | (&extension_mask << *bits)
                } else {
                    lower_bound.clone()
                };

                let new_upper = if upper_bound & &sign_bit_mask != BigUint::zero() {
                    upper_bound | (&extension_mask << *bits)
                } else {
                    upper_bound.clone()
                };

                Self::new(new_bits, stride.clone(), new_lower, new_upper)
            }
        }
    }

    /// Performs unsigned division
    pub fn udiv(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                },
                StridedInterval::Normal {
                    bits: bits2,
                    stride: o_stride,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                },
            ) => {
                let bits = max(*bits1, *bits2);

                // Avoid division by zero
                if (o_lb == &BigUint::zero() && o_ub == &BigUint::zero())
                    || (o_stride.is_zero() && o_lb.is_zero())
                    || other.contains_zero()
                {
                    return Ok(Self::top(bits));
                }

                // Simple case: dividing by a constant
                if o_lb == o_ub {
                    let divisor = o_lb.clone();
                    let new_stride = if s_stride == &BigUint::zero() {
                        BigUint::zero()
                    } else {
                        BigUint::one()
                    };
                    let new_lower = s_lb / &divisor;
                    let new_upper = s_ub / &divisor;
                    return Ok(Self::new(bits, new_stride, new_lower, new_upper));
                }

                // Special case: numerator is constant, denominator is interval
                if s_lb == s_ub {
                    let dividend = s_lb.clone();
                    let (c, d) = (o_lb, o_ub);

                    let mut min_val = &dividend / d;
                    let mut max_val = &dividend / c;

                    if min_val > max_val {
                        std::mem::swap(&mut min_val, &mut max_val);
                    }

                    return Ok(Self::new(bits, BigUint::one(), min_val, max_val));
                }

                // General case: both numerator and denominator are intervals
                let (a, b) = (s_lb, s_ub);
                let (c, d) = (o_lb, o_ub);

                let ac = if *c != BigUint::zero() {
                    a / c
                } else {
                    BigUint::zero()
                };
                let ad = if *d != BigUint::zero() {
                    a / d
                } else {
                    BigUint::zero()
                };
                let bc = if *c != BigUint::zero() {
                    b / c
                } else {
                    BigUint::zero()
                };
                let bd = if *d != BigUint::zero() {
                    b / d
                } else {
                    BigUint::zero()
                };

                let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
                let max_val = ac.max(ad).max(bc).max(bd);

                Ok(Self::new(bits, BigUint::one(), min_val, max_val))
            }
        }
    }

    /// Performs signed division
    pub fn sdiv(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal { bits: bits1, .. },
                StridedInterval::Normal {
                    bits: bits2,
                    stride: o_stride,
                    lower_bound: o_lb,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);

                // Avoid division by zero
                if (o_stride.is_zero() && o_lb.is_zero()) || other.contains_zero() {
                    return Ok(Self::top(bits));
                }

                // Simple case: both are constants
                if self.is_integer() && other.is_integer() {
                    let (self_signed, _) = self.get_signed_bounds();
                    let (other_signed, _) = other.get_signed_bounds();

                    // Perform signed division
                    let result = self_signed / other_signed;

                    // Convert back to unsigned representation
                    let result_unsigned = if result < BigInt::zero() {
                        // For negative results, compute two's complement
                        let abs_result = -result.clone();
                        let mask = Self::max_int(bits);
                        (&mask + BigUint::one() - abs_result.to_biguint().unwrap()) & &mask
                    } else {
                        result.to_biguint().unwrap()
                    };

                    return Ok(Self::constant(bits, result_unsigned));
                }

                // For the general case, provide a conservative approximation
                Ok(Self::top(bits))
            }
        }
    }

    /// Performs unsigned remainder
    pub fn urem(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(StridedInterval::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    lower_bound: s_lb,
                    ..
                },
                StridedInterval::Normal {
                    bits: bits2,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);

                // Simple case: both are constants
                if s_lb == o_lb && s_lb == o_ub {
                    let result = s_lb % o_lb;
                    return Ok(StridedInterval::constant(bits, result));
                }

                // If divisor is a constant
                if o_lb == o_ub {
                    let max_remainder = o_lb - BigUint::one();
                    return Ok(StridedInterval::range(bits, 0u32, max_remainder));
                }

                // If divisor is a range, the remainder can be from 0 to max(divisor)-1
                let (_, other_max) = other.get_unsigned_bounds();
                Ok(StridedInterval::range(
                    bits,
                    0u32,
                    &other_max - BigUint::one(),
                ))
            }
        }
    }

    /// Performs signed remainder
    pub fn srem(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::empty(max(self.bits(), other.bits())));
        }

        // // Check for division by zero
        // if other.contains_zero() {
        //     return Err(ClarirsError::DivideByZero);
        // }

        let bits = max(self.bits(), other.bits());

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            let (self_signed, _) = self.get_signed_bounds();
            let (other_signed, _) = other.get_signed_bounds();

            // Perform signed remainder
            let result = self_signed % other_signed;

            // Convert back to unsigned representation
            let result_unsigned = if result < BigInt::zero() {
                // For negative results, compute two's complement
                let abs_result = -result.clone();
                let mask = Self::max_int(bits);

                (&mask + BigUint::one() - abs_result.to_biguint().unwrap()) & &mask
            } else {
                result.to_biguint().unwrap()
            };

            return Ok(Self::constant(bits, result_unsigned));
        }

        // For the general case, we need to take the sign of the dividend into account
        // This is a conservative approximation
        Ok(Self::top(bits))
    }

    /// Shifts left with another interval as the shift amount
    pub fn shl(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits,
                    stride,
                    lower_bound,
                    upper_bound,
                },
                StridedInterval::Normal {
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                // Simple case: constant shift amount
                if o_lb == o_ub {
                    if let Some(shift) = o_lb.to_u32() {
                        if shift >= *bits {
                            return Ok(Self::constant(*bits, 0));
                        }
                        let factor = BigUint::one() << shift;
                        let new_stride = stride * &factor;
                        let new_lower = StridedInterval::modular_mul(lower_bound, &factor, *bits);
                        let new_upper = StridedInterval::modular_mul(upper_bound, &factor, *bits);
                        return Ok(Self::new(*bits, new_stride, new_lower, new_upper));
                    }
                }
                
                // Improved: compute union of min and max shift results
                if let (Some(min_shift), Some(max_shift)) = (o_lb.to_u32(), o_ub.to_u32()) {
                    let min_shift = min_shift.min(*bits);
                    let max_shift = max_shift.min(*bits);
                    
                    // Compute result for minimum shift
                    let min_result = if min_shift >= *bits {
                        Self::constant(*bits, 0)
                    } else {
                        let factor = BigUint::one() << min_shift;
                        let new_lower = StridedInterval::modular_mul(lower_bound, &factor, *bits);
                        let new_upper = StridedInterval::modular_mul(upper_bound, &factor, *bits);
                        Self::new(*bits, BigUint::one(), new_lower, new_upper)
                    };
                    
                    // Compute result for maximum shift
                    let max_result = if max_shift >= *bits {
                        Self::constant(*bits, 0)
                    } else {
                        let factor = BigUint::one() << max_shift;
                        let new_lower = StridedInterval::modular_mul(lower_bound, &factor, *bits);
                        let new_upper = StridedInterval::modular_mul(upper_bound, &factor, *bits);
                        Self::new(*bits, BigUint::one(), new_lower, new_upper)
                    };
                    
                    return Ok(min_result.union(&max_result));
                }
                
                // Fallback to top if shift amount is too large to convert
                Ok(Self::top(*bits))
            }
        }
    }

    /// Logical shifts right with another interval as the shift amount
    pub fn lshr(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits,
                    stride,
                    lower_bound,
                    upper_bound,
                    ..
                },
                StridedInterval::Normal {
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                // Simple case: constant shift amount
                if o_lb == o_ub {
                    if let Some(shift) = o_lb.to_u32() {
                        if shift >= *bits {
                            return Ok(Self::constant(*bits, 0));
                        }
                        let divisor = BigUint::one() << shift;
                        let new_stride = if stride == &BigUint::zero() {
                            BigUint::zero()
                        } else {
                            max(BigUint::one(), stride / &divisor)
                        };
                        let new_lower = lower_bound >> shift;
                        let new_upper = upper_bound >> shift;
                        return Ok(Self::new(*bits, new_stride, new_lower, new_upper));
                    }
                }
                
                // Improved: compute union of min and max shift results
                if let (Some(min_shift), Some(max_shift)) = (o_lb.to_u32(), o_ub.to_u32()) {
                    let min_shift = min_shift.min(*bits);
                    let max_shift = max_shift.min(*bits);
                    
                    // Compute result for minimum shift
                    let min_result = if min_shift >= *bits {
                        Self::constant(*bits, 0)
                    } else {
                        let new_lower = lower_bound >> min_shift;
                        let new_upper = upper_bound >> min_shift;
                        Self::new(*bits, BigUint::one(), new_lower, new_upper)
                    };
                    
                    // Compute result for maximum shift
                    let max_result = if max_shift >= *bits {
                        Self::constant(*bits, 0)
                    } else {
                        let new_lower = lower_bound >> max_shift;
                        let new_upper = upper_bound >> max_shift;
                        Self::new(*bits, BigUint::one(), new_lower, new_upper)
                    };
                    
                    return Ok(min_result.union(&max_result));
                }
                
                // Fallback to top if shift amount is too large to convert
                Ok(Self::top(*bits))
            }
        }
    }

    /// Arithmetic shifts right with another interval as the shift amount
    pub fn ashr(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits,
                    stride,
                    lower_bound,
                    upper_bound,
                    ..
                },
                StridedInterval::Normal {
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                // Simple case: constant shift amount
                if o_lb == o_ub {
                    if let Some(shift) = o_lb.to_u32() {
                        if shift >= *bits {
                            // Check the sign bit of the lower and upper bounds
                            let sign_bit_mask = BigUint::one() << (*bits - 1);
                            let lower_sign = lower_bound & &sign_bit_mask != BigUint::zero();
                            let upper_sign = upper_bound & &sign_bit_mask != BigUint::zero();

                            if lower_sign && upper_sign {
                                // Both are negative, result is all 1s (-1)
                                return Ok(Self::constant(*bits, Self::max_int(*bits)));
                            } else if !lower_sign && !upper_sign {
                                // Both are positive, result is 0
                                return Ok(Self::constant(*bits, 0));
                            } else {
                                // Mixed signs, result is either 0 or -1
                                return Ok(Self::range(*bits, 0, Self::max_int(*bits)));
                            }
                        }

                        // For arithmetic right shift, we need to preserve the sign bit
                        let sign_bit_mask = BigUint::one() << (*bits - 1);
                        let lower_sign = lower_bound & &sign_bit_mask != BigUint::zero();
                        let upper_sign = upper_bound & &sign_bit_mask != BigUint::zero();

                        // Generate sign extension mask
                        let sign_ext_mask =
                            ((BigUint::one() << shift) - BigUint::one()) << (*bits - shift);

                        // Perform logical right shift
                        let mut new_lower = lower_bound >> shift;
                        let mut new_upper = upper_bound >> shift;

                        // Apply sign extension if needed
                        if lower_sign {
                            new_lower |= &sign_ext_mask;
                        }

                        if upper_sign {
                            new_upper |= &sign_ext_mask;
                        }

                        // Compute new stride
                        let new_stride = if stride == &BigUint::zero() {
                            BigUint::zero()
                        } else {
                            max(BigUint::one(), stride >> shift)
                        };

                        return Ok(Self::new(*bits, new_stride, new_lower, new_upper));
                    }
                }
                
                // Improved: compute union of min and max shift results
                if let (Some(min_shift), Some(max_shift)) = (o_lb.to_u32(), o_ub.to_u32()) {
                    let min_shift = min_shift.min(*bits);
                    let max_shift = max_shift.min(*bits);
                    
                    // Helper to compute ashr for a specific shift amount
                    let compute_ashr = |shift: u32| -> Self {
                        if shift >= *bits {
                            // Check the sign bit of the lower and upper bounds
                            let sign_bit_mask = BigUint::one() << (*bits - 1);
                            let lower_sign = lower_bound & &sign_bit_mask != BigUint::zero();
                            let upper_sign = upper_bound & &sign_bit_mask != BigUint::zero();

                            if lower_sign && upper_sign {
                                // Both are negative, result is all 1s (-1)
                                Self::constant(*bits, Self::max_int(*bits))
                            } else if !lower_sign && !upper_sign {
                                // Both are positive, result is 0
                                Self::constant(*bits, 0)
                            } else {
                                // Mixed signs, result is either 0 or -1
                                Self::range(*bits, 0, Self::max_int(*bits))
                            }
                        } else {
                            // For arithmetic right shift, preserve the sign bit
                            let sign_bit_mask = BigUint::one() << (*bits - 1);
                            let lower_sign = lower_bound & &sign_bit_mask != BigUint::zero();
                            let upper_sign = upper_bound & &sign_bit_mask != BigUint::zero();

                            // Generate sign extension mask
                            let sign_ext_mask =
                                ((BigUint::one() << shift) - BigUint::one()) << (*bits - shift);

                            // Perform logical right shift
                            let mut new_lower = lower_bound >> shift;
                            let mut new_upper = upper_bound >> shift;

                            // Apply sign extension if needed
                            if lower_sign {
                                new_lower |= &sign_ext_mask;
                            }

                            if upper_sign {
                                new_upper |= &sign_ext_mask;
                            }

                            Self::new(*bits, BigUint::one(), new_lower, new_upper)
                        }
                    };
                    
                    let min_result = compute_ashr(min_shift);
                    let max_result = compute_ashr(max_shift);
                    
                    return Ok(min_result.union(&max_result));
                }
                
                // Fallback to top if shift amount is too large to convert
                Ok(Self::top(*bits))
            }
        }
    }

    /// Rotates bits left with another interval as the rotation amount
    pub fn rotate_left(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                // Simple case: both are constants
                if self.is_integer() && other.is_integer() {
                    if let Some(rot) = o_lb.to_u32() {
                        let rot = rot % *bits;
                        if rot == 0 {
                            return Ok(self.clone());
                        }
                        let left_part = s_lb << rot;
                        let right_part = s_lb >> (*bits - rot);
                        let rotated = (left_part | right_part) & Self::max_int(*bits);
                        return Ok(Self::constant(*bits, rotated));
                    }
                }
                
                // Improved: compute union for min and max rotation amounts
                if let (Some(min_rot), Some(max_rot)) = (o_lb.to_u32(), o_ub.to_u32()) {
                    // If rotation range is small enough, compute union
                    let min_rot = min_rot % *bits;
                    let max_rot = max_rot % *bits;
                    
                    // Helper to compute rotate_left for specific amount
                    let compute_rotate = |val: &BigUint, rot: u32| -> BigUint {
                        if rot == 0 {
                            val.clone()
                        } else {
                            let left_part = val << rot;
                            let right_part = val >> (*bits - rot);
                            (left_part | right_part) & Self::max_int(*bits)
                        }
                    };
                    
                    // Compute rotations for corners
                    let min_val_min_rot = compute_rotate(s_lb, min_rot);
                    let min_val_max_rot = compute_rotate(s_lb, max_rot);
                    let max_val_min_rot = compute_rotate(s_ub, min_rot);
                    let max_val_max_rot = compute_rotate(s_ub, max_rot);
                    
                    let lower = min_val_min_rot.clone()
                        .min(min_val_max_rot.clone())
                        .min(max_val_min_rot.clone())
                        .min(max_val_max_rot.clone());
                    let upper = min_val_min_rot
                        .max(min_val_max_rot)
                        .max(max_val_min_rot)
                        .max(max_val_max_rot);
                    
                    return Ok(Self::range(*bits, lower, upper));
                }
                
                // Fallback to top for complex cases
                Ok(Self::top(*bits))
            }
        }
    }

    /// Rotates bits right with another interval as the rotation amount
    pub fn rotate_right(&self, other: &Self) -> Result<Self, ClarirsError> {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                Ok(Self::empty(*bits))
            }
            (
                StridedInterval::Normal {
                    bits,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                // Simple case: both are constants
                if self.is_integer() && other.is_integer() {
                    if let Some(rot) = o_lb.to_u32() {
                        let rot = rot % *bits;
                        if rot == 0 {
                            return Ok(self.clone());
                        }
                        let right_part = s_lb >> rot;
                        let left_part = s_lb << (*bits - rot);
                        let rotated = (left_part | right_part) & Self::max_int(*bits);
                        return Ok(Self::constant(*bits, rotated));
                    }
                }
                
                // Improved: compute union for min and max rotation amounts
                if let (Some(min_rot), Some(max_rot)) = (o_lb.to_u32(), o_ub.to_u32()) {
                    let min_rot = min_rot % *bits;
                    let max_rot = max_rot % *bits;
                    
                    // Helper to compute rotate_right for specific amount
                    let compute_rotate = |val: &BigUint, rot: u32| -> BigUint {
                        if rot == 0 {
                            val.clone()
                        } else {
                            let right_part = val >> rot;
                            let left_part = val << (*bits - rot);
                            (left_part | right_part) & Self::max_int(*bits)
                        }
                    };
                    
                    // Compute rotations for corners
                    let min_val_min_rot = compute_rotate(s_lb, min_rot);
                    let min_val_max_rot = compute_rotate(s_lb, max_rot);
                    let max_val_min_rot = compute_rotate(s_ub, min_rot);
                    let max_val_max_rot = compute_rotate(s_ub, max_rot);
                    
                    let lower = min_val_min_rot.clone()
                        .min(min_val_max_rot.clone())
                        .min(max_val_min_rot.clone())
                        .min(max_val_max_rot.clone());
                    let upper = min_val_min_rot
                        .max(min_val_max_rot)
                        .max(max_val_min_rot)
                        .max(max_val_max_rot);
                    
                    return Ok(Self::range(*bits, lower, upper));
                }
                
                // Fallback to top for complex cases
                Ok(Self::top(*bits))
            }
        }
    }

    /// Zero extend to amount bits
    pub fn zero_ext(&self, amount: u32) -> Self {
        self.zero_extend(self.bits() + amount)
    }

    /// Sign extend to amount bits
    pub fn sign_ext(&self, amount: u32) -> Self {
        self.sign_extend(self.bits() + amount)
    }

    /// Reverse the bits in the interval
    pub fn reverse(&self) -> Self {
        match self {
            StridedInterval::Empty { bits } => Self::empty(*bits),
            StridedInterval::Normal {
                bits,
                lower_bound,
                upper_bound,
                ..
            } if lower_bound == upper_bound => {
                let mut result = BigUint::zero();
                let mut val = lower_bound.clone();

                for i in 0..*bits {
                    if &val & BigUint::one() != BigUint::zero() {
                        result |= BigUint::one() << (*bits - 1 - i);
                    }
                    val >>= 1;
                }

                Self::constant(*bits, result)
            }
            StridedInterval::Normal { bits: 8, .. } => self.clone(),
            StridedInterval::Normal { bits, .. } => Self::top(*bits),
        }
    }

    /// Returns a new StridedInterval with the upper bound clamped (unsigned).
    pub fn clamp_upper_unsigned<T: ToBigUint>(&self, new_upper: T) -> Self {
        match self {
            StridedInterval::Empty { bits } => Self::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                let new_upper = new_upper.to_biguint().unwrap();
                let clamped_upper = std::cmp::min(upper_bound.clone(), new_upper);
                if lower_bound > &clamped_upper {
                    return Self::empty(*bits);
                }
                Self::new(*bits, stride.clone(), lower_bound.clone(), clamped_upper)
            }
        }
    }

    /// Returns a new StridedInterval with the lower bound clamped (unsigned).
    pub fn clamp_lower_unsigned<T: ToBigUint>(&self, new_lower: T) -> Self {
        match self {
            StridedInterval::Empty { bits } => Self::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                let new_lower = new_lower.to_biguint().unwrap();
                let clamped_lower = std::cmp::max(lower_bound.clone(), new_lower);
                if clamped_lower > *upper_bound {
                    return Self::empty(*bits);
                }
                Self::new(*bits, stride.clone(), clamped_lower, upper_bound.clone())
            }
        }
    }

    /// Returns a new StridedInterval with the upper bound clamped (signed).
    pub fn clamp_upper_signed<T: ToBigInt>(&self, new_upper: T) -> Self {
        match self {
            StridedInterval::Empty { bits } => Self::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                ..
            } => {
                let new_upper = new_upper.to_bigint().unwrap();
                let (lb_signed, ub_signed) = self.get_signed_bounds();
                let clamped_ub = std::cmp::min(ub_signed, new_upper);

                // If lower > clamped upper, return bottom
                if lb_signed > clamped_ub {
                    return Self::empty(*bits);
                }

                // Convert clamped_ub back to unsigned
                let max_unsigned = Self::max_int(*bits);
                let clamped_ub_unsigned = if clamped_ub < num_bigint::BigInt::zero() {
                    // Two's complement for negative values
                    let modulus = num_bigint::BigInt::one() << *bits;
                    let val = (modulus.clone() + clamped_ub) % modulus;
                    val.to_biguint().unwrap()
                } else {
                    clamped_ub.to_biguint().unwrap()
                };

                Self::new(
                    *bits,
                    stride.clone(),
                    lower_bound.clone(),
                    clamped_ub_unsigned & max_unsigned,
                )
            }
        }
    }

    /// Returns a new StridedInterval with the lower bound clamped (signed).
    pub fn clamp_lower_signed<T: ToBigInt>(&self, new_lower: T) -> Self {
        match self {
            StridedInterval::Empty { bits } => Self::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                upper_bound,
                ..
            } => {
                let new_lower = new_lower.to_bigint().unwrap();
                let (lb_signed, ub_signed) = self.get_signed_bounds();
                let clamped_lb = std::cmp::max(lb_signed, new_lower);

                // If clamped lower > upper, return bottom
                if clamped_lb > ub_signed {
                    return Self::empty(*bits);
                }

                // Convert clamped_lb back to unsigned
                let max_unsigned = Self::max_int(*bits);
                let clamped_lb_unsigned = if clamped_lb < num_bigint::BigInt::zero() {
                    // Two's complement for negative values
                    let modulus = num_bigint::BigInt::one() << *bits;
                    let val = (modulus.clone() + clamped_lb) % modulus;
                    val.to_biguint().unwrap()
                } else {
                    clamped_lb.to_biguint().unwrap()
                };

                Self::new(
                    *bits,
                    stride.clone(),
                    clamped_lb_unsigned & max_unsigned,
                    upper_bound.clone(),
                )
            }
        }
    }
}

// Implementation of basic operations for StridedInterval

impl Add for &StridedInterval {
    type Output = StridedInterval;

    fn add(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits,
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                },
                StridedInterval::Normal {
                    stride: o_stride,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let new_stride = StridedInterval::gcd(s_stride, o_stride);
                let new_lower = StridedInterval::modular_add(s_lb, o_lb, *bits);
                let new_upper = StridedInterval::modular_add(s_ub, o_ub, *bits);
                StridedInterval::new(*bits, new_stride, new_lower, new_upper)
            }
        }
    }
}

impl Add for StridedInterval {
    type Output = StridedInterval;

    fn add(self, other: StridedInterval) -> StridedInterval {
        &self + &other
    }
}

impl Sub for &StridedInterval {
    type Output = StridedInterval;

    fn sub(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits,
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                },
                StridedInterval::Normal {
                    stride: o_stride,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let new_stride = StridedInterval::gcd(s_stride, o_stride);
                let new_lower = StridedInterval::modular_sub(s_lb, o_ub, *bits);
                let new_upper = StridedInterval::modular_sub(s_ub, o_lb, *bits);
                StridedInterval::new(*bits, new_stride, new_lower, new_upper)
            }
        }
    }
}

impl Sub for StridedInterval {
    type Output = StridedInterval;

    fn sub(self, other: StridedInterval) -> StridedInterval {
        &self - &other
    }
}

impl Mul for &StridedInterval {
    type Output = StridedInterval;

    fn mul(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                },
                StridedInterval::Normal {
                    bits: bits2,
                    stride: o_stride,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                },
            ) => {
                let bits = max(*bits1, *bits2);
                // Conservative: if either operand straddles unsigned or signed poles, return TOP
                let msb_mask = BigUint::one() << (bits - 1);
                let to_signed = |v: &BigUint| -> BigInt {
                    if (v & &msb_mask) != BigUint::zero() {
                        v.to_bigint().unwrap() - (BigInt::one() << bits)
                    } else {
                        v.to_bigint().unwrap()
                    }
                };
                let s_low = to_signed(s_lb);
                let s_high = to_signed(s_ub);
                let s_low_other = to_signed(o_lb);
                let s_high_other = to_signed(o_ub);
                if (s_lb > s_ub && !self.is_top())
                    || (o_lb > o_ub && !other.is_top())
                    || (s_low.sign() != s_high.sign())
                    || (s_low_other.sign() != s_high_other.sign())
                {
                    return StridedInterval::top(bits);
                }
                // Simple case: one operand is a constant
                if s_lb == s_ub {
                    let factor = s_lb.clone();
                    let new_stride = o_stride * &factor;
                    let new_lower = StridedInterval::modular_mul(o_lb, &factor, bits);
                    let new_upper = StridedInterval::modular_mul(o_ub, &factor, bits);
                    return StridedInterval::new(bits, new_stride, new_lower, new_upper);
                }
                if o_lb == o_ub {
                    let factor = o_lb.clone();
                    let new_stride = s_stride * &factor;
                    let new_lower = StridedInterval::modular_mul(s_lb, &factor, bits);
                    let new_upper = StridedInterval::modular_mul(s_ub, &factor, bits);
                    return StridedInterval::new(bits, new_stride, new_lower, new_upper);
                }
                // Both are intervals: compute min/max of all combinations
                let (a, b) = (s_lb, s_ub);
                let (c, d) = (o_lb, o_ub);
                let ac = (a * c) & StridedInterval::max_int(bits);
                let ad = (a * d) & StridedInterval::max_int(bits);
                let bc = (b * c) & StridedInterval::max_int(bits);
                let bd = (b * d) & StridedInterval::max_int(bits);
                let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
                let max_val = ac.max(ad).max(bc).max(bd);
                // Conservative stride
                let stride = BigUint::one();
                StridedInterval::new(bits, stride, min_val, max_val)
            }
        }
    }
}

impl Mul for StridedInterval {
    type Output = StridedInterval;

    fn mul(self, other: StridedInterval) -> StridedInterval {
        &self * &other
    }
}

impl Div for &StridedInterval {
    type Output = StridedInterval;

    fn div(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    stride: s_stride,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                },
                StridedInterval::Normal {
                    bits: bits2,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);
                // Check for division by zero
                let other_contains_zero = if o_lb <= o_ub {
                    // Non-wrapping case
                    *o_lb == BigUint::zero() || *o_ub == BigUint::zero()
                } else {
                    // Wrapping case
                    *o_lb >= BigUint::zero() && *o_ub <= BigUint::zero()
                };
                if other_contains_zero {
                    return StridedInterval::top(bits);
                }
                // Simple case: dividing by a constant
                if o_lb == o_ub {
                    let divisor = o_lb.clone();
                    let new_stride = if s_stride == &BigUint::zero() {
                        BigUint::zero()
                    } else {
                        BigUint::one()
                    };
                    let new_lower = s_lb / &divisor;
                    let new_upper = s_ub / &divisor;
                    return StridedInterval::new(bits, new_stride, new_lower, new_upper);
                }
                // Special case: dividend is constant
                if s_lb == s_ub {
                    let dividend = s_lb.clone();
                    let (c, d) = (o_lb, o_ub);
                    let mut min_val = &dividend / d;
                    let mut max_val = &dividend / c;
                    if min_val > max_val {
                        std::mem::swap(&mut min_val, &mut max_val);
                    }
                    let stride = BigUint::one();
                    return StridedInterval::new(bits, stride, min_val, max_val);
                }
                // Both are intervals: compute min/max of all combinations
                let (a, b) = (s_lb, s_ub);
                let (c, d) = (o_lb, o_ub);
                let ac = if *c != BigUint::zero() {
                    a / c
                } else {
                    BigUint::zero()
                };
                let ad = if *d != BigUint::zero() {
                    a / d
                } else {
                    BigUint::zero()
                };
                let bc = if *c != BigUint::zero() {
                    b / c
                } else {
                    BigUint::zero()
                };
                let bd = if *d != BigUint::zero() {
                    b / d
                } else {
                    BigUint::zero()
                };
                let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
                let max_val = ac.max(ad).max(bc).max(bd);
                let stride = BigUint::one();
                StridedInterval::new(bits, stride, min_val, max_val)
            }
        }
    }
}

impl Div for StridedInterval {
    type Output = StridedInterval;

    fn div(self, other: StridedInterval) -> StridedInterval {
        &self / &other
    }
}

impl BitAnd for &StridedInterval {
    type Output = StridedInterval;

    fn bitand(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    bits: bits2,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);
                
                // Simple case: both are constants
                if s_lb == s_ub && o_lb == o_ub {
                    let result = s_lb & o_lb;
                    return StridedInterval::constant(bits, result);
                }
                
                // Special case: one operand is constant
                if s_lb == s_ub {
                    let mask = s_lb;
                    // x & constant: result is at most the constant value
                    let upper = mask.clone();
                    return StridedInterval::range(bits, 0u32, upper);
                }
                if o_lb == o_ub {
                    let mask = o_lb;
                    let upper = mask.clone();
                    return StridedInterval::range(bits, 0u32, upper);
                }
                
                // General case: compute tighter bounds
                // For AND, result is at most min(max(self), max(other))
                let (_, self_max) = self.get_unsigned_bounds();
                let (_, other_max) = other.get_unsigned_bounds();
                let upper = self_max.min(other_max);
                
                // Lower bound is 0 (can always produce 0)
                StridedInterval::range(bits, 0u32, upper)
            }
        }
    }
}

impl BitAnd for StridedInterval {
    type Output = StridedInterval;

    fn bitand(self, other: StridedInterval) -> StridedInterval {
        &self & &other
    }
}

impl BitOr for &StridedInterval {
    type Output = StridedInterval;

    fn bitor(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    bits: bits2,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);
                
                // Simple case: both are constants
                if s_lb == s_ub && o_lb == o_ub {
                    let result = s_lb | o_lb;
                    return StridedInterval::constant(bits, result);
                }
                
                if self.is_top() || other.is_top() {
                    return StridedInterval::top(bits);
                }
                
                // Compute tighter bounds
                let (self_min, self_max) = self.get_unsigned_bounds();
                let (other_min, other_max) = other.get_unsigned_bounds();
                
                // Lower bound: OR of minimums
                let lower = &self_min | &other_min;
                
                // Upper bound: compute highest possible OR
                // Find the highest bit set in either maximum
                let combined_max = &self_max | &other_max;
                let highest_bit = if combined_max.bits() > 0 {
                    combined_max.bits() as u32
                } else {
                    0
                };
                
                // Upper bound is at most all bits up to highest_bit set to 1
                let upper = if highest_bit >= bits {
                    StridedInterval::max_int(bits)
                } else {
                    let max_possible = (BigUint::one() << highest_bit) - BigUint::one();
                    max_possible.max(combined_max)
                };
                
                StridedInterval::range(bits, lower, upper)
            }
        }
    }
}

impl BitOr for StridedInterval {
    type Output = StridedInterval;

    fn bitor(self, other: StridedInterval) -> StridedInterval {
        &self | &other
    }
}

impl BitXor for &StridedInterval {
    type Output = StridedInterval;

    fn bitxor(self, other: &StridedInterval) -> StridedInterval {
        match (self, other) {
            (StridedInterval::Empty { bits }, _) | (_, StridedInterval::Empty { bits }) => {
                StridedInterval::empty(*bits)
            }
            (
                StridedInterval::Normal {
                    bits: bits1,
                    lower_bound: s_lb,
                    upper_bound: s_ub,
                    ..
                },
                StridedInterval::Normal {
                    bits: bits2,
                    lower_bound: o_lb,
                    upper_bound: o_ub,
                    ..
                },
            ) => {
                let bits = max(*bits1, *bits2);
                
                // Simple case: both are constants
                if s_lb == s_ub && o_lb == o_ub {
                    let result = s_lb ^ o_lb;
                    return StridedInterval::constant(bits, result);
                }
                
                if self.is_top() || other.is_top() {
                    return StridedInterval::top(bits);
                }
                
                // XOR can produce values from 0 to max based on highest bit position
                let (_, self_max) = self.get_unsigned_bounds();
                let (_, other_max) = other.get_unsigned_bounds();
                
                // Find highest bit position in either operand
                let max_val = self_max.max(other_max);
                let highest_bit = if max_val.bits() > 0 {
                    max_val.bits() as u32
                } else {
                    0
                };
                
                // Upper bound: all bits up to highest_bit could be set
                let upper = if highest_bit >= bits {
                    StridedInterval::max_int(bits)
                } else if highest_bit == 0 {
                    BigUint::zero()
                } else {
                    (BigUint::one() << highest_bit) - BigUint::one()
                };
                
                StridedInterval::range(bits, 0u32, upper)
            }
        }
    }
}

impl BitXor for StridedInterval {
    type Output = StridedInterval;

    fn bitxor(self, other: StridedInterval) -> StridedInterval {
        &self ^ &other
    }
}

impl Not for &StridedInterval {
    type Output = StridedInterval;

    fn not(self) -> StridedInterval {
        match self {
            StridedInterval::Empty { bits } => StridedInterval::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                // For NOT, flip all bits
                // If it's a constant, easy to compute
                if lower_bound == upper_bound {
                    // To perform NOT on BigUint, we need to: NOT(x) = MAX_INT - x
                    let result = StridedInterval::max_int(*bits) - lower_bound;
                    return StridedInterval::constant(*bits, result);
                }
                // For intervals, NOT(x) is equivalent to (MAX_INT - x)
                // For stride S[a,b], NOT would be S[NOT(b), NOT(a)]
                let max_value = StridedInterval::max_int(*bits);
                let new_lower = &max_value - upper_bound;
                let new_upper = &max_value - lower_bound;
                // Stride remains the same
                StridedInterval::new(*bits, stride.clone(), new_lower, new_upper)
            }
        }
    }
}

impl Not for StridedInterval {
    type Output = StridedInterval;

    fn not(self) -> StridedInterval {
        !&self
    }
}

impl Neg for &StridedInterval {
    type Output = StridedInterval;

    fn neg(self) -> StridedInterval {
        match self {
            StridedInterval::Empty { bits } => StridedInterval::empty(*bits),
            _ => {
                // Negation in two's complement is: -x = ~x + 1
                let one = StridedInterval::constant(self.bits(), 1);
                let not_interval = !self;
                &not_interval + &one
            }
        }
    }
}

impl Neg for StridedInterval {
    type Output = StridedInterval;

    fn neg(self) -> StridedInterval {
        -&self
    }
}

impl Shl<u32> for &StridedInterval {
    type Output = StridedInterval;

    fn shl(self, shift: u32) -> StridedInterval {
        match self {
            StridedInterval::Empty { bits } => StridedInterval::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                if shift >= *bits {
                    // Shifting by more than or equal to bit width results in 0
                    return StridedInterval::constant(*bits, 0);
                }
                // For left shift, multiply by 2^shift
                let factor = BigUint::one() << shift;
                let new_stride = stride * &factor;
                let new_lower = StridedInterval::modular_mul(lower_bound, &factor, *bits);
                let new_upper = StridedInterval::modular_mul(upper_bound, &factor, *bits);
                StridedInterval::new(*bits, new_stride, new_lower, new_upper)
            }
        }
    }
}

impl Shl<u32> for StridedInterval {
    type Output = StridedInterval;

    fn shl(self, shift: u32) -> StridedInterval {
        &self << shift
    }
}

impl Shr<u32> for &StridedInterval {
    type Output = StridedInterval;

    fn shr(self, shift: u32) -> StridedInterval {
        match self {
            StridedInterval::Empty { bits } => StridedInterval::empty(*bits),
            StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            } => {
                if shift >= *bits {
                    // Shifting by more than or equal to bit width results in 0
                    return StridedInterval::constant(*bits, 0);
                }
                // For right shift, divide by 2^shift (integer division)
                let divisor = BigUint::one() << shift;
                let new_stride = if stride == &BigUint::zero() {
                    BigUint::zero()
                } else {
                    max(BigUint::one(), stride / &divisor)
                };
                let new_lower = lower_bound >> shift;
                let new_upper = upper_bound >> shift;
                StridedInterval::new(*bits, new_stride, new_lower, new_upper)
            }
        }
    }
}

impl Shr<u32> for StridedInterval {
    type Output = StridedInterval;

    fn shr(self, shift: u32) -> StridedInterval {
        &self >> shift
    }
}

// From implementations for common types
impl From<u64> for StridedInterval {
    fn from(value: u64) -> Self {
        Self::constant(64, value)
    }
}

impl From<u32> for StridedInterval {
    fn from(value: u32) -> Self {
        Self::constant(32, value)
    }
}

impl From<u16> for StridedInterval {
    fn from(value: u16) -> Self {
        Self::constant(16, value)
    }
}

impl From<u8> for StridedInterval {
    fn from(value: u8) -> Self {
        Self::constant(8, value)
    }
}

// Try conversion to concrete values when possible
impl TryFrom<&StridedInterval> for u64 {
    type Error = &'static str;

    fn try_from(value: &StridedInterval) -> Result<Self, Self::Error> {
        if !value.is_integer() {
            return Err("StridedInterval is not a single concrete value");
        }

        if value.bits() > 64 {
            return Err("Value too large for u64");
        }

        // Use ToPrimitive trait for conversion
        match value {
            StridedInterval::Normal { lower_bound, .. } => lower_bound
                .to_u64()
                .ok_or("Value cannot be converted to u64"),
            _ => Err("Not a normal strided interval"),
        }
    }
}

// Implementation of PartialOrd for comparison
impl PartialOrd for StridedInterval {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.is_less_than(other) {
            ComparisonResult::True => Some(std::cmp::Ordering::Less),
            ComparisonResult::False => match self.eq_(other) {
                ComparisonResult::True => Some(std::cmp::Ordering::Equal),
                ComparisonResult::False => Some(std::cmp::Ordering::Greater),
                ComparisonResult::Maybe => None,
            },
            ComparisonResult::Maybe => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant() {
        let si = StridedInterval::constant(32, 42u32);
        assert_eq!(
            si,
            StridedInterval::new(
                32,
                BigUint::zero(),
                BigUint::from(42u32),
                BigUint::from(42u32)
            )
        );
        assert!(si.is_integer());
        assert!(!si.is_empty());
        assert!(!si.is_top());
    }

    #[test]
    fn test_top() {
        let si = StridedInterval::top(32);
        assert_eq!(
            si,
            StridedInterval::new(
                32,
                BigUint::one(),
                BigUint::zero(),
                (BigUint::one() << 32) - BigUint::one()
            )
        );
        assert!(!si.is_integer());
        assert!(!si.is_empty());
        assert!(si.is_top());
    }

    #[test]
    fn test_bottom() {
        let si = StridedInterval::empty(32);
        match si {
            StridedInterval::Empty { bits } => assert_eq!(bits, 32),
            _ => panic!("Expected Empty variant"),
        }
        assert!(si.is_empty());
        assert!(!si.is_integer());
        assert!(!si.is_top());
    }

    #[test]
    fn test_range() {
        let si = StridedInterval::range(32, 10u32, 20u32);
        assert_eq!(
            si,
            StridedInterval::new(
                32,
                BigUint::one(),
                BigUint::from(10u32),
                BigUint::from(20u32)
            )
        );
        assert!(!si.is_integer());
        assert!(!si.is_empty());
        assert!(!si.is_top());
    }

    #[test]
    fn test_add() {
        let a = StridedInterval::constant(32, 10u32);
        let b = StridedInterval::constant(32, 20u32);
        let result = &a + &b;
        assert_eq!(result, StridedInterval::constant(32, 30u32));
        assert!(result.is_integer());

        let a = StridedInterval::range(32, 10u32, 20u32);
        let b = StridedInterval::range(32, 5u32, 15u32);
        let result = &a + &b;
        assert_eq!(result, StridedInterval::range(32, 15u32, 35u32));
        assert!(!result.is_integer());
    }

    #[test]
    fn test_sub() {
        let a = StridedInterval::constant(32, 30u32);
        let b = StridedInterval::constant(32, 10u32);
        let result = &a - &b;
        assert_eq!(result, StridedInterval::constant(32, 20u32));
        assert!(result.is_integer());

        let a = StridedInterval::range(32, 20u32, 30u32);
        let b = StridedInterval::range(32, 5u32, 15u32);
        let result = &a - &b;
        assert_eq!(result, StridedInterval::range(32, 5u32, 25u32));
        assert!(!result.is_integer());
    }

    #[test]
    fn test_intersection() {
        let a = StridedInterval::range(32, 10u32, 30u32);
        let b = StridedInterval::range(32, 20u32, 40u32);
        let result = a.intersection(&b);
        assert_eq!(result, StridedInterval::range(32, 20u32, 30u32));
        assert!(!result.is_empty());

        let a = StridedInterval::range(32, 10u32, 20u32);
        let b = StridedInterval::range(32, 30u32, 40u32);
        let result = a.intersection(&b);
        assert!(result.is_empty());
    }

    #[test]
    fn test_union() {
        let a = StridedInterval::range(32, 10u32, 30u32);
        let b = StridedInterval::range(32, 20u32, 40u32);
        let result = a.union(&b);
        assert_eq!(result, StridedInterval::range(32, 10u32, 40u32));

        let a = StridedInterval::range(32, 10u32, 20u32);
        let b = StridedInterval::range(32, 30u32, 40u32);
        let result = a.union(&b);
        assert_eq!(result, StridedInterval::range(32, 10u32, 40u32));
    }

    #[test]
    fn test_eval() {
        let si = StridedInterval::constant(32, 42u32);
        let values = si.eval(10);
        assert_eq!(values.len(), 1);
        assert_eq!(values[0], BigUint::from(42u32));

        let si = StridedInterval::new(
            8,
            BigUint::from(2u32),
            BigUint::from(1u32),
            BigUint::from(5u32),
        );
        let values = si.eval(10);
        assert_eq!(values.len(), 3);
        assert_eq!(values[0], BigUint::from(1u32));
        assert_eq!(values[1], BigUint::from(3u32));
        assert_eq!(values[2], BigUint::from(5u32));
    }

    #[test]
    fn test_contains_zero() {
        let si = StridedInterval::range(32, 0u32, 10u32);
        assert!(si.contains_zero());

        let si = StridedInterval::range(32, 1u32, 10u32);
        assert!(!si.contains_zero());

        let si = StridedInterval::new(
            32,
            BigUint::from(2u32),
            BigUint::from(0u32),
            BigUint::from(10u32),
        );
        assert!(si.contains_zero());
    }

    #[test]
    fn test_strided_range() {
        let si = StridedInterval::strided_range(32, 2u32);
        assert_eq!(
            si,
            StridedInterval::Normal {
                bits: 32,
                stride: BigUint::from(2u32),
                lower_bound: BigUint::zero(),
                upper_bound: (BigUint::one() << 32) - BigUint::one()
            }
        );
    }

    #[test]
    fn test_from_u32() {
        let si: StridedInterval = 42u32.into();
        assert_eq!(
            si,
            StridedInterval::Normal {
                bits: 32,
                stride: BigUint::zero(),
                lower_bound: BigUint::from(42u32),
                upper_bound: BigUint::from(42u32)
            }
        );
        assert!(si.is_integer());
    }

    #[test]
    fn test_try_from_si_to_u64() {
        let si = StridedInterval::constant(32, 42u32);
        let value = u64::try_from(&si).unwrap();
        assert_eq!(value, 42u64);

        let si = StridedInterval::range(32, 10u32, 20u32);
        assert!(u64::try_from(&si).is_err());
    }

    #[test]
    fn test_get_unsigned_bounds() {
        // Normal interval: lower <= upper
        let si = StridedInterval::range(8, 10u32, 20u32);
        let (min_u, max_u) = si.get_unsigned_bounds();
        assert_eq!(min_u, BigUint::from(10u32));
        assert_eq!(max_u, BigUint::from(20u32));

        // Wrap-around interval: lower > upper
        let si = StridedInterval::Normal {
            bits: 8,
            stride: BigUint::one(),
            lower_bound: BigUint::from(250u32),
            upper_bound: BigUint::from(5u32),
        };
        let (min_u, max_u) = si.get_unsigned_bounds();
        assert_eq!(min_u, BigUint::from(250u32));
        assert_eq!(max_u, BigUint::from(255u32)); // max for 8 bits

        // Empty interval
        let si = StridedInterval::empty(8);
        let (min_u, max_u) = si.get_unsigned_bounds();
        assert_eq!(min_u, BigUint::zero());
        assert_eq!(max_u, BigUint::zero());
    }

    #[test]
    fn test_get_signed_bounds() {
        // Positive range
        let si = StridedInterval::range(8, 10u32, 20u32);
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::from(10));
        assert_eq!(max_s, BigInt::from(20));

        // Negative range (e.g., 240-250 in 8 bits is -16 to -6)
        let si = StridedInterval::range(8, 240u32, 250u32);
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::from(-16));
        assert_eq!(max_s, BigInt::from(-6));

        // Wrap-around interval: lower > upper, e.g., 250 to 5
        let si = StridedInterval::Normal {
            bits: 8,
            stride: BigUint::one(),
            lower_bound: BigUint::from(250u32),
            upper_bound: BigUint::from(5u32),
        };
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::from(-6));
        assert_eq!(max_s, BigInt::from(5));

        // Empty interval
        let si = StridedInterval::empty(8);
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::zero());
        assert_eq!(max_s, BigInt::zero());
    }

    #[test]
    fn test_clamp_upper_unsigned() {
        // Clamp upper within bounds
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(15u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(15u32));
        assert_eq!(clamped, StridedInterval::range(8, 10u32, 15u32));

        // Clamp upper to current upper (no-op)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(20u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(20u32));
        assert_eq!(clamped, StridedInterval::range(8, 10u32, 20u32));

        // Clamp upper below lower (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(5u32);
        assert!(clamped.is_empty());

        // Clamp upper on empty interval (should be bottom)
        let si = StridedInterval::empty(8);
        let clamped = si.clamp_upper_unsigned(15u32);
        assert!(clamped.is_empty());

        // Clamp upper on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_upper_unsigned(12u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        assert_eq!(clamped, StridedInterval::constant(8, 12u32));
        let clamped = si.clamp_upper_unsigned(10u32);
        assert!(clamped.is_empty());
    }

    #[test]
    fn test_clamp_lower_unsigned() {
        // Clamp lower within bounds
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(15u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(15u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(20u32));
        assert_eq!(clamped, StridedInterval::range(8, 15u32, 20u32));

        // Clamp lower to current lower (no-op)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(10u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(20u32));
        assert_eq!(clamped, StridedInterval::range(8, 10u32, 20u32));

        // Clamp lower above upper (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(25u32);
        assert!(clamped.is_empty());

        // Clamp lower on empty interval (should be bottom)
        let si = StridedInterval::empty(8);
        let clamped = si.clamp_lower_unsigned(15u32);
        assert!(clamped.is_empty());

        // Clamp lower on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_lower_unsigned(12u32);
        // assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        assert_eq!(clamped, StridedInterval::constant(8, 12u32));
        let clamped = si.clamp_lower_unsigned(15u32);
        assert!(clamped.is_empty());
    }

    #[test]
    fn test_clamp_upper_signed() {
        // Clamp upper within signed range (positive)
        let si = StridedInterval::range(8, 10u32, 120u32);
        let clamped = si.clamp_upper_signed(50i32);
        let (_, ub_signed) = clamped.get_signed_bounds();
        assert!(ub_signed <= BigInt::from(50));

        // Clamp upper to negative value (should handle two's complement)
        let si = StridedInterval::range(8, 200u32, 250u32); // signed: -56 to -6
        let clamped = si.clamp_upper_signed(-10i32);
        let (_, ub_signed) = clamped.get_signed_bounds();
        assert!(ub_signed <= BigInt::from(-10));

        // Clamp upper below lower (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_signed(-100i32);
        assert!(clamped.is_empty());

        // Clamp upper on empty interval (should be bottom)
        let si = StridedInterval::empty(8);
        let clamped = si.clamp_upper_signed(10i32);
        assert!(clamped.is_empty());

        // Clamp upper on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_upper_signed(12i32);
        // assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        assert_eq!(clamped, StridedInterval::constant(8, 12u32));
        let clamped = si.clamp_upper_signed(10i32);
        assert!(clamped.is_empty());
    }

    #[test]
    fn test_clamp_lower_signed() {
        // Clamp lower within signed range (negative)
        let si = StridedInterval::range(8, 120u32, 200u32); // signed: -128 to -56
        let clamped = si.clamp_lower_signed(-100i32);
        let (lb_signed, _) = clamped.get_signed_bounds();
        assert!(lb_signed >= BigInt::from(-100));

        // Clamp lower to positive value (should increase lower bound)
        let si = StridedInterval::range(8, 10u32, 120u32);
        let clamped = si.clamp_lower_signed(50i32);
        let (lb_signed, _) = clamped.get_signed_bounds();
        assert!(lb_signed >= BigInt::from(50));

        // Clamp lower above upper (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_signed(100i32);
        assert!(clamped.is_empty());

        // Clamp lower on empty interval (should be bottom)
        let si = StridedInterval::empty(8);
        let clamped = si.clamp_lower_signed(10i32);
        assert!(clamped.is_empty());

        // Clamp lower on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_lower_signed(12i32);
        // assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        // assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        assert_eq!(clamped, StridedInterval::constant(8, 12u32));
        let clamped = si.clamp_lower_signed(15i32);
        assert!(clamped.is_empty());
    }

    #[test]
    fn test_bitand_with_mask() {
        // Test: x & 0xFF should give [0, 255]
        let x = StridedInterval::range(32, 0u32, 1000u32);
        let mask = StridedInterval::constant(32, 0xFFu32);
        let result = &x & &mask;
        assert_eq!(result, StridedInterval::range(32, 0u32, 0xFFu32));
    }

    #[test]
    fn test_bitand_constants() {
        // Test: constant & constant
        let a = StridedInterval::constant(8, 0xF0u32);
        let b = StridedInterval::constant(8, 0x0Fu32);
        let result = &a & &b;
        assert_eq!(result, StridedInterval::constant(8, 0u32));
    }

    #[test]
    fn test_bitand_tighter_bounds() {
        // Test: [0, 100] & [0, 200] should give [0, 100]
        let a = StridedInterval::range(8, 0u32, 100u32);
        let b = StridedInterval::range(8, 0u32, 200u32);
        let result = &a & &b;
        let (_, upper) = result.get_unsigned_bounds();
        assert!(upper <= BigUint::from(100u32));
    }

    #[test]
    fn test_bitor_bounds() {
        // Test: [0, 15] | [16, 31] should give reasonable bounds
        let a = StridedInterval::range(8, 0u32, 15u32);
        let b = StridedInterval::range(8, 16u32, 31u32);
        let result = &a | &b;
        let (lower, upper) = result.get_unsigned_bounds();
        assert!(lower >= BigUint::from(16u32));
        assert!(upper <= BigUint::from(31u32));
    }

    #[test]
    fn test_bitor_constants() {
        // Test: constant | constant
        let a = StridedInterval::constant(8, 0xF0u32);
        let b = StridedInterval::constant(8, 0x0Fu32);
        let result = &a | &b;
        assert_eq!(result, StridedInterval::constant(8, 0xFFu32));
    }

    #[test]
    fn test_bitxor_constants() {
        // Test: constant ^ constant
        let a = StridedInterval::constant(8, 0xFFu32);
        let b = StridedInterval::constant(8, 0xFFu32);
        let result = &a ^ &b;
        assert_eq!(result, StridedInterval::constant(8, 0u32));
    }

    #[test]
    fn test_bitxor_bounds() {
        // Test: XOR produces reasonable bounds
        let a = StridedInterval::range(8, 0u32, 15u32);
        let b = StridedInterval::range(8, 0u32, 15u32);
        let result = &a ^ &b;
        let (_, upper) = result.get_unsigned_bounds();
        // XOR of [0,15] and [0,15] can produce at most 15 (0b1111)
        assert!(upper <= BigUint::from(15u32));
    }

    #[test]
    fn test_shl_with_range() {
        // Test: [100, 200] << [0, 2] should give union of results
        let val = StridedInterval::range(32, 100u32, 200u32);
        let shift = StridedInterval::range(32, 0u32, 2u32);
        let result = StridedInterval::shl(&val, &shift).unwrap();
        
        // Should contain 100 (shift by 0) and 800 (200 << 2)
        assert!(result.contains_value(&BigUint::from(100u32)));
        assert!(result.contains_value(&BigUint::from(800u32)));
        
        // Should not be top
        assert!(!result.is_top());
    }

    #[test]
    fn test_lshr_with_range() {
        // Test: [100, 200] >> [0, 2] should give union of results
        let val = StridedInterval::range(32, 100u32, 200u32);
        let shift = StridedInterval::range(32, 0u32, 2u32);
        let result = StridedInterval::lshr(&val, &shift).unwrap();
        
        // Should contain 100 (shift by 0) and 50 (200 >> 2)
        assert!(result.contains_value(&BigUint::from(100u32)));
        assert!(result.contains_value(&BigUint::from(50u32)));
        
        // Should not be top
        assert!(!result.is_top());
    }

    #[test]
    fn test_extract_preserves_stride() {
        // Test: extracting from a strided interval
        let si = StridedInterval::new(8, BigUint::from(4u32), BigUint::zero(), BigUint::from(16u32));
        let extracted = si.extract(7, 2);
        
        // Extracting bits [7:2] from values {0,4,8,12,16}
        // After >> 2: {0,1,2,3,4}
        let (lower, upper) = extracted.get_unsigned_bounds();
        assert_eq!(lower, BigUint::zero());
        assert!(upper <= BigUint::from(4u32));
    }

    #[test]
    fn test_concat_with_strides() {
        // Test: concatenating intervals with strides
        let high = StridedInterval::new(4, BigUint::from(2u32), BigUint::from(0u32), BigUint::from(4u32));
        let low = StridedInterval::constant(4, 0xFu32);
        let result = high.concat(&low);
        
        // High bits {0,2,4} concat with low bits {15}
        // Should give {0x0F, 0x2F, 0x4F}
        assert!(result.contains_value(&BigUint::from(0x0Fu32)));
        assert!(result.contains_value(&BigUint::from(0x2Fu32)));
        assert!(result.contains_value(&BigUint::from(0x4Fu32)));
    }

    #[test]
    fn test_rotate_left_with_range() {
        // Test: rotate with a range of rotation amounts
        let val = StridedInterval::constant(8, 0b10000001u32);
        let rot = StridedInterval::range(8, 0u32, 1u32);
        let result = StridedInterval::rotate_left(&val, &rot).unwrap();
        
        // Should contain both original (rot=0) and rotated by 1
        assert!(result.contains_value(&BigUint::from(0b10000001u32)));
        assert!(result.contains_value(&BigUint::from(0b00000011u32)));
    }

    #[test]
    fn test_rotate_right_with_range() {
        // Test: rotate with a range of rotation amounts
        let val = StridedInterval::constant(8, 0b10000001u32);
        let rot = StridedInterval::range(8, 0u32, 1u32);
        let result = StridedInterval::rotate_right(&val, &rot).unwrap();
        
        // Should contain both original (rot=0) and rotated by 1
        assert!(result.contains_value(&BigUint::from(0b10000001u32)));
        assert!(result.contains_value(&BigUint::from(0b11000000u32)));
    }
}
