use num_bigint::{BigInt, BigUint, ToBigInt, ToBigUint};
use num_traits::{One, ToPrimitive, Zero};
use std::cmp::{max, min};
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Shl, Shr, Sub};

use clarirs_core::prelude::*;

/// A StridedInterval represents a set of integers in the form:
/// `<bits> stride[lower_bound, upper_bound]`
///
/// It can represent values within a range that follow a specific stride pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StridedInterval {
    pub bits: u32,
    pub stride: BigUint,
    pub lower_bound: BigUint,
    pub upper_bound: BigUint,
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
        if self.is_empty() {
            return false;
        }
        let (min, max) = self.get_unsigned_bounds();
        if value < &min || value > &max {
            return false;
        }
        if self.stride.is_zero() {
            return &self.lower_bound == value;
        }
        (&(value - &self.lower_bound) % &self.stride).is_zero()
    }

    /// Helper method to check if bit lengths match
    fn check_bit_length(&self, other: &Self) -> Result<(), ClarirsError> {
        if self.bits != other.bits {
            Err(ClarirsError::InvalidArgumentsWithMessage(format!(
                "Bit length mismatch: {} vs {}",
                self.bits, other.bits
            )))
        } else {
            Ok(())
        }
    }

    /// Creates a new StridedInterval with the given parameters
    pub fn new(bits: u32, stride: BigUint, lower_bound: BigUint, upper_bound: BigUint) -> Self {
        let mut si = Self {
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
    pub fn bottom(bits: u32) -> Self {
        Self {
            bits,
            stride: BigUint::one(),
            lower_bound: BigUint::one(),
            upper_bound: BigUint::zero(),
        }
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
        if self.is_empty() {
            return;
        }

        // Ensure bounds are within the bit range
        let max_value = Self::max_int(self.bits);
        self.lower_bound = &self.lower_bound & &max_value;
        self.upper_bound = &self.upper_bound & &max_value;

        // If lower_bound == upper_bound, stride should be 0
        if self.lower_bound == self.upper_bound {
            self.stride = BigUint::zero();
        } else if self.stride.is_zero() {
            // Defensive: zero stride but not singleton is invalid, set stride to 1
            self.stride = BigUint::one();
        }

        // Normalize top value
        if self.stride == BigUint::one()
            && Self::modular_add(&self.upper_bound, &BigUint::one(), self.bits) == self.lower_bound
            && self.lower_bound == BigUint::zero()
            && self.upper_bound == Self::max_int(self.bits)
        {
            self.lower_bound = BigUint::zero();
            self.upper_bound = Self::max_int(self.bits);
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
        if self.lower_bound > self.upper_bound {
            // Special case: bottom interval
            if self.lower_bound == BigUint::one() && self.upper_bound.is_zero() {
                true
            } else {
                // Wrap-around interval: empty only if stride != 1
                self.stride != BigUint::one()
            }
        } else {
            false
        }
    }

    /// Checks if the StridedInterval represents a single concrete value
    pub fn is_integer(&self) -> bool {
        !self.is_empty() && self.lower_bound == self.upper_bound
    }

    /// Checks if the StridedInterval represents the entire range of values
    pub fn is_top(&self) -> bool {
        !self.is_empty()
            && self.stride == BigUint::one()
            && self.lower_bound == BigUint::zero()
            && self.upper_bound == Self::max_int(self.bits)
    }

    /// Returns the cardinality (number of values) in the StridedInterval
    pub fn cardinality(&self) -> BigUint {
        if self.is_empty() {
            return BigUint::zero();
        }
        if self.is_integer() {
            return BigUint::one();
        }
        if self.stride.is_zero() {
            // Defensive: zero stride but not singleton is invalid, treat as empty
            if self.lower_bound == self.upper_bound {
                return BigUint::one();
            } else {
                return BigUint::zero();
            }
        }

        let range = if self.upper_bound >= self.lower_bound {
            &self.upper_bound - &self.lower_bound + BigUint::one()
        } else {
            let max_val = Self::max_int(self.bits);
            &max_val - &self.lower_bound + &self.upper_bound + BigUint::one()
        };

        (range + &self.stride - BigUint::one()) / &self.stride
    }

    /// Finds the intersection of two StridedIntervals
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::bottom(max(self.bits, other.bits));
        }

        if self.bits != other.bits {
            // Create a copy with matching bits
            let extended_other = Self::new(
                self.bits,
                other.stride.clone(),
                other.lower_bound.clone(),
                other.upper_bound.clone(),
            );
            return self.intersection(&extended_other);
        }

        // Check if ranges overlap
        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        // Simple case: one interval is contained within the other
        if self_min >= other_min
            && self_max <= other_max
            && (self.stride.is_zero()
                || other.stride.is_zero()
                || &self.stride % &other.stride == BigUint::zero())
        {
            return self.clone();
        }

        if other_min >= self_min
            && other_max <= self_max
            && (self.stride.is_zero()
                || other.stride.is_zero()
                || &other.stride % &self.stride == BigUint::zero())
        {
            return other.clone();
        }

        // Handle non-overlapping case
        if (self_min > other_max && self_max > other_max)
            || (other_min > self_max && other_max > self_max)
        {
            return Self::bottom(self.bits);
        }

        // Robust handling of zero strides to avoid division by zero
        if self.stride.is_zero() && other.stride.is_zero() {
            if self.lower_bound == other.lower_bound {
                return self.clone();
            } else {
                return Self::bottom(self.bits);
            }
        }
        if self.stride.is_zero() {
            if other.contains(self) {
                return self.clone();
            } else {
                return Self::bottom(self.bits);
            }
        }
        if other.stride.is_zero() {
            if self.contains(other) {
                return other.clone();
            } else {
                return Self::bottom(self.bits);
            }
        }

        let gcd = Self::gcd(&self.stride, &other.stride);
        let new_stride = if gcd.is_zero() {
            BigUint::zero()
        } else {
            (&self.stride * &other.stride) / &gcd
        };

        // Find the smallest value >= lower_bound that satisfies both intervals
        let new_lower = max(self_min, other_min);
        let new_upper = min(self_max, other_max);

        Self::new(self.bits, new_stride, new_lower, new_upper)
    }

    /// Finds the union of two StridedIntervals
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        if self.bits != other.bits {
            // Create a copy with matching bits
            let extended_other = Self::new(
                self.bits,
                other.stride.clone(),
                other.lower_bound.clone(),
                other.upper_bound.clone(),
            );
            return self.union(&extended_other);
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
        let new_stride = if self.stride.is_zero() && other.stride.is_zero() {
            if self.lower_bound == other.lower_bound && self.upper_bound == other.upper_bound {
                BigUint::zero()
            } else if self.lower_bound > other.lower_bound {
                &self.lower_bound - &other.lower_bound
            } else {
                &other.lower_bound - &self.lower_bound
            }
        } else if self.stride.is_zero() {
            other.stride.clone()
        } else if other.stride.is_zero() {
            self.stride.clone()
        } else {
            Self::gcd(&self.stride, &other.stride)
        };

        Self::new(self.bits, new_stride, new_lower, new_upper)
    }

    /// Checks if this StridedInterval contains another
    pub fn contains(&self, other: &Self) -> bool {
        if self.is_empty() {
            return false;
        }
        if other.is_empty() {
            return true;
        }

        if self.bits != other.bits {
            return false;
        }

        let (self_min, self_max) = self.get_unsigned_bounds();
        let (other_min, other_max) = other.get_unsigned_bounds();

        // Check if bounds are contained
        let bounds_contained = self_min <= other_min && self_max >= other_max;

        // Check if stride is compatible
        let stride_compatible = if self.stride.is_zero() {
            // If self stride is 0, it's a singleton value and other must match exactly
            self.lower_bound == other.lower_bound && other.stride.is_zero()
        } else {
            &other.stride % &self.stride == BigUint::zero()
        };

        bounds_contained && stride_compatible
    }

    /// Gets the unsigned bounds as a tuple (min, max)
    pub fn get_unsigned_bounds(&self) -> (BigUint, BigUint) {
        if self.is_empty() {
            // For empty intervals, return something that won't affect calculations
            return (BigUint::zero(), BigUint::zero());
        }

        if self.upper_bound >= self.lower_bound {
            (self.lower_bound.clone(), self.upper_bound.clone())
        } else if self.is_top() {
            // Full range
            (BigUint::zero(), Self::max_int(self.bits))
        } else {
            // Wrap-around case
            (self.lower_bound.clone(), Self::max_int(self.bits))
        }
    }

    /// Gets the signed bounds as a tuple (min, max) considering two's complement
    pub fn get_signed_bounds(&self) -> (BigInt, BigInt) {
        if self.is_empty() {
            // For empty intervals, return something that won't affect calculations
            return (BigInt::zero(), BigInt::zero());
        }

        let msb_mask = BigUint::one() << (self.bits - 1);

        // Convert from unsigned to signed (two's complement)
        let to_signed = |v: &BigUint| -> BigInt {
            if (v & &msb_mask) != BigUint::zero() {
                v.to_bigint().unwrap() - (BigInt::one() << self.bits)
            } else {
                v.to_bigint().unwrap()
            }
        };

        if self.upper_bound >= self.lower_bound {
            let (lb_u, ub_u) = self.get_unsigned_bounds();
            (to_signed(&lb_u), to_signed(&ub_u))
        } else if self.stride == BigUint::one() {
            // For stride 1 wrap-around, treat as mixed signed interval
            let lb_signed = to_signed(&self.lower_bound);
            let ub_signed = to_signed(&self.upper_bound);
            (lb_signed, ub_signed)
        } else {
            // For other wrap-around, conservatively return full signed range
            let min_signed = -(BigInt::one() << (self.bits - 1));
            let max_signed = (BigInt::one() << (self.bits - 1)) - BigInt::one();
            (min_signed, max_signed)
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
        if self.is_empty() {
            return false;
        }

        if self.lower_bound <= self.upper_bound {
            // No wrap-around
            BigUint::zero() >= self.lower_bound && BigUint::zero() <= self.upper_bound
        } else {
            // Wrap-around case
            // 0 is contained if it's >= lower_bound or <= upper_bound
            BigUint::zero() >= self.lower_bound || BigUint::zero() <= self.upper_bound
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

        if self_max < other_min || self.upper_bound < other.lower_bound {
            ComparisonResult::True
        } else if self.lower_bound > other.upper_bound {
            ComparisonResult::False
        } else {
            ComparisonResult::Maybe
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

        if self.is_integer() && other.is_integer() && self.lower_bound == other.lower_bound {
            return ComparisonResult::True;
        }

        // If intervals don't overlap, they can't be equal
        let intersection = self.intersection(other);
        if intersection.is_empty() {
            return ComparisonResult::False;
        }

        // If both intervals are the same singleton, they're definitely equal
        if self.is_integer() && other.is_integer() && self.lower_bound == other.lower_bound {
            return ComparisonResult::True;
        }

        // If intervals don't overlap, they can't be equal
        let intersection = self.intersection(other);
        if intersection.is_empty() {
            return ComparisonResult::False;
        }

        // If both intervals are the same singleton, they're definitely equal
        if self.is_integer() && other.is_integer() && self.lower_bound == other.lower_bound {
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
        println!("slt: self: {:?}, other: {:?}", self, other);
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

        if self.is_integer() || self.stride.is_zero() {
            return vec![self.lower_bound.clone()];
        }

        let mut results = Vec::new();

        if self.lower_bound <= self.upper_bound {
            // No wrap-around
            let mut value = self.lower_bound.clone();
            while value <= self.upper_bound && results.len() < limit as usize {
                results.push(value.clone());
                value += &self.stride;
            }
        } else {
            // Wrap-around case
            let max_value = Self::max_int(self.bits);

            // First part: from lower_bound to max_value
            let mut value = self.lower_bound.clone();
            while value <= max_value && results.len() < limit as usize {
                results.push(value.clone());
                value += &self.stride;
            }

            // Second part: from 0 to upper_bound
            if results.len() < limit as usize {
                let mut remainder =
                    (&max_value + BigUint::one() - &self.lower_bound) % &self.stride;
                if remainder == BigUint::zero() {
                    remainder = self.stride.clone();
                }

                let mut value = remainder.clone();
                while value <= self.upper_bound && results.len() < limit as usize {
                    results.push(value.clone());
                    value += &self.stride;
                }
            }
        }

        results
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
            return Self::top(self.bits);
        }

        if self.is_top() {
            return Self::bottom(self.bits);
        }

        // Handle the case of a singleton value
        if self.is_integer() {
            let lower = Self::modular_add(&self.upper_bound, &BigUint::one(), self.bits);
            let upper = Self::modular_sub(&self.lower_bound, &BigUint::one(), self.bits);
            return Self::new(self.bits, BigUint::one(), lower, upper);
        }

        // For the general case
        // If the stride is greater than 1, we need to handle all values between the intervals
        if self.stride > BigUint::one() {
            // Complex case: we need to calculate the values between the intervals
            // For simplicity, we'll return a conservative approximation
            // A more precise implementation could return a set of intervals
            let lower = Self::modular_add(&self.upper_bound, &BigUint::one(), self.bits);
            let upper = Self::modular_sub(&self.lower_bound, &BigUint::one(), self.bits);
            return Self::new(self.bits, BigUint::one(), lower, upper);
        }

        // For stride 1, simply invert the range
        let lower = Self::modular_add(&self.upper_bound, &BigUint::one(), self.bits);
        let upper = Self::modular_sub(&self.lower_bound, &BigUint::one(), self.bits);
        Self::new(self.bits, BigUint::one(), lower, upper)
    }

    /// Test if this interval has an empty intersection with another
    pub fn is_disjoint_from(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }

    /// Create a widened interval by extending bounds
    pub fn widen(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }

        if other.is_empty() {
            return self.clone();
        }

        // If the intervals have different bit widths, normalize
        if self.bits != other.bits {
            return self.widen(&Self::new(
                self.bits,
                other.stride.clone(),
                other.lower_bound.clone(),
                other.upper_bound.clone(),
            ));
        }

        // Calculate new bounds
        let new_lower = if other.lower_bound < self.lower_bound {
            other.lower_bound.clone()
        } else {
            self.lower_bound.clone()
        };

        let new_upper = if other.upper_bound > self.upper_bound {
            other.upper_bound.clone()
        } else {
            self.upper_bound.clone()
        };

        // Calculate new stride - take the GCD
        let new_stride = Self::gcd(&self.stride, &other.stride);

        Self::new(self.bits, new_stride, new_lower, new_upper)
    }

    /// Extract bits from the interval (similar to bitslice)
    pub fn extract(&self, high_bit: u32, low_bit: u32) -> Self {
        if self.is_empty() {
            return Self::bottom(high_bit - low_bit + 1);
        }

        if low_bit >= self.bits || high_bit >= self.bits || high_bit < low_bit {
            return Self::bottom(high_bit - low_bit + 1);
        }

        // First shift right by low_bit
        let shifted = if low_bit > 0 {
            self >> low_bit
        } else {
            self.clone()
        };

        // Then mask to only keep the bits we want
        let mask = (BigUint::one() << (high_bit - low_bit + 1)) - BigUint::one();
        let new_lower = &shifted.lower_bound & &mask;
        let new_upper = &shifted.upper_bound & &mask;

        // Compute new stride
        let new_stride = if shifted.stride == BigUint::zero() {
            BigUint::zero()
        } else {
            // For more complex stride patterns, this is a conservative approximation
            BigUint::one()
        };

        Self::new(high_bit - low_bit + 1, new_stride, new_lower, new_upper)
    }

    /// Concatenate two intervals (high bits from self, low bits from other)
    pub fn concat(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::bottom(self.bits + other.bits);
        }

        // Combine with OR - this is a conservative approximation
        // A more precise implementation would consider all possible combinations

        // Simple case: if both are constants
        if self.is_integer() && other.is_integer() {
            let new_value = (&self.lower_bound << other.bits) | &other.lower_bound;
            return Self::constant(self.bits + other.bits, new_value);
        }

        // General case - compute all corner combinations
        let a = &self.lower_bound << other.bits;
        let b = &self.upper_bound << other.bits;
        let c = &other.lower_bound;
        let d = &other.upper_bound;

        let ac = &a | c;
        let ad = &a | d;
        let bc = &b | c;
        let bd = &b | d;

        let new_lower = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
        let new_upper = ac.max(ad).max(bc).max(bd);

        Self::new(
            self.bits + other.bits,
            BigUint::one(), // Conservative stride
            new_lower,
            new_upper,
        )
    }

    /// Zero-extend the interval to a new bit width
    pub fn zero_extend(&self, new_bits: u32) -> Self {
        if self.is_empty() {
            return Self::bottom(new_bits);
        }

        if new_bits <= self.bits {
            return self.clone();
        }

        Self::new(
            new_bits,
            self.stride.clone(),
            self.lower_bound.clone(),
            self.upper_bound.clone(),
        )
    }

    /// Sign-extend the interval to a new bit width
    pub fn sign_extend(&self, new_bits: u32) -> Self {
        if self.is_empty() {
            return Self::bottom(new_bits);
        }

        if new_bits <= self.bits {
            return self.clone();
        }

        // Check if the sign bit is set for lower and upper bounds
        let sign_bit_mask = BigUint::one() << (self.bits - 1);
        let extension_bits = new_bits - self.bits;
        let extension_mask = (BigUint::one() << extension_bits) - BigUint::one();

        let new_lower = if &self.lower_bound & &sign_bit_mask != BigUint::zero() {
            &self.lower_bound | (&extension_mask << self.bits)
        } else {
            self.lower_bound.clone()
        };

        let new_upper = if &self.upper_bound & &sign_bit_mask != BigUint::zero() {
            &self.upper_bound | (&extension_mask << self.bits)
        } else {
            self.upper_bound.clone()
        };

        Self::new(new_bits, self.stride.clone(), new_lower, new_upper)
    }

    /// Performs unsigned division
    pub fn udiv(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(max(self.bits, other.bits)));
        }

        // Avoid division by zero
        if other.contains_zero() || (other.stride.is_zero() && other.lower_bound.is_zero()) {
            return Ok(Self::top(max(self.bits, other.bits)));
        }

        let bits = max(self.bits, other.bits);

        // Simple case: dividing by a constant
        if other.is_integer() {
            let divisor = other.lower_bound.clone();
            // New stride is a conservative approximation
            let new_stride = if self.stride == BigUint::zero() {
                BigUint::zero()
            } else {
                BigUint::one()
            };

            // Calculate new bounds
            let new_lower = &self.lower_bound / &divisor;
            let new_upper = &self.upper_bound / &divisor;

            return Ok(Self::new(bits, new_stride, new_lower, new_upper));
        }

        // Special case: numerator is constant, denominator is interval
        if self.is_integer() {
            let dividend = self.lower_bound.clone();
            let (c, d) = other.get_unsigned_bounds();

            let mut min_val = &dividend / &d;
            let mut max_val = &dividend / &c;

            if min_val > max_val {
                std::mem::swap(&mut min_val, &mut max_val);
            }

            return Ok(Self::new(bits, BigUint::one(), min_val, max_val));
        }

        // General case: both numerator and denominator are intervals
        let (a, b) = self.get_unsigned_bounds();
        let (c, d) = other.get_unsigned_bounds();

        let ac = if c != BigUint::zero() {
            &a / &c
        } else {
            BigUint::zero()
        };
        let ad = if d != BigUint::zero() {
            &a / &d
        } else {
            BigUint::zero()
        };
        let bc = if c != BigUint::zero() {
            &b / &c
        } else {
            BigUint::zero()
        };
        let bd = if d != BigUint::zero() {
            &b / &d
        } else {
            BigUint::zero()
        };

        let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
        let max_val = ac.max(ad).max(bc).max(bd);

        Ok(Self::new(bits, BigUint::one(), min_val, max_val))
    }

    /// Performs signed division
    pub fn sdiv(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(max(self.bits, other.bits)));
        }

        // Avoid division by zero
        if other.contains_zero() || other.stride.is_zero() && other.lower_bound.is_zero() {
            return Ok(Self::top(max(self.bits, other.bits)));
        }

        let bits = max(self.bits, other.bits);

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
        // Signed division requires more careful analysis for precise results
        Ok(Self::top(bits))
    }

    /// Performs unsigned remainder
    pub fn urem(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(max(self.bits, other.bits)));
        }

        // // Check for division by zero
        // if other.contains_zero() {
        //     return Err(ClarirsError::DivideByZero);
        // }

        let bits = max(self.bits, other.bits);

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            let result = &self.lower_bound % &other.lower_bound;
            return Ok(Self::constant(bits, result));
        }

        // For the general case, provide a bound based on divisor
        // The remainder is always less than the divisor
        if other.is_integer() {
            let max_remainder = &other.lower_bound - BigUint::one();
            return Ok(Self::range(bits, 0, max_remainder));
        }

        // If divisor is a range, the remainder can be from 0 to max(divisor)-1
        let (_, other_max) = other.get_unsigned_bounds();
        Ok(Self::range(bits, 0, &other_max - BigUint::one()))
    }

    /// Performs signed remainder
    pub fn srem(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(max(self.bits, other.bits)));
        }

        // // Check for division by zero
        // if other.contains_zero() {
        //     return Err(ClarirsError::DivideByZero);
        // }

        let bits = max(self.bits, other.bits);

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
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(self.bits));
        }

        // Simple case: constant shift amount
        if other.is_integer() {
            // Try to convert to u32
            if let Some(shift) = other.lower_bound.to_u32() {
                // If shift is larger than bit width, result is 0
                if shift >= self.bits {
                    return Ok(Self::constant(self.bits, 0));
                }

                // Normal shift operation
                let factor = BigUint::one() << shift;
                let new_stride = &self.stride * &factor;
                let new_lower = Self::modular_mul(&self.lower_bound, &factor, self.bits);
                let new_upper = Self::modular_mul(&self.upper_bound, &factor, self.bits);

                return Ok(Self::new(self.bits, new_stride, new_lower, new_upper));
            }
        }

        // If shift amount is a range, we need to consider all possible shifts
        // This is a conservative approximation
        Ok(Self::top(self.bits))
    }

    /// Logical shifts right with another interval as the shift amount
    pub fn lshr(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(self.bits));
        }

        // Simple case: constant shift amount
        if other.is_integer() {
            // Try to convert to u32
            if let Some(shift) = other.lower_bound.to_u32() {
                // If shift is larger than bit width, result is 0
                if shift >= self.bits {
                    return Ok(Self::constant(self.bits, 0));
                }

                // For logical right shift, divide by 2^shift (integer division)
                let divisor = BigUint::one() << shift;
                let new_stride = if self.stride == BigUint::zero() {
                    BigUint::zero()
                } else {
                    max(BigUint::one(), &self.stride / &divisor)
                };

                let new_lower = &self.lower_bound >> shift;
                let new_upper = &self.upper_bound >> shift;

                return Ok(Self::new(self.bits, new_stride, new_lower, new_upper));
            }
        }

        // If shift amount is a range, we need to consider all possible shifts
        // This is a conservative approximation
        Ok(Self::top(self.bits))
    }

    /// Arithmetic shifts right with another interval as the shift amount
    pub fn ashr(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(self.bits));
        }

        // Simple case: constant shift amount
        if other.is_integer() {
            // Try to convert to u32
            if let Some(shift) = other.lower_bound.to_u32() {
                // If shift is larger than bit width, result is either 0 (for positive) or -1 (for negative)
                if shift >= self.bits {
                    // Check the sign bit of the lower and upper bounds
                    let sign_bit_mask = BigUint::one() << (self.bits - 1);
                    let lower_sign = &self.lower_bound & &sign_bit_mask != BigUint::zero();
                    let upper_sign = &self.upper_bound & &sign_bit_mask != BigUint::zero();

                    if lower_sign && upper_sign {
                        // Both are negative, result is all 1s (-1)
                        return Ok(Self::constant(self.bits, Self::max_int(self.bits)));
                    } else if !lower_sign && !upper_sign {
                        // Both are positive, result is 0
                        return Ok(Self::constant(self.bits, 0));
                    } else {
                        // Mixed signs, result is either 0 or -1
                        return Ok(Self::range(self.bits, 0, Self::max_int(self.bits)));
                    }
                }

                // For arithmetic right shift, we need to preserve the sign bit
                let sign_bit_mask = BigUint::one() << (self.bits - 1);
                let lower_sign = &self.lower_bound & &sign_bit_mask != BigUint::zero();
                let upper_sign = &self.upper_bound & &sign_bit_mask != BigUint::zero();

                // Generate sign extension mask
                let sign_ext_mask =
                    ((BigUint::one() << shift) - BigUint::one()) << (self.bits - shift);

                // Perform logical right shift
                let mut new_lower = &self.lower_bound >> shift;
                let mut new_upper = &self.upper_bound >> shift;

                // Apply sign extension if needed
                if lower_sign {
                    new_lower |= &sign_ext_mask;
                }

                if upper_sign {
                    new_upper |= &sign_ext_mask;
                }

                // Compute new stride
                let new_stride = if self.stride == BigUint::zero() {
                    BigUint::zero()
                } else {
                    max(BigUint::one(), &self.stride >> shift)
                };

                return Ok(Self::new(self.bits, new_stride, new_lower, new_upper));
            }
        }

        // If shift amount is a range, we need to consider all possible shifts
        // This is a conservative approximation
        Ok(Self::top(self.bits))
    }

    /// Rotates bits left with another interval as the rotation amount
    pub fn rotate_left(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(self.bits));
        }

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            // Try to convert to u32
            if let Some(rot) = other.lower_bound.to_u32() {
                // Normalize rotation amount to be within bit width
                let rot = rot % self.bits;

                if rot == 0 {
                    return Ok(self.clone());
                }

                // Compute rotation
                let left_part = &self.lower_bound << rot;
                let right_part = &self.lower_bound >> (self.bits - rot);
                let rotated = (left_part | right_part) & Self::max_int(self.bits);

                return Ok(Self::constant(self.bits, rotated));
            }
        }

        // For the general case, this is a complex operation
        // Return a conservative approximation
        Ok(Self::top(self.bits))
    }

    /// Rotates bits right with another interval as the rotation amount
    pub fn rotate_right(&self, other: &Self) -> Result<Self, ClarirsError> {
        if self.is_empty() || other.is_empty() {
            return Ok(Self::bottom(self.bits));
        }

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            // Try to convert to u32
            if let Some(rot) = other.lower_bound.to_u32() {
                // Normalize rotation amount to be within bit width
                let rot = rot % self.bits;

                if rot == 0 {
                    return Ok(self.clone());
                }

                // Compute rotation
                let right_part = &self.lower_bound >> rot;
                let left_part = &self.lower_bound << (self.bits - rot);
                let rotated = (left_part | right_part) & Self::max_int(self.bits);

                return Ok(Self::constant(self.bits, rotated));
            }
        }

        // For the general case, this is a complex operation
        // Return a conservative approximation
        Ok(Self::top(self.bits))
    }

    /// Zero extend to amount bits
    pub fn zero_ext(&self, amount: u32) -> Self {
        self.zero_extend(self.bits + amount)
    }

    /// Sign extend to amount bits
    pub fn sign_ext(&self, amount: u32) -> Self {
        self.sign_extend(self.bits + amount)
    }

    /// Reverse the bits in the interval
    pub fn reverse(&self) -> Self {
        if self.is_empty() {
            return Self::bottom(self.bits);
        }

        // Simple case: single concrete value
        if self.is_integer() {
            let mut result = BigUint::zero();
            let mut val = self.lower_bound.clone();

            // Reverse the bits
            for i in 0..self.bits {
                if &val & BigUint::one() != BigUint::zero() {
                    result |= BigUint::one() << (self.bits - 1 - i);
                }
                val >>= 1;
            }

            return Self::constant(self.bits, result);
        }

        // For intervals, bit reversal is a complex transformation
        // Provide a conservative approximation
        Self::top(self.bits)
    }

    /// Returns a new StridedInterval with the upper bound clamped (unsigned).
    pub fn clamp_upper_unsigned<T: ToBigUint>(&self, new_upper: T) -> Self {
        if self.is_empty() {
            return Self::bottom(self.bits);
        }
        let new_upper = new_upper.to_biguint().unwrap();
        let clamped_upper = std::cmp::min(self.upper_bound.clone(), new_upper);
        if self.lower_bound > clamped_upper {
            return Self::bottom(self.bits);
        }
        Self::new(
            self.bits,
            self.stride.clone(),
            self.lower_bound.clone(),
            clamped_upper,
        )
    }

    /// Returns a new StridedInterval with the lower bound clamped (unsigned).
    pub fn clamp_lower_unsigned<T: ToBigUint>(&self, new_lower: T) -> Self {
        if self.is_empty() {
            return Self::bottom(self.bits);
        }
        let new_lower = new_lower.to_biguint().unwrap();
        let clamped_lower = std::cmp::max(self.lower_bound.clone(), new_lower);
        if clamped_lower > self.upper_bound {
            return Self::bottom(self.bits);
        }
        Self::new(
            self.bits,
            self.stride.clone(),
            clamped_lower,
            self.upper_bound.clone(),
        )
    }

    /// Returns a new StridedInterval with the upper bound clamped (signed).
    pub fn clamp_upper_signed<T: ToBigInt>(&self, new_upper: T) -> Self {
        if self.is_empty() {
            return Self::bottom(self.bits);
        }
        let new_upper = new_upper.to_bigint().unwrap();
        let (lb_signed, ub_signed) = self.get_signed_bounds();
        let clamped_ub = std::cmp::min(ub_signed, new_upper);

        // If lower > clamped upper, return bottom
        if lb_signed > clamped_ub {
            return Self::bottom(self.bits);
        }

        // Convert clamped_ub back to unsigned
        let bits = self.bits;
        let max_unsigned = Self::max_int(bits);
        let clamped_ub_unsigned = if clamped_ub < num_bigint::BigInt::zero() {
            // Two's complement for negative values
            let modulus = num_bigint::BigInt::one() << bits;
            let val = (modulus.clone() + clamped_ub) % modulus;
            val.to_biguint().unwrap()
        } else {
            clamped_ub.to_biguint().unwrap()
        };

        Self::new(
            bits,
            self.stride.clone(),
            self.lower_bound.clone(),
            clamped_ub_unsigned & max_unsigned,
        )
    }

    /// Returns a new StridedInterval with the lower bound clamped (signed).
    pub fn clamp_lower_signed<T: ToBigInt>(&self, new_lower: T) -> Self {
        if self.is_empty() {
            return Self::bottom(self.bits);
        }
        let new_lower = new_lower.to_bigint().unwrap();
        let (lb_signed, ub_signed) = self.get_signed_bounds();
        let clamped_lb = std::cmp::max(lb_signed, new_lower);

        // If clamped lower > upper, return bottom
        if clamped_lb > ub_signed {
            return Self::bottom(self.bits);
        }

        // Convert clamped_lb back to unsigned
        let bits = self.bits;
        let max_unsigned = Self::max_int(bits);
        let clamped_lb_unsigned = if clamped_lb < num_bigint::BigInt::zero() {
            // Two's complement for negative values
            let modulus = num_bigint::BigInt::one() << bits;
            let val = (modulus.clone() + clamped_lb) % modulus;
            val.to_biguint().unwrap()
        } else {
            clamped_lb.to_biguint().unwrap()
        };

        Self::new(
            bits,
            self.stride.clone(),
            clamped_lb_unsigned & max_unsigned,
            self.upper_bound.clone(),
        )
    }
}

impl fmt::Display for StridedInterval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            write!(f, "<{}>[EmptySI]", self.bits)
        } else {
            write!(
                f,
                "<{}>0x{}[0x{}, 0x{}]",
                self.bits,
                self.stride.to_str_radix(16),
                self.lower_bound.to_str_radix(16),
                self.upper_bound.to_str_radix(16)
            )
        }
    }
}

// Implementation of basic operations for StridedInterval

impl Add for &StridedInterval {
    type Output = StridedInterval;

    fn add(self, other: &StridedInterval) -> StridedInterval {
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(self.bits);
        }

        // Check bit lengths match
        if self.check_bit_length(other).is_err() {
            return StridedInterval::bottom(self.bits);
        }

        let new_stride = StridedInterval::gcd(&self.stride, &other.stride);

        // Calculate new bounds considering wraparound
        let new_lower =
            StridedInterval::modular_add(&self.lower_bound, &other.lower_bound, self.bits);
        let new_upper =
            StridedInterval::modular_add(&self.upper_bound, &other.upper_bound, self.bits);

        StridedInterval::new(self.bits, new_stride, new_lower, new_upper)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);
        let new_stride = StridedInterval::gcd(&self.stride, &other.stride);

        // Calculate new bounds considering wraparound
        let new_lower = StridedInterval::modular_sub(&self.lower_bound, &other.upper_bound, bits);
        let new_upper = StridedInterval::modular_sub(&self.upper_bound, &other.lower_bound, bits);

        StridedInterval::new(bits, new_stride, new_lower, new_upper)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);

        // Conservative: if either operand straddles unsigned or signed poles, return TOP
        let msb_mask = BigUint::one() << (bits - 1);
        let to_signed = |v: &BigUint| -> BigInt {
            if (v & &msb_mask) != BigUint::zero() {
                v.to_bigint().unwrap() - (BigInt::one() << bits)
            } else {
                v.to_bigint().unwrap()
            }
        };

        let s_low = to_signed(&self.lower_bound);
        let s_high = to_signed(&self.upper_bound);
        let s_low_other = to_signed(&other.lower_bound);
        let s_high_other = to_signed(&other.upper_bound);

        if (self.lower_bound > self.upper_bound && !self.is_top())
            || (other.lower_bound > other.upper_bound && !other.is_top())
            || (s_low.sign() != s_high.sign())
            || (s_low_other.sign() != s_high_other.sign())
        {
            return StridedInterval::top(bits);
        }

        // Simple case: one operand is a constant
        if self.is_integer() {
            let factor = self.lower_bound.clone();
            let new_stride = &other.stride * &factor;
            let new_lower = StridedInterval::modular_mul(&other.lower_bound, &factor, bits);
            let new_upper = StridedInterval::modular_mul(&other.upper_bound, &factor, bits);
            return StridedInterval::new(bits, new_stride, new_lower, new_upper);
        }

        if other.is_integer() {
            let factor = other.lower_bound.clone();
            let new_stride = &self.stride * &factor;
            let new_lower = StridedInterval::modular_mul(&self.lower_bound, &factor, bits);
            let new_upper = StridedInterval::modular_mul(&self.upper_bound, &factor, bits);
            return StridedInterval::new(bits, new_stride, new_lower, new_upper);
        }

        // Both are intervals: compute min/max of all combinations
        let (a, b) = self.get_unsigned_bounds();
        let (c, d) = other.get_unsigned_bounds();

        let ac = (&a * &c) & StridedInterval::max_int(bits);
        let ad = (&a * &d) & StridedInterval::max_int(bits);
        let bc = (&b * &c) & StridedInterval::max_int(bits);
        let bd = (&b * &d) & StridedInterval::max_int(bits);

        let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
        let max_val = ac.max(ad).max(bc).max(bd);

        // Conservative stride
        let stride = BigUint::one();

        StridedInterval::new(bits, stride, min_val, max_val)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        // Check for division by zero
        if other.contains_zero() {
            return StridedInterval::top(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);

        // Simple case: dividing by a constant
        if other.is_integer() {
            let divisor = other.lower_bound.clone();
            let new_stride = if self.stride == BigUint::zero() {
                BigUint::zero()
            } else {
                BigUint::one()
            };

            let new_lower = &self.lower_bound / &divisor;
            let new_upper = &self.upper_bound / &divisor;

            return StridedInterval::new(bits, new_stride, new_lower, new_upper);
        }

        // Special case: dividend is constant
        if self.is_integer() {
            let dividend = self.lower_bound.clone();

            // If divisor interval includes zero, return top
            if other.contains_zero() {
                return StridedInterval::top(bits);
            }

            let (c, d) = other.get_unsigned_bounds();

            let mut min_val = &dividend / &d;
            let mut max_val = &dividend / &c;

            if min_val > max_val {
                std::mem::swap(&mut min_val, &mut max_val);
            }

            let stride = BigUint::one();

            return StridedInterval::new(bits, stride, min_val, max_val);
        }

        // Both are intervals: compute min/max of all combinations
        let (a, b) = self.get_unsigned_bounds();
        let (c, d) = other.get_unsigned_bounds();

        let ac = if c != BigUint::zero() {
            &a / &c
        } else {
            BigUint::zero()
        };
        let ad = if d != BigUint::zero() {
            &a / &d
        } else {
            BigUint::zero()
        };
        let bc = if c != BigUint::zero() {
            &b / &c
        } else {
            BigUint::zero()
        };
        let bd = if d != BigUint::zero() {
            &b / &d
        } else {
            BigUint::zero()
        };

        let min_val = ac.clone().min(ad.clone()).min(bc.clone()).min(bd.clone());
        let max_val = ac.max(ad).max(bc).max(bd);

        let stride = BigUint::one();

        StridedInterval::new(bits, stride, min_val, max_val)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);

        // Simple case: one is constant
        if self.is_integer() && other.is_integer() {
            let result = &self.lower_bound & &other.lower_bound;
            return StridedInterval::constant(bits, result);
        }

        // For bitwise AND, a conservative but sound approximation
        // is to find the bits that must be 0 in the result

        // If any operand has a fixed 0 bit, the result will have a 0 at that position
        let lower_bound = BigUint::zero();
        let upper_bound = StridedInterval::max_int(bits);

        // Conservative approximation
        // A more precise implementation would analyze bit patterns in detail

        // If either interval is small enough, we could enumerate all values
        // and compute the exact result, but for larger intervals we use
        // a more conservative approach
        if self.cardinality() <= BigUint::from(64u32) && other.cardinality() <= BigUint::from(64u32)
        {
            // We could enumerate all combinations for small intervals
            // But we'll stick with a simpler approach for now
        }

        // For now, return a safe approximation
        if self.is_top() || other.is_top() {
            return StridedInterval::top(bits);
        }

        // Otherwise, make a conservative estimate
        StridedInterval::new(bits, BigUint::one(), lower_bound, upper_bound)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            let result = &self.lower_bound | &other.lower_bound;
            return StridedInterval::constant(bits, result);
        }

        // Conservative approximation for OR
        // Similar logic to AND but looking at fixed 1 bits

        // For now, return a safe approximation
        if self.is_top() || other.is_top() {
            return StridedInterval::top(bits);
        }

        // Otherwise, make a conservative estimate
        let lower_bound = BigUint::zero();
        let upper_bound = StridedInterval::max_int(bits);

        StridedInterval::new(bits, BigUint::one(), lower_bound, upper_bound)
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
        if self.is_empty() || other.is_empty() {
            return StridedInterval::bottom(max(self.bits, other.bits));
        }

        let bits = max(self.bits, other.bits);

        // Simple case: both are constants
        if self.is_integer() && other.is_integer() {
            let result = &self.lower_bound ^ &other.lower_bound;
            return StridedInterval::constant(bits, result);
        }

        // For XOR, a precise analysis is complex
        // Return a conservative approximation

        // If either is TOP, result could be anything
        if self.is_top() || other.is_top() {
            return StridedInterval::top(bits);
        }

        // Otherwise, return a conservative estimate
        let lower_bound = BigUint::zero();
        let upper_bound = StridedInterval::max_int(bits);

        StridedInterval::new(bits, BigUint::one(), lower_bound, upper_bound)
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
        if self.is_empty() {
            return StridedInterval::bottom(self.bits);
        }

        // For NOT, flip all bits
        // If it's a constant, easy to compute
        if self.is_integer() {
            // To perform NOT on BigUint, we need to: NOT(x) = MAX_INT - x
            let result = StridedInterval::max_int(self.bits) - &self.lower_bound;
            return StridedInterval::constant(self.bits, result);
        }

        // For intervals, NOT(x) is equivalent to (MAX_INT - x)
        // For stride S[a,b], NOT would be S[NOT(b), NOT(a)]
        let max_value = StridedInterval::max_int(self.bits);
        let new_lower = &max_value - &self.upper_bound;
        let new_upper = &max_value - &self.lower_bound;

        // Stride remains the same
        StridedInterval::new(self.bits, self.stride.clone(), new_lower, new_upper)
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
        if self.is_empty() {
            return StridedInterval::bottom(self.bits);
        }

        // Negation in two's complement is: -x = ~x + 1
        let not_interval = !self;
        let one = StridedInterval::constant(self.bits, 1);
        &not_interval + &one
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
        if self.is_empty() {
            return StridedInterval::bottom(self.bits);
        }

        if shift >= self.bits {
            // Shifting by more than or equal to bit width results in 0
            return StridedInterval::constant(self.bits, 0);
        }

        // For left shift, multiply by 2^shift
        let factor = BigUint::one() << shift;
        let new_stride = &self.stride * &factor;
        let new_lower = StridedInterval::modular_mul(&self.lower_bound, &factor, self.bits);
        let new_upper = StridedInterval::modular_mul(&self.upper_bound, &factor, self.bits);

        StridedInterval::new(self.bits, new_stride, new_lower, new_upper)
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
        if self.is_empty() {
            return StridedInterval::bottom(self.bits);
        }

        if shift >= self.bits {
            // Shifting by more than or equal to bit width results in 0
            return StridedInterval::constant(self.bits, 0);
        }

        // For right shift, divide by 2^shift (integer division)
        let divisor = BigUint::one() << shift;
        let new_stride = if self.stride == BigUint::zero() {
            BigUint::zero()
        } else {
            max(BigUint::one(), &self.stride / &divisor)
        };

        let new_lower = &self.lower_bound >> shift;
        let new_upper = &self.upper_bound >> shift;

        StridedInterval::new(self.bits, new_stride, new_lower, new_upper)
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

        if value.bits > 64 {
            return Err("Value too large for u64");
        }

        // Use ToPrimitive trait for conversion
        value
            .lower_bound
            .to_u64()
            .ok_or("Value cannot be converted to u64")
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
        assert_eq!(si.bits, 32);
        assert_eq!(si.stride, BigUint::zero());
        assert_eq!(si.lower_bound, BigUint::from(42u32));
        assert_eq!(si.upper_bound, BigUint::from(42u32));
        assert!(si.is_integer());
        assert!(!si.is_empty());
        assert!(!si.is_top());
    }

    #[test]
    fn test_top() {
        let si = StridedInterval::top(32);
        assert_eq!(si.bits, 32);
        assert_eq!(si.stride, BigUint::one());
        assert_eq!(si.lower_bound, BigUint::zero());
        assert_eq!(si.upper_bound, (BigUint::one() << 32) - BigUint::one());
        assert!(!si.is_integer());
        assert!(!si.is_empty());
        assert!(si.is_top());
    }

    #[test]
    fn test_bottom() {
        let si = StridedInterval::bottom(32);
        assert_eq!(si.bits, 32);
        assert!(si.is_empty());
        assert!(!si.is_integer());
        assert!(!si.is_top());
    }

    #[test]
    fn test_range() {
        let si = StridedInterval::range(32, 10u32, 20u32);
        assert_eq!(si.bits, 32);
        assert_eq!(si.stride, BigUint::one());
        assert_eq!(si.lower_bound, BigUint::from(10u32));
        assert_eq!(si.upper_bound, BigUint::from(20u32));
        assert!(!si.is_integer());
        assert!(!si.is_empty());
        assert!(!si.is_top());
    }

    #[test]
    fn test_add() {
        let a = StridedInterval::constant(32, 10u32);
        let b = StridedInterval::constant(32, 20u32);
        let result = &a + &b;
        assert_eq!(result.lower_bound, BigUint::from(30u32));
        assert_eq!(result.upper_bound, BigUint::from(30u32));
        assert!(result.is_integer());

        let a = StridedInterval::range(32, 10u32, 20u32);
        let b = StridedInterval::range(32, 5u32, 15u32);
        let result = &a + &b;
        assert_eq!(result.lower_bound, BigUint::from(15u32));
        assert_eq!(result.upper_bound, BigUint::from(35u32));
        assert!(!result.is_integer());
    }

    #[test]
    fn test_sub() {
        let a = StridedInterval::constant(32, 30u32);
        let b = StridedInterval::constant(32, 10u32);
        let result = &a - &b;
        assert_eq!(result.lower_bound, BigUint::from(20u32));
        assert_eq!(result.upper_bound, BigUint::from(20u32));
        assert!(result.is_integer());

        let a = StridedInterval::range(32, 20u32, 30u32);
        let b = StridedInterval::range(32, 5u32, 15u32);
        let result = &a - &b;
        assert_eq!(result.lower_bound, BigUint::from(5u32));
        assert_eq!(result.upper_bound, BigUint::from(25u32));
        assert!(!result.is_integer());
    }

    #[test]
    fn test_intersection() {
        let a = StridedInterval::range(32, 10u32, 30u32);
        let b = StridedInterval::range(32, 20u32, 40u32);
        let result = a.intersection(&b);
        assert_eq!(result.lower_bound, BigUint::from(20u32));
        assert_eq!(result.upper_bound, BigUint::from(30u32));
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
        assert_eq!(result.lower_bound, BigUint::from(10u32));
        assert_eq!(result.upper_bound, BigUint::from(40u32));

        let a = StridedInterval::range(32, 10u32, 20u32);
        let b = StridedInterval::range(32, 30u32, 40u32);
        let result = a.union(&b);
        assert_eq!(result.lower_bound, BigUint::from(10u32));
        assert_eq!(result.upper_bound, BigUint::from(40u32));
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
        assert_eq!(si.bits, 32);
        assert_eq!(si.stride, BigUint::from(2u32));
        assert_eq!(si.lower_bound, BigUint::zero());
        assert_eq!(si.upper_bound, (BigUint::one() << 32) - BigUint::one());
    }

    #[test]
    fn test_from_u32() {
        let si: StridedInterval = 42u32.into();
        assert_eq!(si.bits, 32);
        assert_eq!(si.lower_bound, BigUint::from(42u32));
        assert_eq!(si.upper_bound, BigUint::from(42u32));
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
        let si = StridedInterval {
            bits: 8,
            stride: BigUint::one(),
            lower_bound: BigUint::from(250u32),
            upper_bound: BigUint::from(5u32),
        };
        let (min_u, max_u) = si.get_unsigned_bounds();
        assert_eq!(min_u, BigUint::from(250u32));
        assert_eq!(max_u, BigUint::from(255u32)); // max for 8 bits

        // Empty interval
        let si = StridedInterval::bottom(8);
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
        let si = StridedInterval {
            bits: 8,
            stride: BigUint::one(),
            lower_bound: BigUint::from(250u32),
            upper_bound: BigUint::from(5u32),
        };
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::from(-6));
        assert_eq!(max_s, BigInt::from(5));

        // Empty interval
        let si = StridedInterval::bottom(8);
        let (min_s, max_s) = si.get_signed_bounds();
        assert_eq!(min_s, BigInt::zero());
        assert_eq!(max_s, BigInt::zero());
    }

    #[test]
    fn test_clamp_upper_unsigned() {
        // Clamp upper within bounds
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(15u32);
        assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        assert_eq!(clamped.upper_bound, BigUint::from(15u32));

        // Clamp upper to current upper (no-op)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(20u32);
        assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        assert_eq!(clamped.upper_bound, BigUint::from(20u32));

        // Clamp upper below lower (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_upper_unsigned(5u32);
        assert!(clamped.is_empty());

        // Clamp upper on empty interval (should be bottom)
        let si = StridedInterval::bottom(8);
        let clamped = si.clamp_upper_unsigned(15u32);
        assert!(clamped.is_empty());

        // Clamp upper on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_upper_unsigned(12u32);
        assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        let clamped = si.clamp_upper_unsigned(10u32);
        assert!(clamped.is_empty());
    }

    #[test]
    fn test_clamp_lower_unsigned() {
        // Clamp lower within bounds
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(15u32);
        assert_eq!(clamped.lower_bound, BigUint::from(15u32));
        assert_eq!(clamped.upper_bound, BigUint::from(20u32));

        // Clamp lower to current lower (no-op)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(10u32);
        assert_eq!(clamped.lower_bound, BigUint::from(10u32));
        assert_eq!(clamped.upper_bound, BigUint::from(20u32));

        // Clamp lower above upper (should be bottom)
        let si = StridedInterval::range(8, 10u32, 20u32);
        let clamped = si.clamp_lower_unsigned(25u32);
        assert!(clamped.is_empty());

        // Clamp lower on empty interval (should be bottom)
        let si = StridedInterval::bottom(8);
        let clamped = si.clamp_lower_unsigned(15u32);
        assert!(clamped.is_empty());

        // Clamp lower on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_lower_unsigned(12u32);
        assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        assert_eq!(clamped.upper_bound, BigUint::from(12u32));
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
        let si = StridedInterval::bottom(8);
        let clamped = si.clamp_upper_signed(10i32);
        assert!(clamped.is_empty());

        // Clamp upper on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_upper_signed(12i32);
        assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        assert_eq!(clamped.upper_bound, BigUint::from(12u32));
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
        let si = StridedInterval::bottom(8);
        let clamped = si.clamp_lower_signed(10i32);
        assert!(clamped.is_empty());

        // Clamp lower on singleton (should clamp to itself or bottom)
        let si = StridedInterval::constant(8, 12u32);
        let clamped = si.clamp_lower_signed(12i32);
        assert_eq!(clamped.lower_bound, BigUint::from(12u32));
        assert_eq!(clamped.upper_bound, BigUint::from(12u32));
        let clamped = si.clamp_lower_signed(15i32);
        assert!(clamped.is_empty());
    }
}
