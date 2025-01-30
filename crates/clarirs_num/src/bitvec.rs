use std::fmt::Debug;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

use num_bigint::BigUint;
use num_traits::cast::ToPrimitive;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Error)]
pub enum BitVecError {
    #[error("BitVector too short: {value:?} is too short for length {length}")]
    BitVectorTooShort { value: BigUint, length: usize },
}

/// BitVec are represented as a SmallVec of usize, where each usize is a word of
/// the bitvector.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct BitVec {
    words: SmallVec<[u64; 1]>,
    length: usize,
    #[serde(skip)] // TODO: This needs to be recalculated when deserializing
    final_word_mask: u64,
}

impl BitVec {
    pub fn new(words: SmallVec<[u64; 1]>, length: usize) -> Self {
        // Calculate mask for the final word - keep all valid bits
        let bits_in_last_word = length % 64;
        let final_word_mask = if bits_in_last_word == 0 {
            u64::MAX
        } else {
            (1u64 << bits_in_last_word) - 1
        };

        Self {
            words: SmallVec::from_iter(words.iter().copied()),
            length,
            final_word_mask,
        }
    }

    pub fn from_prim<T>(value: T) -> Self
    where
        T: Into<u64>,
    {
        BitVec::from_prim_with_size(value, size_of::<T>() * 8)
    }

    pub fn from_prim_with_size<T>(value: T, length: usize) -> Self
    where
        T: Into<u64>,
    {
        let mut words = SmallVec::new();
        words.push(value.into());
        Self::new(words, length)
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.length
    }

    pub fn from_biguint(value: &BigUint, length: usize) -> Result<BitVec, BitVecError> {
        if value.bits() as usize > length {
            return Err(BitVecError::BitVectorTooShort {
                value: value.clone(),
                length,
            });
        }

        if value == &BigUint::ZERO {
            let mut words = SmallVec::new();
            let num_words = (length + 63) / 64; // Number of 64-bit words
            if num_words > 0 {
                words.push(0);
            }
            return Ok(BitVec::new(words, length));
        }

        // Convert the BigUint to a BitVec
        Ok(BitVec::new(value.iter_u64_digits().collect(), length))
    }

    pub fn from_biguint_trunc(value: &BigUint, length: usize) -> BitVec {
        if value == &BigUint::ZERO {
            // Represent zero as a single zero-filled word,
            let mut words = SmallVec::new();
            // Determine number of  64-bit words are needed for the given length
            let num_words = (length + 63) / 64;
            // If there's at least one word in the length, ensure we have that word
            if num_words > 0 {
                words.push(0);
            }
            return BitVec::new(words, length);
        }

        let num_words = (length + 63) / 64;

        BitVec::new(value.iter_u64_digits().take(num_words).collect(), length)
    }

    pub fn as_biguint(&self) -> BigUint {
        BigUint::from_bytes_be(
            self.words
                .iter()
                .flat_map(|w| w.to_be_bytes())
                .collect::<Vec<u8>>()
                .as_slice(),
        )
    }

    pub fn sign(&self) -> bool {
        if self.length == 0 {
            return false;
        }

        let last_word_index = (self.length - 1) / 64;
        let bit_index = (self.length - 1) % 64;

        if let Some(word) = self.words.get(last_word_index) {
            (word & (1u64 << bit_index)) != 0
        } else {
            false
        }
    }

    pub fn reverse(&self) -> Self {
        let mut new_bv = self.words.clone();
        new_bv.reverse();
        BitVec::new(new_bv, self.length)
    }

    // Check if all bits in the BitVec are 1
    pub fn is_all_ones(&self) -> bool {
        // Check each word to see if all bits are set to 1
        for (i, &word) in self.words.iter().enumerate() {
            if i == self.words.len() - 1 {
                // For the final word, apply the final_word_mask
                if word != self.final_word_mask {
                    return false;
                }
            } else {
                // For all other words, they must be completely filled with 1s
                if word != !0 {
                    return false;
                }
            }
        }
        true
    }

    // Check if all bits in the BitVec are 0
    pub fn is_zero(&self) -> bool {
        // Check each word to see if all bits are 0
        self.words.iter().all(|&word| word == 0)
    }

    // Converts the BitVec to a usize if it fits within the usize range, otherwise returns None
    pub fn to_usize(&self) -> Option<usize> {
        // Check that the BitVec's bit length does not exceed the size of usize
        if self.len() > (usize::BITS as usize) {
            None
        } else {
            Some(self.to_biguint().to_usize().unwrap_or(0))
        }
    }

    // Converts the BitVec to BigUint
    pub fn to_biguint(&self) -> BigUint {
        BigUint::from_bytes_le(
            &self
                .words
                .iter()
                .flat_map(|w| w.to_le_bytes())
                .collect::<Vec<u8>>(),
        )
    }

    pub fn to_u64(&self) -> Option<u64> {
        if self.len() > 64 {
            // The BitVec is too large to fit in a u64
            return None;
        }

        // Combine all words into a single u64
        let mut value: u64 = 0;
        for (i, &word) in self.words.iter().enumerate() {
            value |= word << (i * 64);
        }
        Some(value)
    }

    /// Counts the number of leading zeros in the BitVec.
    pub fn leading_zeros(&self) -> usize {
        let mut count = 0;
        for word in self.words.iter().rev() {
            // Start from the most significant word
            if *word == 0 {
                count += 64; // Each word is 64 bits, so add 64 if the word is all zeros
            } else {
                count += word.leading_zeros() as usize; // Count leading zeros in the current word
                break; // Stop once a non-zero word is found
            }
        }
        count.min(self.length) // Ensure count does not exceed the BitVec length
    }

    // Creates and returns a BitVec with these zero-filled words.
    pub fn zeros(length: usize) -> BitVec {
        let mut words = SmallVec::new();
        let num_words = (length + 63) / 64; // Number of 64-bit words
        for _ in 0..num_words {
            words.push(0);
        }
        BitVec::new(words, length)
    }

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

    pub fn signed_lt(&self, other: &Self) -> bool {
        assert_eq!(
            self.length, other.length,
            "BitVec lengths must match for comparison"
        );

        // Different signs
        match (self.sign(), other.sign()) {
            (true, false) => true,  // Negative < Positive
            (false, true) => false, // Positive > Negative
            _ => {
                // Same sign - compare magnitudes
                for (a, b) in self.words.iter().zip(other.words.iter()).rev() {
                    if a != b {
                        // If negative, reverse the comparison
                        return (a < b) ^ self.sign();
                    }
                }
                false // Equal numbers
            }
        }
    }

    pub fn signed_le(&self, other: &Self) -> bool {
        self.signed_lt(other) || self == other
    }

    pub fn signed_gt(&self, other: &Self) -> bool {
        !self.signed_le(other)
    }

    pub fn signed_ge(&self, other: &Self) -> bool {
        !self.signed_lt(other)
    }

    pub fn extract(&self, from: usize, to: usize) -> Result<Self, BitVecError> {
        if from > to || to >= self.len() {
            return Err(BitVecError::BitVectorTooShort {
                value: self.to_biguint(),
                length: self.len(),
            });
        }

        let mut new_bv = SmallVec::new();
        let mut word_index = from / 64;
        let mut bit_index = from % 64;
        let mut current_word = 0;
        let mut current_word_bits = 0;

        while bit_index <= to {
            let bits_to_copy = (to + 1 - bit_index).min(64 - current_word_bits);
            let mask = (1u64 << bits_to_copy) - 1;
            let bits = (self.words[word_index] >> bit_index) & mask;
            current_word |= bits << current_word_bits;
            current_word_bits += bits_to_copy;
            bit_index += bits_to_copy;

            if current_word_bits == 64 {
                new_bv.push(current_word);
                current_word = 0;
                current_word_bits = 0;
            }

            if bit_index % 64 == 0 {
                word_index += 1;
            }
        }

        if current_word_bits > 0 {
            new_bv.push(current_word);
        }

        Ok(BitVec::new(new_bv, to - from + 1))
    }

    pub fn concat(&self, other: &Self) -> Self {
        let mut new_bv = other.words.clone();
        let shift = other.length % 64;

        if shift == 0 {
            // Words are perfectly aligned, just extend
            new_bv.extend(self.words.iter().copied());
        } else {
            // Handle unaligned case

            // Combine the words with appropriate shifting
            for (i, &word) in self.words.iter().enumerate() {
                if i == 0 {
                    // First word needs to be merged with the last word of self
                    if let Some(last) = new_bv.last_mut() {
                        *last |= word << shift;
                    }
                    // Push the remaining bits to the next word
                    new_bv.push(word >> (64 - shift));
                } else {
                    // Subsequent words need to be split across two words
                    if let Some(last) = new_bv.last_mut() {
                        *last |= word << shift;
                        new_bv.push(word >> (64 - shift));
                    }
                }
            }

            // Check if we have an extra word
            let expected_words = (self.len() + other.len() + 63) / 64;
            if new_bv.len() > expected_words {
                new_bv.pop();
            }
        }

        BitVec::new(new_bv, self.length + other.length)
    }

    // Power function for BitVec
    pub fn pow(&self, exponent: &BitVec) -> Result<BitVec, BitVecError> {
        let exp_value = exponent.to_biguint();
        let mut result = BigUint::from(1u64);
        let mut base_value = self.to_biguint();
        let mut exp_value = exp_value.clone();

        while !exp_value.is_zero() {
            if &exp_value & BigUint::from(1u64) == BigUint::from(1u64) {
                result *= &base_value;
            }
            base_value = &base_value * &base_value;
            exp_value >>= 1;
        }

        BitVec::from_biguint(&result, self.len())
    }

    pub fn zero_extend(&self, additional_bits: usize) -> Self {
        BitVec::from_prim_with_size(0u8, additional_bits).concat(self)
    }

    pub fn sign_extend(&self, additional_bits: usize) -> Self {
        let extension = if self.sign() {
            BitVec::from_biguint_trunc(
                &((BigUint::from(1u8) << additional_bits) - 1u8),
                additional_bits,
            )
        } else {
            BitVec::from_biguint_trunc(&BigUint::zero(), additional_bits)
        };
        extension.concat(self)
    }
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawBitVector")
            .field("words", &self.words)
            .field("length", &self.length)
            .finish()
    }
}

impl TryFrom<BigUint> for BitVec {
    type Error = BitVecError;

    fn try_from(value: BigUint) -> Result<Self, Self::Error> {
        BitVec::from_biguint(&value, value.bits() as usize)
    }
}

impl From<&BitVec> for BigUint {
    fn from(bv: &BitVec) -> Self {
        BigUint::from_bytes_be(
            bv.words
                .iter()
                .flat_map(|w| w.to_be_bytes())
                .collect::<Vec<u8>>()
                .as_slice(),
        )
    }
}

impl PartialOrd for BitVec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BitVec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.words
            .iter()
            .zip(other.words.iter())
            .rev()
            .filter_map(|(l, r)| l.partial_cmp(r))
            .next()
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

impl Add for BitVec {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut new_bv = self
            .words
            .iter()
            .zip(rhs.words.iter())
            .fold(
                (SmallVec::with_capacity(self.words.len()), 0),
                |(mut result, carry), (l, r)| {
                    let (sum1, carry1) = l.overflowing_add(*r);
                    let (sum2, carry2) = sum1.overflowing_add(carry);
                    let new_carry = carry1 as u64 + carry2 as u64;
                    result.push(sum2);
                    (result, new_carry)
                },
            )
            .0;

        // Mask the final word if necessary
        if let Some(w) = new_bv.get_mut(self.len() - 1) {
            *w &= self.final_word_mask;
        }

        BitVec::new(new_bv, self.length)
    }
}

impl Sub for BitVec {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        // Ensure both BitVecs have the same length
        assert_eq!(
            self.length, rhs.length,
            "BitVec lengths must match for subtraction"
        );

        // Perform word-wise subtraction with wrapping
        let mut new_words = self
            .words
            .iter()
            .zip(rhs.words.iter())
            .fold(
                (SmallVec::with_capacity(self.words.len()), 0),
                |(mut result, borrow), (l, r)| {
                    let (diff1, borrow1) = l.overflowing_sub(*r);
                    let (diff2, borrow2) = diff1.overflowing_sub(borrow);
                    let new_borrow = borrow1 as u64 + borrow2 as u64;
                    result.push(diff2);
                    (result, new_borrow)
                },
            )
            .0;

        // Mask the final word if necessary
        if let Some(w) = new_words.get_mut(self.len() - 1) {
            *w &= self.final_word_mask;
        }

        BitVec::new(new_words, self.length)
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

impl Div for BitVec {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) / BigUint::from(&rhs)), self.length)
    }
}

impl Mul for BitVec {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) * BigUint::from(&rhs)), self.length)
    }
}

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

impl Rem for BitVec {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) % BigUint::from(&rhs)), self.length)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract() {
        // Test case 1: Extract middle bits (inclusive bounds)
        let bv = BitVec::from_prim_with_size(0b11110000u8, 8);
        let extracted = bv.extract(2, 5).unwrap();
        assert_eq!(extracted.to_biguint(), BigUint::from(0b1100u8));
        assert_eq!(extracted.len(), 4);

        // Test case 2: Extract spanning multiple words
        let bv = BitVec::from_prim_with_size(0xFFFFFFFFFFFFFFFFu64, 64);
        let extracted = bv.extract(56, 63).unwrap();
        assert_eq!(extracted.to_biguint(), BigUint::from(0xFFu8));
        assert_eq!(extracted.len(), 8);

        // Test case 3: Extract single bit
        let bv = BitVec::from_prim_with_size(0b10101010u8, 8);
        let extracted = bv.extract(3, 3).unwrap();
        assert_eq!(extracted.to_biguint(), BigUint::from(1u8));
        assert_eq!(extracted.len(), 1);

        // Test case 4: Extract at bounds
        let bv = BitVec::from_prim_with_size(0xFFu8, 8);
        let extracted = bv.extract(0, 7).unwrap();
        assert_eq!(extracted.to_biguint(), BigUint::from(0xFFu8));
        assert_eq!(extracted.len(), 8);

        // Additional test case for bounds checking
        assert!(
            bv.extract(7, 8).is_err(),
            "Should fail on out-of-bounds extraction"
        );
    }

    #[test]
    fn test_concat() {
        // Zero BitVecs
        assert_eq!(
            BitVec::from_prim(0u8).concat(&BitVec::from_prim(0u8)),
            BitVec::from_prim(0u16)
        );

        // Test concatenating with unaligned bits
        let bv1 = BitVec::from_prim_with_size(0b111u8, 3);
        let bv2 = BitVec::from_prim_with_size(0b101u8, 3);
        let result = bv1.concat(&bv2);
        assert_eq!(result.words.len(), 1);
        assert_eq!(result.length, 6);
        assert_eq!(result.to_biguint(), BigUint::from(0b111101u8));

        // Test multi-word
        let bv1 = BitVec::from_prim_with_size(0xFFFF_FFFF_FFFF_FFFF_u64, 64);
        let bv2 = BitVec::from_prim_with_size(0x0u64, 64);
        let result = bv1.concat(&bv2);
        assert_eq!(result.words.len(), 2);
        assert_eq!(result.length, 128);
        assert_eq!(
            result.to_biguint(),
            BigUint::from(0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000_u128)
        );

        // Test concatenating two 40-bit values
        let bv1 = BitVec::from_prim_with_size(0xFFFF_FFFFFFu64, 40);
        let bv2 = BitVec::from_prim_with_size(0xAAAA_AAAAAAu64, 40);
        let result = bv1.concat(&bv2);
        assert_eq!(result.words.len(), 2);
        assert_eq!(result.length, 80);
        assert_eq!(
            result.to_biguint(),
            BigUint::from_bytes_be(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA])
        );
    }

    #[test]
    fn test_zero_extend() {
        // Test extending by 0 bits
        let bv = BitVec::from_prim_with_size(0b1111u8, 4);
        let extended = bv.zero_extend(0);
        assert_eq!(extended.len(), 4);
        assert_eq!(extended.to_biguint(), BigUint::from(0b1111u8));

        // Test extending by a few bits
        let bv = BitVec::from_prim_with_size(0b1111u8, 4);
        let extended = bv.zero_extend(4);
        assert_eq!(extended.len(), 8);
        assert_eq!(extended.to_biguint(), BigUint::from(0b00001111u8));

        // Test extending across word boundary
        let bv = BitVec::from_prim_with_size(0xFFFFFFFFFFFFFFFFu64, 64);
        let extended = bv.zero_extend(64);
        assert_eq!(extended.len(), 128);
        assert_eq!(extended.words.len(), 2);
        assert_eq!(extended.words[0], 0xFFFFFFFFFFFFFFFF);
        assert_eq!(extended.words[1], 0);
    }

    #[test]
    fn test_sign_extend() {
        // Test extending positive number
        let bv = BitVec::from_prim_with_size(0b0111u8, 4);
        let extended = bv.sign_extend(4);
        assert_eq!(extended.len(), 8);
        assert_eq!(extended.to_biguint(), BigUint::from(0b00000111u8));

        // Test extending negative number
        let bv = BitVec::from_prim_with_size(0b1111u8, 4);
        let extended = bv.sign_extend(4);
        assert_eq!(extended.len(), 8);
        assert_eq!(extended.to_biguint(), BigUint::from(0b11111111u8));

        // Test extending across word boundary
        let bv = BitVec::from_prim_with_size(0x8000000000000000u64, 64);
        let extended = bv.sign_extend(64);
        assert_eq!(extended.len(), 128);
        assert_eq!(extended.words.len(), 2);
        assert_eq!(extended.words[0], 0x8000000000000000);
        assert_eq!(extended.words[1], 0xFFFFFFFFFFFFFFFF);

        // Test zero extension (no change)
        let bv = BitVec::from_prim_with_size(0b1111u8, 4);
        let extended = bv.sign_extend(0);
        assert_eq!(extended.len(), 4);
        assert_eq!(extended.to_biguint(), BigUint::from(0b1111u8));
    }
}
