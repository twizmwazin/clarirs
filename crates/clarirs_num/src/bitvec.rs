use std::fmt::Debug;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

use num_bigint::BigUint;
use num_traits::cast::ToPrimitive;
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
    fn test_bv_to_u64() {
        todo!()
        // assert_eq!(bv_to_usize(&vec![false, false, false, false]), 0);
        // assert_eq!(bv_to_usize(&vec![true, false, false, false]), 1);
        // assert_eq!(bv_to_usize(&vec![false, false, false, true]), 8);
        // assert_eq!(bv_to_usize(&vec![true, true, true, true]), 15);
    }

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
}
