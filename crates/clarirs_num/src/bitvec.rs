mod arithmetic;
mod bitwise;
mod comparison;
mod conversion;
mod extension;

#[cfg(test)]
mod tests;

use std::fmt::Debug;

use num_bigint::BigUint;
use num_traits::Zero;
use num_traits::cast::ToPrimitive;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use thiserror::Error;

use num_traits::One;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Error)]
pub enum BitVecError {
    #[error("BitVector too short: {value:?} is too short for length {length}")]
    BitVectorTooShort { value: BigUint, length: usize },
    #[error("BitVector not bite-sized: {length:?} is not a multiple of 8")]
    BitVectorNotByteSized { length: usize },
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
    pub fn new(mut words: SmallVec<[u64; 1]>, length: usize) -> Result<Self, BitVecError> {
        // Calculate mask for the final word - keep all valid bits
        let bits_in_last_word = length % 64;
        let final_word_mask = if bits_in_last_word == 0 {
            u64::MAX
        } else {
            (1u64 << bits_in_last_word) - 1
        };

        if !words.is_empty() {
            let last_idx = words.len() - 1;
            words[last_idx] &= final_word_mask;
        }

        Ok(Self {
            words,
            length,
            final_word_mask,
        })
    }

    pub fn from_prim<T>(value: T) -> Result<Self, BitVecError>
    where
        T: Into<u64>,
    {
        Self::from_prim_with_size(value, size_of::<T>() * 8)
    }

    pub fn from_prim_with_size<T>(value: T, length: usize) -> Result<Self, BitVecError>
    where
        T: Into<u64>,
    {
        let value_u64: u64 = value.into();

        // Ensure the value fits within the given length
        if length < 64 && value_u64 >= (1u64 << length) {
            return Err(BitVecError::BitVectorTooShort {
                value: BigUint::from(value_u64),
                length,
            });
        }

        let mut words = SmallVec::new();
        words.push(value_u64);
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
            return BitVec::new(words, length);
        }

        // Convert the BigUint to a BitVec
        BitVec::new(value.iter_u64_digits().collect(), length)
    }

    pub fn from_biguint_trunc(value: &BigUint, length: usize) -> BitVec {
        let truncated = value % (BigUint::from(2u32).pow(length as u32));
        Self::from_biguint(&truncated, length).expect("BitVec truncation failed")
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

    pub fn reverse_bytes(&self) -> Result<Self, BitVecError> {
        if self.length % 8 != 0 {
            return Err(BitVecError::BitVectorNotByteSized {
                length: self.length,
            });
        }

        // Calculate total number of bytes the bit-vector occupies.
        let total_bytes = self.length / 8;

        // 1. Extract the bytes of the bit-vector in little-endian order.
        // (Words store the low-order bytes first.)
        let mut bytes_le = Vec::with_capacity(total_bytes);
        for i in 0..total_bytes {
            let word_index = i / 8;
            let byte_index = i % 8;
            let byte = self.words[word_index].to_le_bytes()[byte_index];
            bytes_le.push(byte);
        }

        // Now, bytes_le[0] is the least significant byte,
        // and bytes_le[total_bytes - 1] is the most significant.

        // 2. Reverse the bytes.
        bytes_le.reverse();

        // 3. Pack the reversed bytes into 64-bit words.
        // (The first 8 bytes become the first word, the next 8 bytes the second word, and so on.)
        let num_words = self.words.len();
        let mut new_words = SmallVec::<[u64; 1]>::with_capacity(num_words);

        // Initialize with zeros.
        new_words.resize(num_words, 0);
        for (i, &byte) in bytes_le.iter().enumerate() {
            let word_index = i / 8;
            let byte_index = i % 8;
            new_words[word_index] |= (byte as u64) << (8 * byte_index);
        }

        // Clear out any bits beyond the bit-vector's length in the last word.
        let bits_in_last_word = self.length % 64;
        if bits_in_last_word != 0 {
            // Create a mask for the used bits.
            let mask = (1u64 << bits_in_last_word) - 1;
            let last_index = new_words.len() - 1;
            new_words[last_index] &= mask;
        }

        Self::new(new_words, self.length)
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
        let mut total = 0;
        for (i, &word) in self.words.iter().rev().enumerate() {
            let word_size = if i == 0 && self.length % 64 != 0 {
                self.length % 64
            } else {
                64
            };
            let zeros = (word.leading_zeros() as usize).saturating_sub(64 - word_size);
            if zeros != word_size {
                return total + zeros;
            }
            total += word_size;
        }
        total
    }

    pub fn to_biguint_abs(&self) -> BigUint {
        let n = self.to_biguint();
        if !self.sign() {
            // Non-negative
            n
        } else {
            // Negative: 2^bitwidth - n
            let bitwidth = self.len();
            let two_pow_bw = BigUint::one() << bitwidth;
            &two_pow_bw - &n
        }
    }

    // Creates and returns a BitVec with these zero-filled words.
    pub fn zeros(length: usize) -> BitVec {
        let mut words = SmallVec::new();
        let num_words = (length + 63) / 64; // Number of 64-bit words
        for _ in 0..num_words {
            words.push(0);
        }
        BitVec::new(words, length).expect("BitVec::new should never fail in zeros()")
    }

    // Creates and returns a BitVec with these one-filled words.
    pub fn ones(length: usize) -> BitVec {
        BitVec::from_biguint_trunc(&((BigUint::from(2u32) << length) - 1u32), length)
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
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawBitVector")
            .field("words", &self.words)
            .field("length", &self.length)
            .finish()
    }
}
