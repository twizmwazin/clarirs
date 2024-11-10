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
        Self {
            words: SmallVec::from_iter(words.iter().copied()),
            length,
            final_word_mask: !(1 << (length % 64)) - 1,
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
            return BitVec::new(SmallVec::new(), length);
        }
        BitVec::new(
            value.iter_u64_digits().take((length / 64) + 1).collect(),
            length,
        )
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
        return self
            .words
            .last()
            .map(|w| w & (1 << (self.length % 64)) != 0)
            .unwrap_or(false);
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

    // Check if all bits are 1
    // pub fn is_all_ones(&self) -> bool {
    //     self.words.iter().all(|&word| word == !0) // !0 is all bits set to 1
    // }

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

    // pub fn to_biguint(&self) -> num_bigint::BigUint {
    //     num_bigint::BigUint::from_bytes_le(&self.words.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>())
    // }

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
        if let Some(w) = new_bv.get_mut(self.len() - 1) {
            *w &= self.final_word_mask;
        }
        BitVec::new(new_bv, self.length)
    }
}

impl Sub for BitVec {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        BitVec::from_biguint_trunc(&(BigUint::from(&self) - BigUint::from(&rhs)), self.length)
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
}
