use super::{BitVec, BitVecError};
use num_bigint::BigUint;
use num_traits::Zero;

impl BitVec {
    pub fn extract(&self, from: usize, to: usize) -> Result<Self, BitVecError> {
        if from > to || to >= self.len() {
            return Err(BitVecError::BitVectorTooShort {
                value: self.to_biguint(),
                length: self.len(),
            });
        }

        let extract_len = to - from + 1;
        let mut result = BitVec::zeros(extract_len);

        let mut remaining_bits = extract_len;
        let mut src_word_idx = from / 64;
        let mut src_bit_idx = from % 64;
        let mut dst_bit_idx = 0;

        while remaining_bits > 0 {
            // How many bits we can copy in this iteration
            let bits_this_round = std::cmp::min(
                remaining_bits,                                    // How many bits we still need
                64 - std::cmp::max(src_bit_idx, dst_bit_idx % 64), // Space left in current word
            );

            // Extract bits from source word
            let mask = ((1u64 << bits_this_round) - 1) << src_bit_idx;
            let bits = (self.words[src_word_idx] & mask) >> src_bit_idx;

            // Insert bits into destination word
            let dst_word_idx = dst_bit_idx / 64;
            let dst_shift = dst_bit_idx % 64;
            result.words[dst_word_idx] |= bits << dst_shift;

            // Update indices
            remaining_bits -= bits_this_round;
            src_bit_idx += bits_this_round;
            if src_bit_idx >= 64 {
                src_word_idx += 1;
                src_bit_idx = 0;
            }
            dst_bit_idx += bits_this_round;
        }

        Ok(result)
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
