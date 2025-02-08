use super::BitVec;

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

impl BitVec {
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
}

#[cfg(test)]
mod tests {
    use crate::bitvec::BitVec;

    #[test]
    fn test_unsigned_comparison() {
        // Test basic ordering
        let bv1 = BitVec::from_prim_with_size(5u8, 8);
        let bv2 = BitVec::from_prim_with_size(10u8, 8);
        assert!(bv1 < bv2);
        assert!(bv1 <= bv2);
        assert!(bv2 > bv1);
        assert!(bv2 >= bv1);

        // Test equality
        let bv3 = BitVec::from_prim_with_size(5u8, 8);
        assert!(bv1 == bv3);
        assert!(bv1 <= bv3);
        assert!(bv1 >= bv3);

        // Test with larger numbers
        let bv4 = BitVec::from_prim_with_size(0xFFFFu16, 16);
        let bv5 = BitVec::from_prim_with_size(0x0000u16, 16);
        assert!(bv4 > bv5);
        assert!(bv5 < bv4);
    }

    #[test]
    fn test_signed_lt() {
        // Test positive numbers (5 and 10 in 8-bit)
        let pos1 = BitVec::from_prim_with_size(0x05u8, 8);
        let pos2 = BitVec::from_prim_with_size(0x0Au8, 8);
        assert!(pos1.signed_lt(&pos2));
        assert!(!pos2.signed_lt(&pos1));

        // Test negative numbers (-5 = 0xFB and -10 = 0xF6 in 8-bit two's complement)
        let neg1 = BitVec::from_prim_with_size(0xFBu8, 8);
        let neg2 = BitVec::from_prim_with_size(0xF6u8, 8);
        assert!(neg1.signed_lt(&neg2));
        assert!(!neg2.signed_lt(&neg1));

        // Test mixed signs
        assert!(neg1.signed_lt(&pos1));
        assert!(!pos1.signed_lt(&neg1));

        // Test equality
        let pos1_dup = BitVec::from_prim_with_size(0x05u8, 8);
        assert!(!pos1.signed_lt(&pos1_dup));
        assert!(!pos1_dup.signed_lt(&pos1));
    }

    #[test]
    fn test_signed_le() {
        // Test positive numbers (5 and 10 in 8-bit)
        let pos1 = BitVec::from_prim_with_size(0x05u8, 8);
        let pos2 = BitVec::from_prim_with_size(0x0Au8, 8);
        assert!(pos1.signed_le(&pos2));
        assert!(!pos2.signed_le(&pos1));

        // Test negative numbers (-5 = 0xFB and -10 = 0xF6 in 8-bit two's complement)
        let neg1 = BitVec::from_prim_with_size(0xFBu8, 8);
        let neg2 = BitVec::from_prim_with_size(0xF6u8, 8);
        assert!(neg1.signed_le(&neg2));
        assert!(!neg2.signed_le(&neg1));

        // Test equality
        let pos1_dup = BitVec::from_prim_with_size(0x05u8, 8);
        assert!(pos1.signed_le(&pos1_dup));
        assert!(pos1_dup.signed_le(&pos1));
    }

    #[test]
    fn test_signed_gt() {
        // Test positive numbers (5 and 10 in 8-bit)
        let pos1 = BitVec::from_prim_with_size(0x05u8, 8);
        let pos2 = BitVec::from_prim_with_size(0x0Au8, 8);
        assert!(!pos1.signed_gt(&pos2));
        assert!(pos2.signed_gt(&pos1));

        // Test negative numbers (-5 = 0xFB and -10 = 0xF6 in 8-bit two's complement)
        let neg1 = BitVec::from_prim_with_size(0xFBu8, 8);
        let neg2 = BitVec::from_prim_with_size(0xF6u8, 8);
        assert!(!neg1.signed_gt(&neg2));
        assert!(neg2.signed_gt(&neg1));

        // Test mixed signs
        assert!(pos1.signed_gt(&neg1));
        assert!(!neg1.signed_gt(&pos1));

        // Test equality
        let pos1_dup = BitVec::from_prim_with_size(0x05u8, 8);
        assert!(!pos1.signed_gt(&pos1_dup));
        assert!(!pos1_dup.signed_gt(&pos1));
    }

    #[test]
    fn test_signed_ge() {
        // Test positive numbers (5 and 10 in 8-bit)
        let pos1 = BitVec::from_prim_with_size(0x05u8, 8);
        let pos2 = BitVec::from_prim_with_size(0x0Au8, 8);
        assert!(!pos1.signed_ge(&pos2));
        assert!(pos2.signed_ge(&pos1));

        // Test negative numbers (-5 = 0xFB and -10 = 0xF6 in 8-bit two's complement)
        let neg1 = BitVec::from_prim_with_size(0xFBu8, 8);
        let neg2 = BitVec::from_prim_with_size(0xF6u8, 8);
        assert!(!neg1.signed_ge(&neg2));
        assert!(neg2.signed_ge(&neg1));

        // Test equality
        let pos1_dup = BitVec::from_prim_with_size(0x05u8, 8);
        assert!(pos1.signed_ge(&pos1_dup));
        assert!(pos1_dup.signed_ge(&pos1));
    }

    #[test]
    #[should_panic(expected = "BitVec lengths must match for comparison")]
    fn test_signed_comparison_different_lengths() {
        let bv1 = BitVec::from_prim_with_size(0x05u8, 8);
        let bv2 = BitVec::from_prim_with_size(0x0005u16, 16);
        let _ = bv1.signed_lt(&bv2);
    }
}
