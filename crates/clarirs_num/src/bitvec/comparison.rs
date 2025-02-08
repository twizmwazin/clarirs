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
