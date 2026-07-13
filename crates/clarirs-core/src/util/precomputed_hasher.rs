use std::hash::{BuildHasher, Hasher};

/// This is a shim that allows us to use a precomputed hash value in place of a real hasher.
/// It expects the hash implementation of the type to only set a u64 value.
#[derive(Default, Clone)]
pub struct PrecomputedHasher(u64);

impl PrecomputedHasher {
    pub fn new() -> Self {
        Self(0)
    }
}

impl Hasher for PrecomputedHasher {
    fn write(&mut self, _: &[u8]) {}

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

#[derive(Default, Copy, Clone)]
pub struct PrecomputedHasherBuilder;

impl BuildHasher for PrecomputedHasherBuilder {
    type Hasher = PrecomputedHasher;

    fn build_hasher(&self) -> Self::Hasher {
        PrecomputedHasher::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::hash::{BuildHasher, Hasher};

    #[test]
    fn test_new_and_default_start_at_zero() {
        assert_eq!(PrecomputedHasher::new().finish(), 0);
        assert_eq!(PrecomputedHasher::default().finish(), 0);
    }

    #[test]
    fn test_write_u64_sets_value() {
        let mut hasher = PrecomputedHasher::new();
        hasher.write_u64(0xdead_beef_cafe_babe);
        assert_eq!(hasher.finish(), 0xdead_beef_cafe_babe);
    }

    #[test]
    fn test_write_u64_overwrites_previous_value() {
        let mut hasher = PrecomputedHasher::new();
        hasher.write_u64(1);
        hasher.write_u64(2);
        // The last written value wins; values are not mixed.
        assert_eq!(hasher.finish(), 2);
    }

    #[test]
    fn test_write_bytes_is_a_no_op() {
        let mut hasher = PrecomputedHasher::new();
        hasher.write(b"ignored bytes");
        assert_eq!(hasher.finish(), 0);

        // Byte writes do not disturb a previously set value either.
        let mut hasher = PrecomputedHasher::new();
        hasher.write_u64(42);
        hasher.write(b"still ignored");
        assert_eq!(hasher.finish(), 42);
    }

    #[test]
    fn test_clone_preserves_state() {
        let mut hasher = PrecomputedHasher::new();
        hasher.write_u64(7);
        assert_eq!(hasher.clone().finish(), 7);
    }

    #[test]
    fn test_builder_produces_fresh_hashers() {
        let builder = PrecomputedHasherBuilder;
        let mut a = builder.build_hasher();
        a.write_u64(99);
        assert_eq!(a.finish(), 99);
        // A newly built hasher starts from zero regardless of prior use.
        assert_eq!(builder.build_hasher().finish(), 0);
    }

    #[test]
    fn test_hash_one_is_identity_for_u64() {
        // u64's Hash impl calls write_u64 exactly once, so the "hash" is the
        // value itself.
        let builder = PrecomputedHasherBuilder;
        assert_eq!(builder.hash_one(0u64), 0);
        assert_eq!(builder.hash_one(1234u64), 1234);
        assert_eq!(builder.hash_one(u64::MAX), u64::MAX);
    }

    #[test]
    fn test_usable_as_hashmap_hasher() {
        let mut map: HashMap<u64, &str, PrecomputedHasherBuilder> =
            HashMap::with_hasher(PrecomputedHasherBuilder);
        map.insert(1, "one");
        map.insert(2, "two");
        map.insert(1, "uno");
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&1), Some(&"uno"));
        assert_eq!(map.get(&2), Some(&"two"));
        assert_eq!(map.get(&3), None);
    }
}
