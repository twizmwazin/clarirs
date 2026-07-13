use num_bigint::BigUint;
use serde::Serialize;

/// A wrapper excluded from identity: all `Ignored<T>` compare equal and hash to
/// nothing, so a field of this type is skipped by its container's derived
/// `Eq`/`Ord`/`Hash`. The wrapped value is still carried.
#[derive(Debug, Clone, Serialize)]
pub struct Ignored<T>(pub T);

impl<T> PartialEq for Ignored<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for Ignored<T> {}
impl<T> PartialOrd for Ignored<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T> Ord for Ignored<T> {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl<T> std::hash::Hash for Ignored<T> {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl<T> From<T> for Ignored<T> {
    fn from(value: T) -> Self {
        Ignored(value)
    }
}

/// This struct is a sort of hack to allow us to access data in python
/// annotations, while supporting unknown annotations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum AnnotationType {
    Unknown {
        name: String,
        /// Pickled Python object, kept only to reconstruct it; `Ignored`
        /// excludes it from the annotation's identity.
        value: Ignored<Vec<u8>>,
        /// Hash of the originating Python object; identifies the annotation.
        obj_hash: i64,
    },
    SimplificationAvoidance,
    StridedInterval {
        stride: BigUint,
        lower_bound: BigUint,
        upper_bound: BigUint,
    },
    EmptyStridedInterval,
    Region {
        region_id: String,
        region_base_addr: BigUint,
    },
    Uninitialized,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Annotation {
    type_: AnnotationType,
    eliminatable: bool,
    relocatable: bool,
}

impl Annotation {
    pub fn new(type_: AnnotationType, eliminatable: bool, relocatable: bool) -> Self {
        Annotation {
            type_,
            eliminatable,
            relocatable,
        }
    }

    pub fn name(&self) -> &str {
        match self.type_ {
            AnnotationType::Unknown { ref name, .. } => name,
            AnnotationType::SimplificationAvoidance => "SimplificationAvoidanceAnnotation",
            AnnotationType::StridedInterval { .. } => "StridedIntervalAnnotation",
            AnnotationType::EmptyStridedInterval => "EmptyStridedIntervalAnnotation",
            AnnotationType::Region { .. } => "RegionAnnotation",
            AnnotationType::Uninitialized => "UninitializedAnnotation",
        }
    }

    pub fn type_(&self) -> &AnnotationType {
        &self.type_
    }

    pub fn eliminatable(&self) -> bool {
        self.eliminatable
    }

    pub fn relocatable(&self) -> bool {
        self.relocatable
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use std::cmp::Ordering;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_of<T: Hash>(value: &T) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn test_ignored_always_equal() {
        assert_eq!(Ignored(1), Ignored(2));
        assert_eq!(Ignored(vec![1u8, 2, 3]), Ignored(vec![]));
        assert_eq!(Ignored(1).partial_cmp(&Ignored(999)), Some(Ordering::Equal));
        assert_eq!(Ignored(1).cmp(&Ignored(999)), Ordering::Equal);
    }

    #[test]
    fn test_ignored_hashes_to_nothing() {
        // All Ignored values hash identically (the Hash impl writes nothing).
        assert_eq!(hash_of(&Ignored(1u64)), hash_of(&Ignored(2u64)));
        assert_eq!(
            hash_of(&Ignored("abc".to_string())),
            hash_of(&Ignored("xyz".to_string()))
        );
    }

    #[test]
    fn test_ignored_from_and_carries_value() {
        let ignored: Ignored<u32> = 42.into();
        assert_eq!(ignored.0, 42);
        let cloned = ignored.clone();
        assert_eq!(cloned.0, 42);
    }

    #[test]
    fn test_annotation_new_and_accessors() {
        let ann = Annotation::new(AnnotationType::SimplificationAvoidance, true, false);
        assert_eq!(ann.type_(), &AnnotationType::SimplificationAvoidance);
        assert!(ann.eliminatable());
        assert!(!ann.relocatable());

        let ann = Annotation::new(AnnotationType::Uninitialized, false, true);
        assert!(!ann.eliminatable());
        assert!(ann.relocatable());
    }

    #[test]
    fn test_annotation_names() {
        let unknown = AnnotationType::Unknown {
            name: "MyCustomAnnotation".to_string(),
            value: Ignored(vec![1, 2, 3]),
            obj_hash: 7,
        };
        assert_eq!(
            Annotation::new(unknown, true, true).name(),
            "MyCustomAnnotation"
        );
        assert_eq!(
            Annotation::new(AnnotationType::SimplificationAvoidance, true, true).name(),
            "SimplificationAvoidanceAnnotation"
        );
        assert_eq!(
            Annotation::new(
                AnnotationType::StridedInterval {
                    stride: BigUint::from(4u32),
                    lower_bound: BigUint::from(0u32),
                    upper_bound: BigUint::from(16u32),
                },
                true,
                true
            )
            .name(),
            "StridedIntervalAnnotation"
        );
        assert_eq!(
            Annotation::new(AnnotationType::EmptyStridedInterval, true, true).name(),
            "EmptyStridedIntervalAnnotation"
        );
        assert_eq!(
            Annotation::new(
                AnnotationType::Region {
                    region_id: "stack".to_string(),
                    region_base_addr: BigUint::from(0x7fff_0000u32),
                },
                true,
                true
            )
            .name(),
            "RegionAnnotation"
        );
        assert_eq!(
            Annotation::new(AnnotationType::Uninitialized, true, true).name(),
            "UninitializedAnnotation"
        );
    }

    #[test]
    fn test_unknown_identity_ignores_pickled_value() {
        // Two Unknown annotations differing only in their pickled payload are
        // identical: the payload is wrapped in Ignored.
        let a = Annotation::new(
            AnnotationType::Unknown {
                name: "A".to_string(),
                value: Ignored(vec![1, 2, 3]),
                obj_hash: 1234,
            },
            true,
            false,
        );
        let b = Annotation::new(
            AnnotationType::Unknown {
                name: "A".to_string(),
                value: Ignored(vec![9, 9, 9]),
                obj_hash: 1234,
            },
            true,
            false,
        );
        assert_eq!(a, b);
        assert_eq!(hash_of(&a), hash_of(&b));
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn test_unknown_identity_uses_obj_hash_and_name() {
        let base = Annotation::new(
            AnnotationType::Unknown {
                name: "A".to_string(),
                value: Ignored(vec![]),
                obj_hash: 1,
            },
            true,
            false,
        );
        let different_hash = Annotation::new(
            AnnotationType::Unknown {
                name: "A".to_string(),
                value: Ignored(vec![]),
                obj_hash: 2,
            },
            true,
            false,
        );
        let different_name = Annotation::new(
            AnnotationType::Unknown {
                name: "B".to_string(),
                value: Ignored(vec![]),
                obj_hash: 1,
            },
            true,
            false,
        );
        assert_ne!(base, different_hash);
        assert_ne!(base, different_name);
    }

    #[test]
    fn test_annotation_flags_are_part_of_identity() {
        let a = Annotation::new(AnnotationType::Uninitialized, true, false);
        let b = Annotation::new(AnnotationType::Uninitialized, false, false);
        let c = Annotation::new(AnnotationType::Uninitialized, true, true);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_eq!(a, Annotation::new(AnnotationType::Uninitialized, true, false));
    }
}
