use num_bigint::{BigInt, BigUint};
use serde::Serialize;

/// This struct is a sort of hack to allow us to access data in python
/// annotations, while supporting unknown annotations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum AnnotationType {
    Unknown {
        name: String,
        value: Vec<u8>,
    },
    SimplificationAvoidance,
    StridedInterval {
        stride: BigUint,
        // Bounds are signed: claripy allows negative bounds (e.g. from
        // constraints like `x > -5`); they wrap to the value's bit width when
        // the strided interval is materialized.
        lower_bound: BigInt,
        upper_bound: BigInt,
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
