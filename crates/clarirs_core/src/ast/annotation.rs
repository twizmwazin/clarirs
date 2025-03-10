use num_bigint::BigInt;
use serde::Serialize;

/// This struct is a sort of hack to allow us to access data in python
/// annotations, while supporting unknown annotations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum AnnotationType {
    Unknown {
        name: String,
        value: Vec<u8>,
    },
    StridedInterval {
        stride: BigInt,
        lower_bound: BigInt,
        upper_bound: BigInt,
    },
    Region {
        region_id: String,
        region_base_addr: BigInt,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
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
            AnnotationType::StridedInterval { .. } => "StridedIntervalAnnotation",
            AnnotationType::Region { .. } => "RegionAnnotation",
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
