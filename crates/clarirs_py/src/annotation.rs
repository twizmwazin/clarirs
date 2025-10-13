use std::{ffi::CString, mem::discriminant, str::FromStr};

use num_bigint::BigUint;
use pyo3::types::PyType;

use crate::prelude::*;

// This isn't actually exported in python, but it makes more sense to go here
// than anywhere else
#[derive(Debug)]
pub struct PyAnnotationType(AnnotationType);

impl PyAnnotationType {
    pub fn new(type_: AnnotationType) -> Self {
        PyAnnotationType(type_)
    }

    pub fn matches(&self, other: &AnnotationType) -> bool {
        match (&self.0, other) {
            // In the unknown case, we need to compare the name field
            (
                AnnotationType::Unknown { name: name1, .. },
                AnnotationType::Unknown { name: name2, .. },
            ) => name1 == name2,
            // In the other cases, we can just compare the discriminants
            (..) => discriminant(&self.0) == discriminant(other),
        }
    }
}

impl From<AnnotationType> for PyAnnotationType {
    fn from(annotation_type: AnnotationType) -> Self {
        PyAnnotationType(annotation_type)
    }
}

impl From<PyAnnotationType> for AnnotationType {
    fn from(py_annotation_type: PyAnnotationType) -> Self {
        py_annotation_type.0
    }
}

impl<'py> FromPyObject<'py> for PyAnnotationType {
    fn extract_bound(anno_type: &Bound<'py, PyAny>) -> PyResult<Self> {
        let anno_type = anno_type.downcast::<PyType>()?;
        let anno_type_module_name = anno_type.getattr("__module__")?.extract::<String>()?;
        let anno_type_class_name = anno_type
            .getattr("__name__")?
            .extract::<String>()?;

        Ok(match (
            anno_type_module_name.as_str(),
            anno_type_class_name.as_str(),
        ) {
            ("claripy.annotation", "SimplificationAvoidanceAnnotation") => {
                AnnotationType::SimplificationAvoidance
            }
            ("claripy.annotation", "StridedIntervalAnnotation") => {
                AnnotationType::StridedInterval {
                    stride: BigUint::from(0u32),
                    lower_bound: BigUint::from(0u32),
                    upper_bound: BigUint::from(0u32),
                }
            }
            ("claripy.annotation", "RegionAnnotation") => AnnotationType::Region {
                region_id: String::new(),
                region_base_addr: BigUint::from(0u32),
            },
            ("claripy.annotation", "UninitializedAnnotation") => AnnotationType::Uninitialized,
            (anno_module_name, anno_class_name) => AnnotationType::Unknown {
                name: format!("{anno_module_name}:{anno_class_name}"),
                value: Vec::new(),
            },
        }
        .into())
    }
}

#[derive(Clone, Debug)]
pub struct PyAnnotation(pub Annotation);

impl PyAnnotation {
    pub fn new(type_: AnnotationType, eliminatable: bool, relocatable: bool) -> Self {
        PyAnnotation(Annotation::new(type_, eliminatable, relocatable))
    }
}

impl From<Annotation> for PyAnnotation {
    fn from(annotation: Annotation) -> Self {
        PyAnnotation(annotation)
    }
}

impl From<PyAnnotation> for Annotation {
    fn from(py_annotation: PyAnnotation) -> Self {
        py_annotation.0
    }
}

impl FromPyObject<'_> for PyAnnotation {
    fn extract_bound(annotation: &Bound<'_, PyAny>) -> PyResult<Self> {
        let pickle_dumps = annotation.py().import("pickle")?.getattr("dumps")?;
        let anno_module_name = annotation.getattr("__module__")?.extract::<String>()?;
        let anno_class_name = annotation
            .getattr("__class__")?
            .getattr("__name__")?
            .extract::<String>()?;

        Ok(
            match (anno_module_name.as_str(), anno_class_name.as_str()) {
                ("claripy.annotation", "SimplificationAvoidanceAnnotation") => {
                    PyAnnotation::new(AnnotationType::SimplificationAvoidance, false, false)
                }
                ("claripy.annotation", "StridedIntervalAnnotation") => {
                    let stride = annotation.getattr("stride")?.extract::<BigUint>()?;
                    let lower_bound = annotation.getattr("lower_bound")?.extract::<BigUint>()?;
                    let upper_bound = annotation.getattr("upper_bound")?.extract::<BigUint>()?;

                    PyAnnotation::new(
                        AnnotationType::StridedInterval {
                            stride,
                            lower_bound,
                            upper_bound,
                        },
                        false,
                        false,
                    )
                }
                ("claripy.annotation", "RegionAnnotation") => {
                    let region_id = annotation.getattr("region_id")?.extract::<String>()?;
                    let region_base_addr = annotation
                        .getattr("region_base_addr")?
                        .extract::<BigUint>()?;

                    PyAnnotation::new(
                        AnnotationType::Region {
                            region_id,
                            region_base_addr,
                        },
                        false,
                        false,
                    )
                }
                ("claripy.annotation", "UninitializedAnnotation") => {
                    PyAnnotation::new(AnnotationType::Uninitialized, false, true)
                }
                (anno_module_name, anno_class_name) => PyAnnotation::new(
                    AnnotationType::Unknown {
                        name: format!("{anno_module_name}:{anno_class_name}"),
                        value: pickle_dumps.call1((annotation,))?.extract::<Vec<u8>>()?,
                    },
                    false,
                    false,
                ),
            },
        )
    }
}

impl<'py> IntoPyObject<'py> for PyAnnotation {
    type Target = PyAny;
    type Output = Bound<'py, PyAny>;
    type Error = ClaripyError;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        Ok(match self.0.type_() {
            AnnotationType::Unknown { name: _, value } => {
                let pickle_loads = py.import("pickle")?.getattr("loads")?;
                pickle_loads.call1((value,))?
            }
            AnnotationType::SimplificationAvoidance => {
                let module = py.import("claripy.annotation")?;
                module
                    .getattr("SimplificationAvoidanceAnnotation")?
                    .call1(())?
            }
            AnnotationType::StridedInterval {
                stride,
                lower_bound,
                upper_bound,
            } => {
                let module = py.import("claripy.annotation")?;
                module.getattr("StridedIntervalAnnotation")?.call1((
                    stride,
                    lower_bound,
                    upper_bound,
                ))?
            }
            AnnotationType::Region {
                region_id,
                region_base_addr,
            } => {
                let module = py.import("claripy.annotation")?;
                module
                    .getattr("RegionAnnotation")?
                    .call1((region_id, region_base_addr))?
            }
            AnnotationType::Uninitialized => {
                let module = py.import("claripy.annotation")?;
                module.getattr("UninitializedAnnotation")?.call1(())?
            }
        })
    }
}

// This feels wrong, but it's the only way to get normal classes for compatible
// subclassing behavior in Python.
static MODULE_CODE: &str = r#"
class Annotation:
    relocatable = True
    eliminatable = True

class SimplificationAvoidanceAnnotation(Annotation):
    relocatable = False
    eliminatable = False

class StridedIntervalAnnotation(Annotation):
    relocatable = False
    eliminatable = False

    def __init__(self, stride, lower_bound, upper_bound):
        self.stride = stride
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound

class RegionAnnotation(Annotation):
    relocatable = False
    eliminatable = False

    def __init__(self, region_id, region_base_addr):
        self.region_id = region_id
        self.region_base_addr = region_base_addr

class UninitializedAnnotation(Annotation):
    relocatable = True
    eliminatable = False
"#;

pub(crate) fn build_module(py: Python<'_>) -> PyResult<Bound<'_, PyModule>> {
    let module = PyModule::from_code(
        py,
        &CString::from_str(MODULE_CODE)?,
        &CString::from_str("annotation.py")?,
        &CString::from_str("claripy.annotation")?,
    )?;
    Ok(module)
}
