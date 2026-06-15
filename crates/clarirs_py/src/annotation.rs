use std::mem::discriminant;

use num_bigint::BigUint;
use pyo3::types::{PyDict, PyTuple, PyType};

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

impl<'py> FromPyObject<'_, 'py> for PyAnnotationType {
    type Error = PyErr;

    fn extract(anno_type: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        let anno_type = anno_type.cast::<PyType>()?;
        let anno_type_module_name = anno_type.getattr("__module__")?.extract::<String>()?;
        let anno_type_class_name = anno_type.getattr("__name__")?.extract::<String>()?;

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

/// `claripy.annotation.Annotation`
///
/// The base class for every annotation. This used to be defined as an embedded
/// Python source string because PyO3 could not express subclassable native
/// classes; it is now a real `#[pyclass]`, so the built-in annotations below
/// are genuine subclasses and user code can subclass it as well.
#[pyclass(name = "Annotation", subclass, frozen, module = "claripy.annotation")]
pub struct PyAnnotation;

#[pymethods]
impl PyAnnotation {
    /// Accept (and ignore) arbitrary arguments so that Python subclasses with
    /// their own `__init__` signatures can be instantiated, mirroring the
    /// behaviour of `object.__new__` when `__init__` is overridden.
    #[new]
    #[pyo3(signature = (*_args, **_kwargs))]
    fn py_new(_args: &Bound<'_, PyTuple>, _kwargs: Option<&Bound<'_, PyDict>>) -> Self {
        PyAnnotation
    }

    #[classattr]
    fn relocatable() -> bool {
        true
    }

    #[classattr]
    fn eliminatable() -> bool {
        true
    }
}

impl PyAnnotation {
    /// Convert a Python annotation object (an instance of this class or any of
    /// its subclasses) into the core [`Annotation`] consumed by the solver.
    pub fn to_annotation(slf: &Bound<'_, PyAnnotation>) -> Result<Annotation, ClaripyError> {
        let any = slf.as_any();
        if any.cast::<SimplificationAvoidanceAnnotation>().is_ok() {
            Ok(Annotation::new(
                AnnotationType::SimplificationAvoidance,
                false,
                false,
            ))
        } else if let Ok(si) = any.cast::<StridedIntervalAnnotation>() {
            let si = si.get();
            Ok(Annotation::new(
                AnnotationType::StridedInterval {
                    stride: si.stride.clone(),
                    lower_bound: si.lower_bound.clone(),
                    upper_bound: si.upper_bound.clone(),
                },
                false,
                false,
            ))
        } else if any.cast::<EmptyStridedIntervalAnnotation>().is_ok() {
            Ok(Annotation::new(
                AnnotationType::EmptyStridedInterval,
                false,
                false,
            ))
        } else if let Ok(region) = any.cast::<RegionAnnotation>() {
            let region = region.get();
            Ok(Annotation::new(
                AnnotationType::Region {
                    region_id: region.region_id.clone(),
                    region_base_addr: region.region_base_addr.clone(),
                },
                false,
                false,
            ))
        } else if any.cast::<UninitializedAnnotation>().is_ok() {
            Ok(Annotation::new(AnnotationType::Uninitialized, false, true))
        } else {
            // Unknown, user-defined annotation: preserve it losslessly by
            // pickling the Python object so it can be reconstructed later.
            let eliminatable = slf
                .getattr("eliminatable")
                .and_then(|v| v.extract::<bool>())
                .unwrap_or(true);
            let relocatable = slf
                .getattr("relocatable")
                .and_then(|v| v.extract::<bool>())
                .unwrap_or(true);
            let module_name = slf.getattr("__module__")?.extract::<String>()?;
            let class_name = slf
                .getattr("__class__")?
                .getattr("__name__")?
                .extract::<String>()?;
            let pickle_dumps = slf.py().import("pickle")?.getattr("dumps")?;
            Ok(Annotation::new(
                AnnotationType::Unknown {
                    name: format!("{module_name}:{class_name}"),
                    value: pickle_dumps.call1((slf,))?.extract::<Vec<u8>>()?,
                },
                eliminatable,
                relocatable,
            ))
        }
    }

    /// Build a Python annotation object from a core [`Annotation`].
    pub fn from_annotation<'py>(
        py: Python<'py>,
        annotation: &Annotation,
    ) -> Result<Bound<'py, PyAnnotation>, ClaripyError> {
        match annotation.type_() {
            AnnotationType::Unknown { value, .. } => {
                let pickle_loads = py.import("pickle")?.getattr("loads")?;
                Ok(pickle_loads.call1((value,))?.cast_into::<PyAnnotation>()?)
            }
            AnnotationType::SimplificationAvoidance => upcast(Bound::new(
                py,
                (SimplificationAvoidanceAnnotation, PyAnnotation),
            )?),
            AnnotationType::StridedInterval {
                stride,
                lower_bound,
                upper_bound,
            } => upcast(Bound::new(
                py,
                (
                    StridedIntervalAnnotation {
                        stride: stride.clone(),
                        lower_bound: lower_bound.clone(),
                        upper_bound: upper_bound.clone(),
                    },
                    PyAnnotation,
                ),
            )?),
            AnnotationType::EmptyStridedInterval => upcast(Bound::new(
                py,
                (EmptyStridedIntervalAnnotation, PyAnnotation),
            )?),
            AnnotationType::Region {
                region_id,
                region_base_addr,
            } => upcast(Bound::new(
                py,
                (
                    RegionAnnotation {
                        region_id: region_id.clone(),
                        region_base_addr: region_base_addr.clone(),
                    },
                    PyAnnotation,
                ),
            )?),
            AnnotationType::Uninitialized => {
                upcast(Bound::new(py, (UninitializedAnnotation, PyAnnotation))?)
            }
        }
    }
}

/// Upcast a concrete annotation subclass instance to its `PyAnnotation` base.
fn upcast<'py, T>(bound: Bound<'py, T>) -> Result<Bound<'py, PyAnnotation>, ClaripyError> {
    Ok(bound.into_any().cast_into::<PyAnnotation>()?)
}

/// `claripy.annotation.SimplificationAvoidanceAnnotation`
#[pyclass(extends = PyAnnotation, subclass, frozen, module = "claripy.annotation")]
pub struct SimplificationAvoidanceAnnotation;

#[pymethods]
impl SimplificationAvoidanceAnnotation {
    #[new]
    fn py_new() -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation).add_subclass(SimplificationAvoidanceAnnotation)
    }

    #[classattr]
    fn relocatable() -> bool {
        false
    }

    #[classattr]
    fn eliminatable() -> bool {
        false
    }

    fn __repr__(&self) -> &'static str {
        "SimplificationAvoidanceAnnotation()"
    }
}

/// `claripy.annotation.StridedIntervalAnnotation`
#[pyclass(extends = PyAnnotation, subclass, frozen, module = "claripy.annotation")]
pub struct StridedIntervalAnnotation {
    #[pyo3(get)]
    stride: BigUint,
    #[pyo3(get)]
    lower_bound: BigUint,
    #[pyo3(get)]
    upper_bound: BigUint,
}

#[pymethods]
impl StridedIntervalAnnotation {
    #[new]
    fn py_new(
        stride: BigUint,
        lower_bound: BigUint,
        upper_bound: BigUint,
    ) -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation).add_subclass(StridedIntervalAnnotation {
            stride,
            lower_bound,
            upper_bound,
        })
    }

    #[classattr]
    fn relocatable() -> bool {
        false
    }

    #[classattr]
    fn eliminatable() -> bool {
        false
    }

    fn __repr__(&self) -> String {
        format!(
            "StridedIntervalAnnotation(stride={}, lower_bound={}, upper_bound={})",
            self.stride, self.lower_bound, self.upper_bound
        )
    }
}

/// `claripy.annotation.EmptyStridedIntervalAnnotation`
#[pyclass(extends = PyAnnotation, subclass, frozen, module = "claripy.annotation")]
pub struct EmptyStridedIntervalAnnotation;

#[pymethods]
impl EmptyStridedIntervalAnnotation {
    #[new]
    fn py_new() -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation).add_subclass(EmptyStridedIntervalAnnotation)
    }

    #[classattr]
    fn relocatable() -> bool {
        false
    }

    #[classattr]
    fn eliminatable() -> bool {
        false
    }

    fn __repr__(&self) -> &'static str {
        "EmptyStridedIntervalAnnotation()"
    }
}

/// `claripy.annotation.RegionAnnotation`
#[pyclass(extends = PyAnnotation, subclass, frozen, module = "claripy.annotation")]
pub struct RegionAnnotation {
    #[pyo3(get)]
    region_id: String,
    #[pyo3(get)]
    region_base_addr: BigUint,
}

#[pymethods]
impl RegionAnnotation {
    #[new]
    fn py_new(region_id: String, region_base_addr: BigUint) -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation).add_subclass(RegionAnnotation {
            region_id,
            region_base_addr,
        })
    }

    #[classattr]
    fn relocatable() -> bool {
        false
    }

    #[classattr]
    fn eliminatable() -> bool {
        false
    }

    fn __repr__(&self) -> String {
        format!(
            "RegionAnnotation(region_id={}, region_base_addr={})",
            self.region_id, self.region_base_addr
        )
    }
}

/// `claripy.annotation.UninitializedAnnotation`
#[pyclass(extends = PyAnnotation, subclass, frozen, module = "claripy.annotation")]
pub struct UninitializedAnnotation;

#[pymethods]
impl UninitializedAnnotation {
    #[new]
    fn py_new() -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation).add_subclass(UninitializedAnnotation)
    }

    #[classattr]
    fn relocatable() -> bool {
        true
    }

    #[classattr]
    fn eliminatable() -> bool {
        false
    }

    fn __repr__(&self) -> &'static str {
        "UninitializedAnnotation()"
    }
}

pub(crate) fn build_module(py: Python<'_>) -> PyResult<Bound<'_, PyModule>> {
    let module = PyModule::new(py, "claripy.annotation")?;
    module.add_class::<PyAnnotation>()?;
    module.add_class::<SimplificationAvoidanceAnnotation>()?;
    module.add_class::<StridedIntervalAnnotation>()?;
    module.add_class::<EmptyStridedIntervalAnnotation>()?;
    module.add_class::<RegionAnnotation>()?;
    module.add_class::<UninitializedAnnotation>()?;
    Ok(module)
}
