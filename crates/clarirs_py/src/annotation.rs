use std::hash::{DefaultHasher, Hash, Hasher};

use num_bigint::BigInt;
use pyo3::types::PyTuple;

use crate::prelude::*;

#[pyclass(name = "Annotation", module = "clarirs.annotation", subclass, frozen)]
pub struct PyAnnotation {
    #[pyo3(get)]
    eliminatable: bool,
    #[pyo3(get)]
    relocatable: bool,
}

#[pymethods]
impl PyAnnotation {
    #[new]
    fn new(eliminatable: bool, relocatable: bool) -> PyClassInitializer<Self> {
        PyClassInitializer::from(PyAnnotation {
            eliminatable,
            relocatable,
        })
    }

    fn __getnewargs__(&self) -> PyResult<(bool, bool)> {
        Ok((self.eliminatable, self.relocatable))
    }

    fn __hash__(self_: Bound<PyAnnotation>) -> Result<isize, ClaripyError> {
        let mut hasher = DefaultHasher::new();

        self_.get_type().name()?.hash()?.hash(&mut hasher);
        self_.get().eliminatable.hash(&mut hasher);
        self_.get().relocatable.hash(&mut hasher);

        Ok(hasher.finish() as isize)
    }

    fn __eq__(self_: Bound<PyAnnotation>, other: Bound<PyAny>) -> PyResult<bool> {
        if let Ok(other) = other.downcast::<PyAnnotation>() {
            Ok(self_.get_type().name()?.extract::<String>()?
                == other.get_type().name()?.extract::<String>()?
                && self_.get().eliminatable == other.get().eliminatable
                && self_.get().relocatable == other.get().relocatable)
        } else {
            Ok(false)
        }
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
pub struct SimplificationAvoidanceAnnotation {}

#[pymethods]
impl SimplificationAvoidanceAnnotation {
    #[new]
    fn new() -> PyClassInitializer<Self> {
        PyAnnotation::new(false, false).add_subclass(SimplificationAvoidanceAnnotation {})
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::empty(py)
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
pub struct StridedIntervalAnnotation {
    #[pyo3(get)]
    stride: BigInt,
    #[pyo3(get)]
    lower_bound: BigInt,
    #[pyo3(get)]
    upper_bound: BigInt,
}

#[pymethods]
impl StridedIntervalAnnotation {
    #[new]
    #[pyo3(signature = (stride, lower_bound, upper_bound))]
    fn new(stride: BigInt, lower_bound: BigInt, upper_bound: BigInt) -> PyClassInitializer<Self> {
        PyAnnotation::new(false, false).add_subclass(StridedIntervalAnnotation {
            stride,
            lower_bound,
            upper_bound,
        })
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        PyTuple::new(
            py,
            &[
                self.stride.clone(),
                self.lower_bound.clone(),
                self.upper_bound.clone(),
            ],
        )
    }

    fn __str__(&self) -> String {
        format!(
            "SI(stride={}, lower_bound={}, upper_bound={})",
            self.stride, self.lower_bound, self.upper_bound
        )
    }

    fn __hash__(self_: Bound<StridedIntervalAnnotation>) -> Result<isize, ClaripyError> {
        let mut hasher = DefaultHasher::new();

        // Hash the parent class attributes
        self_.py_super()?.hash()?.hash(&mut hasher);

        // Hash the SI-specific attributes
        self_.get().stride.hash(&mut hasher);
        self_.get().lower_bound.hash(&mut hasher);
        self_.get().upper_bound.hash(&mut hasher);

        Ok(hasher.finish() as isize)
    }

    fn __eq__(
        self_: Bound<StridedIntervalAnnotation>,
        other: Bound<PyAny>,
    ) -> Result<bool, ClaripyError> {
        // First check if types match
        if let Ok(other) = other.downcast::<StridedIntervalAnnotation>() {
            Ok(self_.py_super()?.eq(other)?
                && self_.get().stride == other.get().stride
                && self_.get().lower_bound == other.get().lower_bound
                && self_.get().upper_bound == other.get().upper_bound)
        } else {
            Ok(false)
        }
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
pub struct RegionAnnotation {
    #[pyo3(get)]
    region_id: String,
    #[pyo3(get)]
    region_base_addr: BigInt,
}

#[pymethods]
impl RegionAnnotation {
    #[new]
    fn new(region_id: String, region_base_addr: BigInt) -> PyClassInitializer<Self> {
        PyAnnotation::new(false, false).add_subclass(RegionAnnotation {
            region_id,
            region_base_addr,
        })
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> Result<Bound<'py, PyTuple>, ClaripyError> {
        Ok(PyTuple::new(
            py,
            &[
                self.region_id.clone().into_bound_py_any(py)?,
                self.region_base_addr.clone().into_bound_py_any(py)?,
            ],
        )?)
    }

    fn __hash__(self_: Bound<RegionAnnotation>) -> Result<isize, ClaripyError> {
        let mut hasher = DefaultHasher::new();

        // Hash the parent class attributes
        self_.py_super()?.hash()?.hash(&mut hasher);

        // Hash the RegionAnnotation-specific attributes
        self_.get().region_id.hash(&mut hasher);
        self_.get().region_base_addr.hash(&mut hasher);

        Ok(hasher.finish() as isize)
    }

    fn __eq__(
        self_: Bound<RegionAnnotation>,
        other: Bound<PyAny>,
    ) -> Result<bool, ClaripyError> {
        // First check if types match
        if let Ok(other) = other.downcast::<RegionAnnotation>() {
            Ok(self_.py_super()?.eq(other)?
                && self_.get().region_id == other.get().region_id
                && self_.get().region_base_addr == other.get().region_base_addr)
        } else {
            Ok(false)
        }
    }
}

#[pyclass(extends = PyAnnotation, module = "clarirs.annotation", subclass, frozen)]
pub struct UninitializedAnnotation {}

#[pymethods]
impl UninitializedAnnotation {
    #[new]
    fn new() -> PyClassInitializer<Self> {
        PyAnnotation::new(false, true).add_subclass(UninitializedAnnotation {})
    }

    fn __getnewargs__<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        PyTuple::empty(py)
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyAnnotation>()?;
    m.add_class::<SimplificationAvoidanceAnnotation>()?;
    m.add_class::<StridedIntervalAnnotation>()?;
    m.add_class::<RegionAnnotation>()?;
    m.add_class::<UninitializedAnnotation>()?;

    Ok(())
}

pub(crate) fn extract_annotation(
    annotation: Bound<'_, PyAny>,
) -> Result<Annotation, ClaripyError> {
    let pickle_dumps = annotation.py().import("pickle")?.getattr("dumps")?;
    if let Ok(annotation) = annotation.downcast_exact::<StridedIntervalAnnotation>() {
        Ok(Annotation::new(
            AnnotationType::StridedInterval {
                stride: annotation.get().stride.clone(),
                lower_bound: annotation.get().lower_bound.clone(),
                upper_bound: annotation.get().upper_bound.clone(),
            },
            false,
            false,
        ))
    } else if let Ok(annotation) = annotation.downcast_exact::<RegionAnnotation>() {
        Ok(Annotation::new(
            AnnotationType::Region {
                region_id: annotation.get().region_id.clone(),
                region_base_addr: annotation.get().region_base_addr.clone(),
            },
            false,
            false,
        ))
    } else if let Ok(annotation) = annotation.downcast::<PyAnnotation>() {
        Ok(Annotation::new(
            AnnotationType::Unknown {
                name: annotation.get_type().name()?.extract::<String>()?,
                value: pickle_dumps.call1((annotation,))?.extract::<Vec<u8>>()?,
            },
            annotation.get().eliminatable,
            annotation.get().relocatable,
        ))
    } else {
        Err(ClaripyError::TypeError(format!(
            "Unsupported annotation type: {:?}",
            annotation.get_type().name()?
        )))
    }
}


pub(crate) fn create_pyannotation<'py> (
    py: Python<'py>,
    annotation: &Annotation,
) -> Result<Bound<'py, PyAny>, ClaripyError> {
    Ok(match annotation.type_() {
        AnnotationType::Unknown { name, value } => {
            let _ = name; // uneeded

            let pickle_loads = py.import("pickle")?.getattr("loads")?;
            pickle_loads
                .call1((value,))?
        }
        AnnotationType::StridedInterval { stride, lower_bound, upper_bound } => {
            Bound::new(py, StridedIntervalAnnotation::new(
                stride.clone(),
                lower_bound.clone(),
                upper_bound.clone(),
            ))?.into_any()
        }
        AnnotationType::Region { region_id, region_base_addr } => {
            Bound::new(py, RegionAnnotation::new(
                region_id.clone(),
                region_base_addr.clone(),
            ))?.into_any()
        },
    })
}
