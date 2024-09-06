#![allow(non_snake_case)]

use crate::ast::bits::Bits;
use crate::prelude::*;

#[pyclass(name = "FSort", module = "claripy.ast.fp")]
#[derive(Clone)]
pub struct PyFSort(FSort);

impl PyFSort {
    pub fn new(fsort: FSort) -> Self {
        PyFSort(fsort)
    }
}

impl Into<FSort> for PyFSort {
    fn into(self) -> FSort {
        self.0
    }
}

pub fn fsort_float() -> PyFSort {
    PyFSort(FSort::f32())
}

pub fn fsort_double() -> PyFSort {
    PyFSort(FSort::f64())
}

#[pyclass(extends=Bits, subclass, frozen, weakref, module="claripy.ast.bits")]
pub struct FP {}

impl FP {
    pub fn new() -> Self {
        FP {}
    }
}

impl PyAst for FP {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Bits::new_from_astref(ast_ref).add_subclass(FP::new())
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super().into_super()
    }
}

#[pyfunction]
pub fn FPS(py: Python, name: String, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.fps(name, sort.0)?)
}

#[pyfunction]
pub fn FPV(py: Python, value: f64, sort: PyFSort) -> Result<Py<FP>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT
            .fpv(<f64 as Into<Float>>::into(value).to_fsort(sort.into(), FPRM::default()))?,
    )
}

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<PyFSort>()?;
    m.add_class::<FP>()?;

    add_pyfunctions!(m, FPS, FPV,);

    m.add("FSORT_FLOAT", fsort_float())?;
    m.add("FSORT_DOUBLE", fsort_double())?;

    Ok(())
}
