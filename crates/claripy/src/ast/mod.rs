pub mod base;
pub mod bits;
pub mod bool;
pub mod bv;
pub mod fp;
pub mod py_factory;
pub mod shared_ops;
pub mod string;

use pyo3::{prelude::*, PyClass};

use clarirs_core::ast::AstRef;

use super::import_submodule;

pub trait PyAst: PyClass {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self>;
    fn as_base(self_: PyRef<Self>) -> PyRef<base::Base>;
}

pub fn get_astref<T>(self_: PyRef<T>) -> AstRef<'static>
where
    T: PyAst,
{
    T::as_base(self_).ast.clone()
}

pub(crate) fn import(py: Python, m: &Bound<PyModule>) -> PyResult<()> {
    import_submodule(py, m, "claripy.ast", "base", base::import)?;
    import_submodule(py, m, "claripy.ast", "bits", bits::import)?;
    import_submodule(py, m, "claripy.ast", "bool", bool::import)?;
    import_submodule(py, m, "claripy.ast", "bv", bv::import)?;
    import_submodule(py, m, "claripy.ast", "fp", fp::import)?;
    import_submodule(py, m, "claripy.ast", "strings", string::import)?;

    m.add_class::<base::Base>()?;
    m.add_class::<bits::Bits>()?;
    m.add_class::<bool::Bool>()?;
    m.add_class::<bv::BV>()?;
    m.add_class::<fp::FP>()?;
    m.add_class::<string::AstString>()?;
    Ok(())
}
