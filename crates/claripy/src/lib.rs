#[macro_use]
mod macros;

pub mod annotation;
pub mod ast;
pub mod error;
pub mod prelude;
pub mod solver;
pub mod weakref;

use prelude::*;

fn import_submodule<'py>(
    py: Python<'py>,
    m: &Bound<'py, PyModule>,
    package: &str,
    name: &str,
    import_func: fn(Python<'py>, &Bound<'py, PyModule>) -> PyResult<()>,
) -> PyResult<()> {
    let submodule = PyModule::new(py, name)?;
    import_func(py, &submodule)?;
    pyo3::py_run!(
        py,
        submodule,
        &format!(
            "import sys; sys.modules['{}.{}'] = submodule",
            package, name
        )
    );
    m.add_submodule(&submodule)?;
    Ok(())
}

#[pyfunction(name = "simplify")]
fn py_simplify(py: Python, ast: PyRef<Base>) -> Result<Py<Base>, ClaripyError> {
    py_ast_from_astref(py, get_astref(ast).simplify()?)
}

#[pymodule]
pub fn claripy(py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    import_submodule(py, m, "claripy", "ast", ast::import)?;
    import_submodule(py, m, "claripy", "solver", solver::import)?;

    add_pyfunctions!(
        m,
        ast::bool::BoolS,
        ast::bool::BoolV,
        ast::bv::BVS,
        ast::bv::BVV,
        ast::shared_ops::Not,
        ast::shared_ops::And,
        ast::shared_ops::Or,
        ast::shared_ops::Xor,
        ast::shared_ops::Eq_,
        ast::fp::FPS,
        ast::fp::FPV,
    );

    m.add_class::<ast::base::Base>()?;
    m.add_class::<ast::bits::Bits>()?;
    m.add_class::<ast::bool::Bool>()?;
    m.add_class::<ast::bv::BV>()?;
    m.add_class::<ast::fp::FP>()?;
    m.add_class::<ast::string::String>()?;

    m.add_class::<annotation::PyAnnotation>()?;
    m.add_class::<annotation::SimplificationAvoidanceAnnotation>()?;

    m.add("FSORT_FLOAT", ast::fp::fsort_float())?;
    m.add("FSORT_DOUBLE", ast::fp::fsort_double())?;

    m.add_function(wrap_pyfunction!(py_simplify, m)?)?;

    Ok(())
}
