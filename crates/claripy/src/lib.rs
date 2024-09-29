#[macro_use]
mod macros;

pub mod annotation;
pub mod ast;
pub mod error;
pub mod prelude;
pub mod py_err;
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
    import_submodule(py, m, "claripy", "annotation", annotation::import)?;
    import_submodule(py, m, "claripy", "ast", ast::import)?;
    import_submodule(py, m, "claripy", "solver", solver::import)?;

    add_pyfunctions!(
        m,
        // Bool
        ast::bool::BoolS,
        ast::bool::BoolV,
        ast::bool::true_op,
        ast::bool::false_op,
        // BV
        ast::bv::BVS,
        ast::bv::BVV,
        ast::bv::Add,
        ast::bv::Sub,
        ast::bv::Mul,
        ast::bv::UDiv,
        ast::bv::SDiv,
        ast::bv::UMod,
        ast::bv::SMod,
        ast::bv::Pow,
        ast::bv::LShL,
        ast::bv::LShR,
        ast::bv::AShR,
        ast::bv::AShL,
        ast::bv::Concat,
        ast::bv::Extract,
        ast::bv::ULT,
        ast::bv::ULE,
        ast::bv::UGT,
        ast::bv::UGE,
        ast::bv::SLT,
        ast::bv::SLE,
        ast::bv::SGT,
        ast::bv::SGE,
        // FP
        ast::fp::FPS,
        ast::fp::FPV,
        // String
        ast::string::StringS,
        ast::string::StringV,
        ast::string::StringS,
        ast::string::StringV,
        ast::string::StrLen,
        ast::string::StrConcat,
        ast::string::StrSubstr,
        ast::string::StrContains,
        ast::string::StrIndexOf,
        ast::string::StrReplace,
        ast::string::StrPrefixOf,
        ast::string::StrSuffixOf,
        ast::string::StrToBV,
        ast::string::BVToStr,
        ast::string::StrIsDigit,
        ast::string::StrEq,
        ast::string::StrNeq,
        // Shared
        ast::shared_ops::Not,
        ast::shared_ops::And,
        ast::shared_ops::Or,
        ast::shared_ops::Xor,
        ast::shared_ops::Eq_,
        ast::shared_ops::If,
    );

    m.add_class::<ast::base::Base>()?;
    m.add_class::<ast::bits::Bits>()?;
    m.add_class::<ast::bool::Bool>()?;
    m.add_class::<ast::bv::BV>()?;
    m.add_class::<ast::fp::FP>()?;
    m.add_class::<ast::string::AstString>()?;

    m.add_class::<annotation::PyAnnotation>()?;
    m.add_class::<annotation::SimplificationAvoidanceAnnotation>()?;

    m.add_class::<py_err::PyClaripyError>()?;
    m.add_class::<py_err::UnsatError>()?;
    m.add_class::<py_err::ClaripyFrontendError>()?;
    m.add_class::<py_err::ClaripySolverInterruptError>()?;
    m.add_class::<py_err::ClaripyOperationError>()?;
    m.add_class::<py_err::ClaripyZeroDivisionError>()?;

    m.add("FSORT_FLOAT", ast::fp::fsort_float())?;
    m.add("FSORT_DOUBLE", ast::fp::fsort_double())?;

    m.add_function(wrap_pyfunction!(py_simplify, m)?)?;

    // Compat

    // fp
    let fp = PyModule::new(py, "fp")?;
    fp.add_class::<ast::fp::PyRM>()?;
    fp.add_class::<ast::fp::PyFSort>()?;
    fp.add("FSORT_FLOAT", ast::fp::fsort_float())?;
    fp.add("FSORT_DOUBLE", ast::fp::fsort_double())?;
    m.add_submodule(&fp)?;

    Ok(())
}
