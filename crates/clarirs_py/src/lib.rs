#[allow(clippy::multiple_crate_versions)]
#[macro_use]
mod macros;

pub mod annotation;
pub mod ast;
mod dynsolver;
pub mod error;
pub mod prelude;
pub mod py_err;
pub mod pyslicemethodsext;
pub mod solver;

use clarirs_core::algorithms::{ExcavateIte, Replace};
use prelude::*;

fn import_submodule<'py>(
    py: Python<'py>,
    m: &Bound<'py, PyModule>,
    package: &str,
    name: &str,
    import_func: impl FnOnce(Python<'py>, &Bound<'py, PyModule>) -> PyResult<()>,
) -> PyResult<()> {
    let submodule = PyModule::new(py, name)?;
    import_func(py, &submodule)?;
    pyo3::py_run!(
        py,
        submodule,
        &format!("import sys; sys.modules['{package}.{name}'] = submodule")
    );
    m.add_submodule(&submodule)?;
    Ok(())
}

fn add_submodule<'py>(
    py: Python<'py>,
    m: &Bound<'py, PyModule>,
    package: &str,
    name: &str,
    build_func: impl FnOnce(Python<'py>) -> PyResult<Bound<'py, PyModule>>,
) -> PyResult<Bound<'py, PyModule>> {
    let submodule = build_func(py)?;
    pyo3::py_run!(
        py,
        submodule,
        &format!("import sys; sys.modules['{package}.{name}'] = submodule")
    );
    m.add_submodule(&submodule)?;
    m.add(name, submodule.clone())?;
    Ok(submodule)
}

#[pyfunction(name = "simplify")]
fn py_simplify<'py>(
    py: Python<'py>,
    expr: Bound<'py, Base>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
        BV::new(py, &bv_value.get().inner.simplify().unwrap())
            .map(|b| b.into_any().downcast::<Base>().unwrap().clone())
    } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
        Bool::new(py, &bool_value.get().inner.simplify().unwrap())
            .map(|b| b.into_any().downcast::<Base>().unwrap().clone())
    } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
        FP::new(py, &fp_value.get().inner.simplify().unwrap())
            .map(|b| b.into_any().downcast::<Base>().unwrap().clone())
    } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
        PyAstString::new(py, &string_value.get().inner.simplify().unwrap())
            .map(|b| b.into_any().downcast::<Base>().unwrap().clone())
    } else {
        panic!("Unsupported type");
    }
}

#[pyfunction(name = "replace")]
fn py_replace<'py>(
    expr: Bound<'py, Base>,
    old: Bound<'py, Base>,
    new: Bound<'py, Base>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    Base::from_dynast(
        expr.py(),
        Base::to_dynast(expr)?.replace(&Base::to_dynast(old)?, &Base::to_dynast(new)?)?,
    )
}

#[pyfunction(name = "excavate_ite")]
fn py_excavate_ite<'py>(
    py: Python<'py>,
    expr: Bound<'py, Base>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    Base::from_dynast(py, Base::to_dynast(expr)?.excavate_ite()?)
}

#[pyfunction]
fn is_true(expr: CoerceBool<'_>) -> Result<bool, ClaripyError> {
    Ok(expr.0.get().inner.simplify()?.is_true())
}

#[pyfunction]
fn is_false(expr: CoerceBool<'_>) -> Result<bool, ClaripyError> {
    Ok(expr.0.get().inner.simplify()?.is_false())
}

#[pymodule]
pub fn claripy(py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    let annotation = add_submodule(py, m, "claripy", "annotation", annotation::build_module)?;
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
        ast::bv::ShL,
        ast::bv::LShR,
        ast::bv::AShR,
        ast::bv::RotateLeft,
        ast::bv::RotateRight,
        ast::bv::Concat,
        ast::bv::Extract,
        ast::bv::ZeroExt,
        ast::bv::SignExt,
        ast::bv::Reverse,
        ast::bv::Eq_,
        ast::bv::Neq,
        ast::bv::ULT,
        ast::bv::ULE,
        ast::bv::UGT,
        ast::bv::UGE,
        ast::bv::SLT,
        ast::bv::SLE,
        ast::bv::SGT,
        ast::bv::SGE,
        ast::bv::SI,
        ast::bv::VS,
        ast::bv::Union,
        ast::bv::Intersection,
        // FP
        ast::fp::FPS,
        ast::fp::FPV,
        ast::fp::fpFP,
        ast::fp::FpToFP,
        ast::fp::BvToFpUnsigned,
        ast::fp::fpToIEEEBV,
        ast::fp::FpToUbv,
        ast::fp::FpToBv,
        ast::fp::FpNeg,
        ast::fp::FpAbs,
        ast::fp::FpAdd,
        ast::fp::FpSub,
        ast::fp::FpMul,
        ast::fp::FpDiv,
        ast::fp::FpSqrt,
        ast::fp::FpEq,
        ast::fp::FpNeq,
        ast::fp::FpLt,
        ast::fp::FpLeq,
        ast::fp::FpGt,
        ast::fp::FpGeq,
        ast::fp::FpIsNan,
        ast::fp::FpIsInf,
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
        ast::string::StrToInt,
        ast::string::IntToStr,
        ast::string::StrIsDigit,
        ast::string::StrEq,
        ast::string::StrNeq,
        // Shared
        ast::r#if,
        ast::not,
        ast::and,
        ast::or,
        ast::xor,
    );

    m.add_class::<ast::base::Base>()?;
    m.add_class::<ast::bits::Bits>()?;
    m.add_class::<ast::bool::Bool>()?;
    m.add_class::<ast::bv::BV>()?;
    m.add_class::<ast::fp::FP>()?;
    m.add_class::<ast::string::PyAstString>()?;

    m.add("Annotation", annotation.getattr("Annotation")?)?;
    m.add(
        "SimplificationAvoidanceAnnotation",
        annotation.getattr("SimplificationAvoidanceAnnotation")?,
    )?;
    m.add(
        "StridedIntervalAnnotation",
        annotation.getattr("StridedIntervalAnnotation")?,
    )?;
    m.add("RegionAnnotation", annotation.getattr("RegionAnnotation")?)?;
    m.add(
        "UninitializedAnnotation",
        annotation.getattr("UninitializedAnnotation")?,
    )?;

    m.add("ClaripyError", py.get_type::<py_err::ClaripyError>())?;
    m.add(
        "ClaripyTypeError",
        py.get_type::<py_err::ClaripyTypeError>(),
    )?;
    m.add("UnsatError", py.get_type::<py_err::UnsatError>())?;
    m.add(
        "ClaripyFrontendError",
        py.get_type::<py_err::ClaripyFrontendError>(),
    )?;
    m.add(
        "ClaripySolverInterruptError",
        py.get_type::<py_err::ClaripySolverInterruptError>(),
    )?;
    m.add(
        "ClaripyOperationError",
        py.get_type::<py_err::ClaripyOperationError>(),
    )?;
    m.add(
        "ClaripyZeroDivisionError",
        py.get_type::<py_err::ClaripyZeroDivisionError>(),
    )?;
    m.add(
        "InvalidExtractBounds",
        py.get_type::<py_err::InvalidExtractBoundsError>(),
    )?;

    m.add("FSORT_FLOAT", ast::fp::fsort_float())?;
    m.add("FSORT_DOUBLE", ast::fp::fsort_double())?;

    m.add_function(wrap_pyfunction!(py_simplify, m)?)?;
    m.add_function(wrap_pyfunction!(py_replace, m)?)?;
    m.add_function(wrap_pyfunction!(py_excavate_ite, m)?)?;
    m.add_function(wrap_pyfunction!(is_true, m)?)?;
    m.add_function(wrap_pyfunction!(is_false, m)?)?;
    m.add_function(wrap_pyfunction!(ast::bool::ite_cases, m)?)?;
    m.add_function(wrap_pyfunction!(ast::bool::reverse_ite_cases, m)?)?;
    m.add_function(wrap_pyfunction!(ast::bool::ite_dict, m)?)?;
    m.add_class::<solver::PySolver>()?;
    m.add_class::<solver::PyConcreteSolver>()?;
    m.add_class::<solver::PyVSASolver>()?;
    m.add_class::<solver::PyZ3Solver>()?;

    // Compat

    // fp
    import_submodule(py, m, "claripy", "fp", |py, fp| {
        fp.add_class::<ast::fp::PyRM>()?;
        fp.add_class::<ast::fp::PyFSort>()?;
        fp.add("FSORT_FLOAT", ast::fp::fsort_float())?;
        fp.add("FSORT_DOUBLE", ast::fp::fsort_double())?;
        pyo3::py_run!(py, fp, "import sys; sys.modules['clarirs.fp'] = fp");
        Ok(())
    })?;

    Ok(())
}
