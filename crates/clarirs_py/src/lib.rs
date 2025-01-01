#[allow(clippy::multiple_crate_versions)]
#[macro_use]
mod macros;

pub mod annotation;
pub mod ast;
pub mod error;
pub mod prelude;
pub mod py_err;
pub mod pyslicemethodsext;
pub mod solver;

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
fn py_simplify(py: Python, expr: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
    if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
        BV::new(py, &bv_value.get().inner.simplify().unwrap()).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        })
    } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
        Bool::new(py, &bool_value.get().inner.simplify().unwrap()).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        })
    } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
        FP::new(py, &fp_value.get().inner.simplify().unwrap()).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        })
    } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
        PyAstString::new(py, &string_value.get().inner.simplify().unwrap()).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        })
    } else {
        panic!("Unsupported type");
    }
}

#[pymodule]
pub fn clarirs(py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    import_submodule(py, m, "clarirs", "annotation", annotation::import)?;
    import_submodule(py, m, "clarirs", "ast", ast::import)?;
    import_submodule(py, m, "clarirs", "solver", solver::import)?;

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
    let fp = PyModule::new(py, "clarirs.fp")?;
    fp.add_class::<ast::fp::PyRM>()?;
    fp.add_class::<ast::fp::PyFSort>()?;
    fp.add("FSORT_FLOAT", ast::fp::fsort_float())?;
    fp.add("FSORT_DOUBLE", ast::fp::fsort_double())?;
    pyo3::py_run!(py, fp, "import sys; sys.modules['clarirs.fp'] = fp");
    m.add_submodule(&fp)?;

    Ok(())
}
