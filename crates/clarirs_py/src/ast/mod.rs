pub mod args;
pub mod base;
pub mod bits;
pub mod bool;
pub mod bv;
pub mod coerce;
pub mod fp;
pub mod opstring;
pub mod string;

use std::sync::LazyLock;

use crate::prelude::*;

use super::import_submodule;

pub static GLOBAL_CONTEXT: LazyLock<Context<'static>> = LazyLock::new(Context::new);

#[pyfunction(name = "Not")]
pub fn not(py: Python, b: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
    if let Ok(b_bool) = b.clone().into_any().downcast::<Bool>() {
        return Bool::new(py, &GLOBAL_CONTEXT.not(&b_bool.get().inner)?).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        });
    } else if let Ok(b_bv) = b.clone().into_any().downcast::<BV>() {
        return BV::new(py, &GLOBAL_CONTEXT.not(&b_bv.get().inner)?).map(|b| {
            b.into_any()
                .downcast_bound::<Base>(py)
                .unwrap()
                .clone()
                .unbind()
        });
    } else {
        panic!("unsupported type")
    }
}

macro_rules! define_binop {
    ($name:ident, $op:ident) => {
        #[pyfunction]
        #[allow(non_snake_case)]
        pub fn $name(
            py: Python,
            a: Bound<PyAny>,
            b: Bound<PyAny>,
        ) -> Result<Py<Base>, ClaripyError> {
            if let Ok(a_bool) = a.clone().into_any().downcast::<Bool>() {
                if let Ok(b_bool) = b.clone().into_any().downcast::<Bool>() {
                    return Bool::new(
                        py,
                        &GLOBAL_CONTEXT.$op(&a_bool.get().inner, &b_bool.get().inner)?,
                    )
                    .map(|b| {
                        b.into_any()
                            .downcast_bound::<Base>(py)
                            .unwrap()
                            .clone()
                            .unbind()
                    });
                } else {
                    panic!("mismatched types")
                }
            } else if let Ok(a_bv) = a.clone().into_any().extract::<CoerceBV>() {
                if let Ok(b_bv) = b.clone().into_any().extract::<CoerceBV>() {
                    let (a_bv, b_bv) = CoerceBV::extract_pair(py, &a_bv, &b_bv)?;
                    return BV::new(
                        py,
                        &GLOBAL_CONTEXT.$op(&a_bv.get().inner, &b_bv.get().inner)?,
                    )
                    .map(|b| {
                        b.into_any()
                            .downcast_bound::<Base>(py)
                            .unwrap()
                            .clone()
                            .unbind()
                    });
                } else {
                    panic!("mismatched types")
                }
            } else {
                panic!("unsupported type")
            }
        }
    };
}

define_binop!(and_inner, and);
define_binop!(or_inner, or);
define_binop!(xor, xor);

// The following ops are reducable and support a variable number of arguments

#[pyfunction(name = "And", signature = (*args))]
pub fn and(py: Python, args: Vec<Bound<PyAny>>) -> Result<Py<Base>, ClaripyError> {
    let mut args = args.into_iter();
    let first = args.next().ok_or(ClaripyError::MissingArgIndex(0))?;
    Ok(args
        .try_fold(first, |acc, arg| {
            and_inner(py, acc, arg).map(|b| b.into_any().bind(py).clone())
        })?
        .downcast_into::<Base>()?
        .unbind())
}

#[pyfunction(name = "Or", signature = (*args))]
pub fn or(py: Python, args: Vec<Bound<PyAny>>) -> Result<Py<Base>, ClaripyError> {
    let mut args = args.into_iter();
    let first = args.next().ok_or(ClaripyError::MissingArgIndex(0))?;
    Ok(args
        .try_fold(first, |acc, arg| {
            or_inner(py, acc, arg).map(|b| b.into_any().bind(py).clone())
        })?
        .downcast_into::<Base>()?
        .unbind())
}

#[pyfunction(name = "If")]
pub fn r#if(
    py: Python,
    cond: Bound<Bool>,
    then_: Bound<PyAny>,
    else_: Bound<PyAny>,
) -> Result<Py<Base>, ClaripyError> {
    if let Ok(then_bv) = then_.clone().into_any().extract::<CoerceBV>() {
        if let Ok(else_bv) = else_.clone().into_any().extract::<CoerceBV>() {
            let (then_bv, else_bv) = CoerceBV::extract_pair(py, &then_bv, &else_bv)?;
            BV::new(
                py,
                &GLOBAL_CONTEXT.if_(
                    &cond.get().inner,
                    &then_bv.get().inner,
                    &else_bv.get().inner,
                )?,
            )
            .map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("mismatched types")
        }
    } else if let Ok(then_bool) = then_.clone().into_any().downcast::<Bool>() {
        if let Ok(else_bv) = else_.clone().into_any().downcast::<Bool>() {
            let then_bv = then_bool.get().inner.clone();
            let else_bv = else_bv.get().inner.clone();
            Bool::new(
                py,
                &GLOBAL_CONTEXT.if_(&cond.get().inner, &then_bv, &else_bv)?,
            )
            .map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("mismatched types")
        }
    } else if let Ok(then_fp) = then_.clone().into_any().downcast::<FP>() {
        if let Ok(else_bv) = else_.clone().into_any().downcast::<FP>() {
            let then_bv = then_fp.get().inner.clone();
            let else_bv = else_bv.get().inner.clone();
            FP::new(
                py,
                &GLOBAL_CONTEXT.if_(&cond.get().inner, &then_bv, &else_bv)?,
            )
            .map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("mismatched types")
        }
    } else if let Ok(then_string) = then_.clone().into_any().downcast::<PyAstString>() {
        if let Ok(else_bv) = else_.clone().into_any().downcast::<PyAstString>() {
            let then_bv = then_string.get().inner.clone();
            let else_bv = else_bv.get().inner.clone();
            PyAstString::new(
                py,
                &GLOBAL_CONTEXT.if_(&cond.get().inner, &then_bv, &else_bv)?,
            )
            .map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("mismatched types")
        }
    } else {
        panic!("unsupported type")
    }
}

pub(crate) fn import(py: Python, m: &Bound<PyModule>) -> PyResult<()> {
    import_submodule(py, m, "clarirs.ast", "base", base::import)?;
    import_submodule(py, m, "clarirs.ast", "bits", bits::import)?;
    import_submodule(py, m, "clarirs.ast", "bool", bool::import)?;
    import_submodule(py, m, "clarirs.ast", "bv", bv::import)?;
    import_submodule(py, m, "clarirs.ast", "fp", fp::import)?;
    import_submodule(py, m, "clarirs.ast", "strings", string::import)?;

    m.add_class::<base::Base>()?;
    m.add_class::<bits::Bits>()?;
    m.add_class::<bool::Bool>()?;
    m.add_class::<bv::BV>()?;
    m.add_class::<fp::FP>()?;
    m.add_class::<string::PyAstString>()?;
    m.add_function(wrap_pyfunction!(bool::true_op, m)?)?;
    m.add_function(wrap_pyfunction!(bool::false_op, m)?)?;
    Ok(())
}
