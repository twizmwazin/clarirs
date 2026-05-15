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
pub fn not<'py>(py: Python<'py>, b: Bound<'py, Base>) -> Result<Bound<'py, Base>, ClaripyError> {
    if let Ok(b_bool) = b.clone().into_any().cast::<Bool>() {
        return Bool::new(py, &GLOBAL_CONTEXT.not(&b_bool.get().inner)?)
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    } else if let Ok(b_bv) = b.clone().into_any().cast::<BV>() {
        return BV::new(py, &GLOBAL_CONTEXT.not(&b_bv.get().inner)?)
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    } else {
        panic!("unsupported type")
    }
}

#[pyfunction(name = "And", signature = (*args))]
pub fn and<'py>(
    py: Python<'py>,
    args: Vec<Bound<'py, PyAny>>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    // If all args are actually Bools (or Python bool literals) — not BVs
    // being coerced through the Bool path — use the Bool And. Otherwise fall
    // back to BV bitwise And.
    let all_bools = args
        .iter()
        .all(|arg| arg.cast::<Bool>().is_ok() || arg.extract::<bool>().is_ok());
    if all_bools {
        let bool_args = args
            .into_iter()
            .map(|arg| {
                arg.extract::<CoerceBool>()
                    .map(|b| b.0.get().inner.clone())
                    .map_err(|_| ClaripyError::TypeError("And arguments must be Bool".to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        return Bool::new(py, &GLOBAL_CONTEXT.and(bool_args)?)
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    }
    if args.len() == 2
        && let Some(lhs) = args[0].extract::<CoerceBV>().ok()
        && let Some(rhs) = args[1].extract::<CoerceBV>().ok()
    {
        let (lhs, rhs) = CoerceBV::unpack_pair(py, &lhs, &rhs)?;
        return BV::new(
            py,
            &GLOBAL_CONTEXT.bv_and(&lhs.get().inner, &rhs.get().inner)?,
        )
        .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    }
    Err(ClaripyError::TypeError(
        "And: expected Bools or exactly two BVs".to_string(),
    ))
}

#[pyfunction(name = "Or", signature = (*args))]
pub fn or<'py>(
    py: Python<'py>,
    args: Vec<Bound<'py, PyAny>>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    // Same policy as And: prefer the Bool path whenever every arg is a Bool.
    let all_bools = args
        .iter()
        .all(|arg| arg.cast::<Bool>().is_ok() || arg.extract::<bool>().is_ok());
    if all_bools {
        let bool_args = args
            .into_iter()
            .map(|arg| {
                arg.extract::<CoerceBool>()
                    .map(|b| b.0.get().inner.clone())
                    .map_err(|_| ClaripyError::TypeError("Or arguments must be Bool".to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        return Bool::new(py, &GLOBAL_CONTEXT.or(bool_args)?)
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    }
    if args.len() == 2
        && let Some(lhs) = args[0].extract::<CoerceBV>().ok()
        && let Some(rhs) = args[1].extract::<CoerceBV>().ok()
    {
        let (lhs, rhs) = CoerceBV::unpack_pair(py, &lhs, &rhs)?;
        return BV::new(
            py,
            &GLOBAL_CONTEXT.bv_or(&lhs.get().inner, &rhs.get().inner)?,
        )
        .map(|b| b.into_any().cast::<Base>().unwrap().clone());
    }
    Err(ClaripyError::TypeError(
        "Or: expected Bools or exactly two BVs".to_string(),
    ))
}

#[pyfunction]
#[allow(non_snake_case)]
pub fn xor<'py>(
    py: Python<'py>,
    a: Bound<'py, PyAny>,
    b: Bound<'py, PyAny>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    if let Ok(a_bool) = a.clone().into_any().cast::<Bool>() {
        if let Ok(b_bool) = b.clone().into_any().cast::<Bool>() {
            return Bool::new(
                py,
                &GLOBAL_CONTEXT.xor(&a_bool.get().inner, &b_bool.get().inner)?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
        } else {
            panic!("mismatched types")
        }
    } else if let Ok(a_bv) = a.clone().into_any().extract::<CoerceBV>() {
        if let Ok(b_bv) = b.clone().into_any().extract::<CoerceBV>() {
            let (a_bv, b_bv) = CoerceBV::unpack_pair(py, &a_bv, &b_bv)?;
            return BV::new(
                py,
                &GLOBAL_CONTEXT.bv_xor(&a_bv.get().inner, &b_bv.get().inner)?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone());
        } else {
            panic!("mismatched types")
        }
    } else {
        panic!("unsupported type")
    }
}

#[pyfunction(name = "If")]
pub fn r#if<'py>(
    py: Python<'py>,
    cond: CoerceBool,
    then_: Bound<'py, PyAny>,
    else_: Bound<'py, PyAny>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    // Classify each branch by its concrete AST type so we can dispatch on the
    // explicit sort, not on whichever coercion happens to match first.
    // `CoerceBV` and `CoerceBool` both silently accept the other's AST type,
    // which would otherwise mask a Bool/BV mismatch (and would route a
    // Bool/Bool `If` through the BV path, returning a 1-bit BV).
    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    enum Kind {
        Bool,
        BV,
        FP,
        String,
        Literal,
    }
    fn classify(val: &Bound<'_, PyAny>) -> Kind {
        if val.cast::<Bool>().is_ok() {
            Kind::Bool
        } else if val.cast::<BV>().is_ok() {
            Kind::BV
        } else if val.cast::<FP>().is_ok() {
            Kind::FP
        } else if val.cast::<PyAstString>().is_ok() {
            Kind::String
        } else {
            Kind::Literal
        }
    }

    let then_kind = classify(&then_);
    let else_kind = classify(&else_);
    let kind = match (then_kind, else_kind) {
        // Both literals: default to BV, matching prior behavior for raw ints.
        (Kind::Literal, Kind::Literal) => Kind::BV,
        (Kind::Literal, k) | (k, Kind::Literal) => k,
        (a, b) if a == b => a,
        _ => {
            return Err(ClaripyError::TypeError(format!(
                "Sort mismatch in if-then-else: {then_kind:?} and {else_kind:?}"
            )));
        }
    };

    match kind {
        Kind::Bool => {
            let then_bool = then_.extract::<CoerceBool>()?;
            let else_bool = else_.extract::<CoerceBool>()?;
            Bool::new(
                py,
                &GLOBAL_CONTEXT.ite(
                    &cond.0.get().inner,
                    &then_bool.0.get().inner,
                    &else_bool.0.get().inner,
                )?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone())
        }
        Kind::BV => {
            let then_bv = then_.extract::<CoerceBV>()?;
            let else_bv = else_.extract::<CoerceBV>()?;
            let (then_bv, else_bv) = CoerceBV::unpack_pair(py, &then_bv, &else_bv)?;
            BV::new(
                py,
                &GLOBAL_CONTEXT.ite(
                    &cond.0.get().inner,
                    &then_bv.get().inner,
                    &else_bv.get().inner,
                )?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone())
        }
        Kind::FP => {
            let then_fp = then_.extract::<CoerceFP>()?;
            let else_fp = else_.extract::<CoerceFP>()?;
            let (then_fp, else_fp) = CoerceFP::unpack_pair(py, &then_fp, &else_fp)?;
            FP::new(
                py,
                &GLOBAL_CONTEXT.ite(
                    &cond.0.get().inner,
                    &then_fp.get().inner,
                    &else_fp.get().inner,
                )?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone())
        }
        Kind::String => {
            let then_s = then_.extract::<CoerceString>()?;
            let else_s = else_.extract::<CoerceString>()?;
            PyAstString::new(
                py,
                &GLOBAL_CONTEXT.ite(
                    &cond.0.get().inner,
                    &then_s.0.get().inner,
                    &else_s.0.get().inner,
                )?,
            )
            .map(|b| b.into_any().cast::<Base>().unwrap().clone())
        }
        Kind::Literal => unreachable!(),
    }
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
    m.add_class::<string::PyAstString>()?;
    m.add_function(wrap_pyfunction!(bool::true_op, m)?)?;
    m.add_function(wrap_pyfunction!(bool::false_op, m)?)?;
    Ok(())
}
