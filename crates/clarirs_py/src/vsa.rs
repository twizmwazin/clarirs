#![allow(non_snake_case)]

use clarirs_vsa::StridedInterval;
use clarirs_vsa::reduce::{Reduce, ReduceResult};
use clarirs_vsa::strided_interval::ComparisonResult;
use num_bigint::{BigInt, BigUint};

use crate::prelude::*;

/// Reduce an AST expression using VSA abstract interpretation.
///
/// For Bool expressions: returns `true` if definitely true, `false` if definitely
/// false, or a symbolic `BoolS("maybe")` if the result is indeterminate.
///
/// For BV expressions: returns a concrete BVV if the strided interval resolves to
/// a single value, an SI (strided interval annotated BV) if it resolves to a range,
/// or the original expression if the interval is empty.
#[pyfunction]
pub fn reduce<'py>(
    py: Python<'py>,
    expr: Bound<'py, Base>,
) -> Result<Bound<'py, Base>, ClaripyError> {
    if let Ok(bool_expr) = expr.clone().into_any().cast::<Bool>() {
        let reduced = bool_expr.get().inner.reduce()?;
        let result = match reduced {
            ReduceResult::Bool(ComparisonResult::True) => Bool::new(py, &GLOBAL_CONTEXT.true_()?)?,
            ReduceResult::Bool(ComparisonResult::False) => Bool::new(py, &GLOBAL_CONTEXT.false_()?)?,
            ReduceResult::Bool(ComparisonResult::Maybe) => {
                use crate::ast::bool::BoolS;
                BoolS(py, "maybe", false)?
            }
            _ => return Err(ClaripyError::TypeError("Expected Bool reduce result".to_string())),
        };
        return Ok(result.into_any().cast::<Base>()?.clone());
    }

    if let Ok(bv_expr) = expr.clone().into_any().cast::<BV>() {
        let reduced = bv_expr.get().inner.reduce()?;
        let result = match reduced {
            ReduceResult::BitVec(StridedInterval::Empty { .. }) => bv_expr.clone(),
            ReduceResult::BitVec(StridedInterval::Normal {
                bits,
                stride,
                lower_bound,
                upper_bound,
            }) => {
                if lower_bound == upper_bound {
                    BV::new(
                        py,
                        &GLOBAL_CONTEXT.bvv_from_biguint_with_size(&lower_bound, bits)?,
                    )?
                } else {
                    BV::new(
                        py,
                        &GLOBAL_CONTEXT.si(bits, stride, lower_bound, upper_bound)?,
                    )?
                }
            }
            _ => return Err(ClaripyError::TypeError("Expected BitVec reduce result".to_string())),
        };
        return Ok(result.into_any().cast::<Base>()?.clone());
    }

    Err(ClaripyError::TypeError(
        "reduce: expression must be a Bool or BV".to_string(),
    ))
}

/// Check if a Bool expression is definitely true via VSA.
#[pyfunction]
pub fn is_true(expr: Bound<'_, Bool>) -> Result<bool, ClaripyError> {
    Ok(matches!(
        expr.get().inner.simplify()?.reduce()?,
        ReduceResult::Bool(ComparisonResult::True)
    ))
}

/// Check if a Bool expression is definitely false via VSA.
#[pyfunction]
pub fn is_false(expr: Bound<'_, Bool>) -> Result<bool, ClaripyError> {
    Ok(matches!(
        expr.get().inner.simplify()?.reduce()?,
        ReduceResult::Bool(ComparisonResult::False)
    ))
}

/// Check if a Bool expression could possibly be true via VSA.
#[pyfunction]
pub fn has_true(expr: Bound<'_, Bool>) -> Result<bool, ClaripyError> {
    Ok(matches!(
        expr.get().inner.simplify()?.reduce()?,
        ReduceResult::Bool(ComparisonResult::True) | ReduceResult::Bool(ComparisonResult::Maybe)
    ))
}

/// Check if a Bool expression could possibly be false via VSA.
#[pyfunction]
pub fn has_false(expr: Bound<'_, Bool>) -> Result<bool, ClaripyError> {
    Ok(matches!(
        expr.get().inner.simplify()?.reduce()?,
        ReduceResult::Bool(ComparisonResult::False) | ReduceResult::Bool(ComparisonResult::Maybe)
    ))
}

/// Get the minimum unsigned value of a BV expression via VSA.
#[pyfunction]
#[pyo3(signature = (expr, signed = false))]
pub fn min(expr: Bound<'_, BV>, signed: bool) -> Result<BigInt, ClaripyError> {
    let reduced = expr.get().inner.simplify()?.reduce()?;
    let si = match reduced {
        ReduceResult::BitVec(si) => si,
        _ => return Err(ClaripyError::TypeError("Expected BitVec reduce result".to_string())),
    };
    if signed {
        let (min_bound, _) = si.get_signed_bounds();
        Ok(min_bound)
    } else {
        let (min_bound, _) = si.get_unsigned_bounds();
        Ok(BigInt::from(min_bound))
    }
}

/// Get the maximum unsigned value of a BV expression via VSA.
#[pyfunction]
#[pyo3(signature = (expr, signed = false))]
pub fn max(expr: Bound<'_, BV>, signed: bool) -> Result<BigInt, ClaripyError> {
    let reduced = expr.get().inner.simplify()?.reduce()?;
    let si = match reduced {
        ReduceResult::BitVec(si) => si,
        _ => return Err(ClaripyError::TypeError("Expected BitVec reduce result".to_string())),
    };
    if signed {
        let (_, max_bound) = si.get_signed_bounds();
        Ok(max_bound)
    } else {
        let (_, max_bound) = si.get_unsigned_bounds();
        Ok(BigInt::from(max_bound))
    }
}

/// Evaluate a BV expression via VSA, returning up to `n` concrete values as Python ints.
#[pyfunction]
pub fn eval<'py>(expr: Bound<'py, BV>, n: u32) -> Result<Vec<BigUint>, ClaripyError> {
    let reduced = expr.get().inner.simplify()?.reduce()?;
    let si = match reduced {
        ReduceResult::BitVec(si) => si,
        _ => return Err(ClaripyError::TypeError("Expected BitVec reduce result".to_string())),
    };
    Ok(si.eval(n))
}

/// Get the cardinality (number of possible concrete values) of a BV expression via VSA.
#[pyfunction]
pub fn cardinality(expr: Bound<'_, BV>) -> Result<num_bigint::BigUint, ClaripyError> {
    let reduced = expr.get().inner.simplify()?.reduce()?;
    let si = match reduced {
        ReduceResult::BitVec(si) => si,
        _ => return Err(ClaripyError::TypeError("Expected BitVec reduce result".to_string())),
    };
    Ok(si.cardinality())
}

/// Check if two AST expressions are identical after VSA reduction.
///
/// Both expressions are reduced and then compared for equality.
#[pyfunction]
pub fn identical(a: Bound<'_, Base>, b: Bound<'_, Base>) -> Result<bool, ClaripyError> {
    // Try as BV first
    if let Ok(a_bv) = a.clone().into_any().cast::<BV>()
        && let Ok(b_bv) = b.clone().into_any().cast::<BV>()
    {
        let reduced_a = a_bv.get().inner.reduce()?;
        let reduced_b = b_bv.get().inner.reduce()?;
        return match (reduced_a, reduced_b) {
            (ReduceResult::BitVec(a_si), ReduceResult::BitVec(b_si)) => Ok(a_si == b_si),
            _ => Ok(false),
        };
    }

    // Try as Bool
    if let Ok(a_bool) = a.clone().into_any().cast::<Bool>()
        && let Ok(b_bool) = b.clone().into_any().cast::<Bool>()
    {
        let reduced_a = a_bool.get().inner.reduce()?;
        let reduced_b = b_bool.get().inner.reduce()?;
        return match (reduced_a, reduced_b) {
            (ReduceResult::Bool(a_cr), ReduceResult::Bool(b_cr)) => Ok(a_cr == b_cr),
            _ => Ok(false),
        };
    }

    Err(ClaripyError::TypeError(
        "identical: both arguments must be the same type (Bool or BV)".to_string(),
    ))
}

pub(crate) fn import(_py: Python, m: &Bound<PyModule>) -> PyResult<()> {
    add_pyfunctions!(
        m,
        reduce,
        is_true,
        is_false,
        has_true,
        has_false,
        min,
        max,
        eval,
        cardinality,
        identical,
    );
    Ok(())
}
