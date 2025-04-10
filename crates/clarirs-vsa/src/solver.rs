use clarirs_core::{ast::bitvec::BitVecOpExt, prelude::*};

use crate::{
    Normalize,
    reduce::{Reduce, ReduceResult},
    strided_interval::ComparisonResult,
};

/// A solver that uses Value Set Analysis (VSA) for symbolic computation
#[derive(Clone)]
pub struct VSASolver<'c> {
    ctx: &'c Context<'c>,
}

impl<'c> VSASolver<'c> {
    /// Create a new VSA solver
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self { ctx }
    }
}

impl<'c> HasContext<'c> for VSASolver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Solver<'c> for VSASolver<'c> {
    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(vec![])
    }

    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Adding constraints is not supported in VSASolver".to_string(),
        ))
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        if let ReduceResult::Bool(comp_result) = expr.simplify()?.normalize()?.reduce()? {
            match comp_result {
                ComparisonResult::True => Ok(vec![self.context().boolv(true)?]),
                ComparisonResult::False => Ok(vec![self.context().boolv(false)?]),
                ComparisonResult::Maybe => match n {
                    0 => Ok(vec![]),
                    1 => Ok(vec![self.context().boolv(true)?]),
                    _ => Ok(vec![
                        self.context().boolv(true)?,
                        self.context().boolv(false)?,
                    ]),
                },
            }
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected Bool expression".to_string(),
            ))
        }
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        if let ReduceResult::BitVec(si) = expr.simplify()?.normalize()?.reduce()? {
            if si.is_empty() {
                return Ok(vec![]);
            }
            si.eval(n)
                .into_iter()
                .map(|bv| self.context().bvv_from_biguint_with_size(&bv, expr.size()))
                .collect()
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected BitVec expression".to_string(),
            ))
        }
    }

    fn eval_float_n(
        &mut self,
        _expr: &FloatAst<'c>,
        _n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Floating-point evaluation is not supported in VSASolver".to_string(),
        ))
    }

    fn eval_string_n(
        &mut self,
        _expr: &StringAst<'c>,
        _n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "String evaluation is not supported in VSASolver".to_string(),
        ))
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let reduced = expr.simplify()?.normalize()?.reduce()?;
        if let crate::reduce::ReduceResult::Bool(comp_result) = reduced {
            Ok(comp_result == crate::strided_interval::ComparisonResult::True)
        } else {
            Ok(false)
        }
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let reduced = expr.simplify()?.normalize()?.reduce()?;
        if let crate::reduce::ReduceResult::Bool(comp_result) = reduced {
            Ok(comp_result == crate::strided_interval::ComparisonResult::False)
        } else {
            Ok(false)
        }
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let reduced = expr.simplify()?.normalize()?.reduce()?;
        if let crate::reduce::ReduceResult::Bool(comp_result) = reduced {
            Ok(matches!(
                comp_result,
                crate::strided_interval::ComparisonResult::True
                    | crate::strided_interval::ComparisonResult::Maybe
            ))
        } else {
            Ok(false)
        }
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let reduced = expr.simplify()?.normalize()?.reduce()?;
        if let crate::reduce::ReduceResult::Bool(comp_result) = reduced {
            Ok(matches!(
                comp_result,
                crate::strided_interval::ComparisonResult::False
                    | crate::strided_interval::ComparisonResult::Maybe
            ))
        } else {
            Ok(false)
        }
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if let ReduceResult::BitVec(si) = expr.simplify()?.normalize()?.reduce()? {
            self.context()
                .bvv_from_biguint_with_size(&si.lower_bound, expr.size())
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected BitVec expression".to_string(),
            ))
        }
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if let ReduceResult::BitVec(si) = expr.simplify()?.normalize()?.reduce()? {
            self.context()
                .bvv_from_biguint_with_size(&si.upper_bound, expr.size())
        } else {
            Err(ClarirsError::InvalidArgumentsWithMessage(
                "Expected BitVec expression".to_string(),
            ))
        }
    }

    fn min_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement min_signed for VSASolver")
    }

    fn max_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement max_signed for VSASolver")
    }
}
