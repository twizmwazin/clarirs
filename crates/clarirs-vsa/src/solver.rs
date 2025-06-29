use clarirs_core::{ast::bitvec::BitVecOpExt, prelude::*};

use crate::{Normalize, reduce::Reduce, strided_interval::ComparisonResult};

/// A solver that uses Value Set Analysis (VSA) for symbolic computation
#[derive(Clone, Debug)]
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
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        expr.simplify()?
            .normalize()?
            .reduce()
            .and_then(|comp_result| match comp_result {
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
            })
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        expr.simplify()?.normalize()?.reduce().and_then(|si| {
            if si.is_empty() {
                return Ok(vec![]);
            }
            si.eval(n)
                .into_iter()
                .map(|bv| self.context().bvv_from_biguint_with_size(&bv, expr.size()))
                .collect()
        })
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
        Ok(matches!(
            expr.simplify()?.normalize()?.reduce()?,
            ComparisonResult::True
        ))
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.normalize()?.reduce()?,
            ComparisonResult::False
        ))
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.normalize()?.reduce()?,
            ComparisonResult::True | ComparisonResult::Maybe
        ))
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.normalize()?.reduce()?,
            ComparisonResult::False | ComparisonResult::Maybe
        ))
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        expr.simplify()?.normalize()?.reduce().and_then(|si| {
            expr.context()
                .bvv_from_biguint_with_size(&si.lower_bound, expr.size())
        })
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        expr.simplify()?.normalize()?.reduce().and_then(|si| {
            expr.context()
                .bvv_from_biguint_with_size(&si.upper_bound, expr.size())
        })
    }

    fn min_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement min_signed for VSASolver")
    }

    fn max_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement max_signed for VSASolver")
    }
}
