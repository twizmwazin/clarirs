mod composite;
mod concrete;
mod hybrid;

pub use composite::CompositeSolver;
pub use concrete::ConcreteSolver;
pub use hybrid::HybridSolver;

use std::collections::BTreeSet;

use crate::prelude::*;

pub trait Solver<'c>: Clone + HasContext<'c> {
    // Constraint management
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError>;

    fn clear(&mut self) -> Result<(), ClarirsError>;

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError>;

    /// Simplify the constraints held internally by the solver
    fn simplify(&mut self) -> Result<(), ClarirsError>;

    /// Get all variables involved in the current set of constraints
    fn variables(&self) -> Result<BTreeSet<InternedString>, ClarirsError> {
        Ok(self
            .constraints()?
            .iter()
            .flat_map(|c| c.variables().clone())
            .collect())
    }

    /// Check if the current set of constraints is satisfiable
    fn satisfiable(&mut self) -> Result<bool, ClarirsError>;

    /// Evaluate an expression in the current model.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        let mut results = self.eval_bool_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let mut results = self.eval_bitvec_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        let mut results = self.eval_float_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        let mut results = self.eval_string_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Find multiple solutions for a boolean expression
    fn eval_bool_n(&mut self, expr: &BoolAst<'c>, n: u32)
    -> Result<Vec<BoolAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a bitvector expression
    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a float expression
    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a string expression
    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError>;
}
