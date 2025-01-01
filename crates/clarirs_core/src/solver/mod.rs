pub mod concrete;
#[cfg(test)]
mod tests;

use anyhow::Result;
use std::collections::HashMap;

use crate::prelude::*;

pub trait Model<'c> {
    /// Evaluate an expression in the current model. Eval replaces AST nodes with constraints
    /// from the model, and returns a simplified result.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval_bool(&self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError>;
    fn eval_bitvec(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;
    fn eval_float(&self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError>;
    fn eval_string(&self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError>;

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.eval_bool(expr).map(|v| v.is_true())
    }

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.eval_bool(expr).map(|v| v.is_false())
    }

    /// Get the minimum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn min(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let mut current_expr = expr.clone();
        let mut min_value = None;

        loop {
            match self.eval_bitvec(&current_expr) {
                Ok(value) => {
                    min_value = Some(value.clone());
                    let constraint = expr.context().ult(&value, expr)?;
                    current_expr = expr.context().if_(&constraint, &value, expr)?;
                }
                Err(ClarirsError::UnsatisfiableConstraints) => break,
                Err(e) => return Err(e),
            }
        }

        min_value.ok_or(ClarirsError::UnsatisfiableConstraints)
    }

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let mut current_expr = expr.clone();
        let mut max_value = None;

        loop {
            match self.eval_bitvec(&current_expr) {
                Ok(value) => {
                    max_value = Some(value.clone());
                    let constraint = expr.context().ugt(&value, expr)?;
                    current_expr = expr.context().if_(&constraint, &value, expr)?;
                }
                Err(ClarirsError::UnsatisfiableConstraints) => break,
                Err(e) => return Err(e),
            }
        }

        max_value.ok_or(ClarirsError::UnsatisfiableConstraints)
    }
}

pub trait Solver<'c>: Clone + HasContext<'c> {
    type Model: Model<'c>;

    // Constraint management
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError>;

    /// Check if the current set of constraints is satisfiable
    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        self.model().map(|_| true)
    }

    /// Get the model of the current set of constraints. Ideally, the Vec should be sorted
    /// from least to most significant variable.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn model(&mut self) -> Result<Self::Model, ClarirsError>;

    /// Evaluate an expression in the current model.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        self.model()?.eval_bool(expr)
    }
    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.model()?.eval_bitvec(expr)
    }
    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        self.model()?.eval_float(expr)
    }
    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        self.model()?.eval_string(expr)
    }

    /// Check if an expression is a solution to the current set of constraints.
    /// Implementors may want override this method for performance reasons.
    /// If the constraints are unsatisfiable, an error is returned.
    fn is_solution(
        &mut self,
        variable_values: &HashMap<String, AstRef<'c>>,
    ) -> Result<bool, ClarirsError> {
        for (var, value) in variable_values {
            let var_ast = self.context().bvs(var, value.size())?;
            let eq_constraint = self.context().eq_(&var_ast, value)?;
            self.add(&eq_constraint)?;
        }
        self.satisfiable()
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.model()?.is_true(expr)
    }

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.model()?.is_false(expr)
    }

    /// Get the minimum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.model()?.min(expr)
    }

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.model()?.max(expr)
    }
}
