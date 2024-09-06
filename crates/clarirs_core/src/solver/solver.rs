use anyhow::Result;

use crate::prelude::*;

pub trait Model<'c> {
    /// Evaluate an expression in the current model. Eval replaces AST nodes with constraints
    /// from the model, and returns a simplified result.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval(&self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.batch_eval(std::iter::once(expr.clone()), 1)
            .map(|mut v| v.pop().unwrap())
    }

    /// Evaluate multiple expressions in the current model. Multiple solutions are returned if
    /// available. If the constraints are unsatisfiable, an error is returned.
    fn batch_eval<I>(&self, exprs: I, max_solutions: u32) -> Result<Vec<AstRef<'c>>, ClarirsError>
    where
        I: IntoIterator<Item = AstRef<'c>>;

    /// Check if an expression is a solution to the current set of constraints.
    /// Implementors may want override this method for performance reasons.
    /// If the constraints are unsatisfiable, an error is returned.
    fn is_solution(&self, expr: &AstRef<'c>, value: &AstRef<'c>) -> Result<bool, ClarirsError> {
        todo!()
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.eval(expr).map(|v| v.is_true())
    }

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.eval(expr).map(|v| v.is_false())
    }

    /// Get the minimum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn min(&self, expr: AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        todo!()
    }

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&self, expr: AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        todo!()
    }
}

pub trait Solver<'c, 's>: Clone + HasContext<'c>
where
    'c: 's,
{
    type Model: Model<'c>;

    // Constraint management
    fn add(&'s mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError>;

    /// Check if the current set of constraints is satisfiable
    fn satisfiable(&'s mut self) -> Result<bool, ClarirsError> {
        self.model().map(|_| true)
    }

    /// Get the model of the current set of constraints. Ideally, the Vec should be sorted
    /// from least to most significant variable.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn model(&'s mut self) -> Result<Self::Model, ClarirsError>;

    /// Evaluate an expression in the current model.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval(&'s mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.model()?.eval(expr)
    }

    /// Evaluate multiple expressions in the current model. Multiple solutions are returned if
    /// available. If the constraints are unsatisfiable, an error is returned.
    fn batch_eval<I>(
        &'s mut self,
        exprs: I,
        max_solutions: u32,
    ) -> Result<Vec<AstRef<'c>>, ClarirsError>
    where
        I: IntoIterator<Item = AstRef<'c>>,
    {
        self.model()?.batch_eval(exprs, max_solutions)
    }

    /// Check if an expression is a solution to the current set of constraints.
    /// Implementors may want override this method for performance reasons.
    /// If the constraints are unsatisfiable, an error is returned.
    fn is_solution(
        &'s mut self,
        expr: &AstRef<'c>,
        value: &AstRef<'c>,
    ) -> Result<bool, ClarirsError> {
        self.model()?.is_solution(expr, value)
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&'s mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.model()?.is_true(expr)
    }

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&'s mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.model()?.is_false(expr)
    }

    /// Get the minimum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn min(&'s mut self, expr: AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.model()?.min(expr)
    }

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&'s mut self, expr: AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.model()?.max(expr)
    }
}
