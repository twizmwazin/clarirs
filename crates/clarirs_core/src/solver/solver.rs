use anyhow::Result;

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
        todo!()
    }

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!()
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

    // TODO: This was implemented incorrectly. This method needs to take a map
    // of variables to values, and return a boolean indicating if the values
    // are a solution to the current set of constraints.
    //
    // A lazy implementation would be to add the constraints to the solver
    // and check if the constraints are satisfiable. This is not ideal for
    // performance reasons, though a decent solver should efficiently handle
    // this case.

    /// Check if an expression is a solution to the current set of constraints.
    /// Implementors may want override this method for performance reasons.
    /// If the constraints are unsatisfiable, an error is returned.
    // fn is_solution(
    //     &mut self,
    //     expr: &AstRef<'c>,
    //     value: &AstRef<'c>,
    // ) -> Result<bool, ClarirsError> {
    //     todo!()
    // }

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
