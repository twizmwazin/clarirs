use std::collections::HashSet;

use crate::prelude::*;

pub trait Solver<'c>: Clone + HasContext<'c> {
    // Constraint management
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError>;

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError>;
    fn variables(&self) -> Result<HashSet<String>, ClarirsError> {
        Ok(self
            .constraints()?
            .iter()
            .flat_map(|c| c.variables())
            .cloned()
            .collect())
    }

    /// Check if the current set of constraints is satisfiable
    fn satisfiable(&mut self) -> Result<bool, ClarirsError>;

    /// Evaluate an expression in the current model.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError>;
    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;
    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError>;
    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError>;

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Get the minimum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model. If the constraints are
    /// unsatisfiable, an error is returned.
    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Find multiple solutions for a boolean expression
    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let mut results = Vec::new();
        let mut solver = self.clone();

        // Try to find up to n solutions
        for _ in 0..n {
            // Check if solver is still satisfiable
            if !solver.satisfiable()? {
                break; // No more solutions
            }

            // Get current solution
            let solution = solver.eval_bool(expr)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution for next iteration
            // Don't do this for concrete solvers which don't support constraints
            if let Ok(()) = solver.add(&solver.context().neq(expr, &solution)?) {
                // Successfully added constraint, continue to next iteration
            } else {
                // If we can't add constraints, we can only get one solution
                break;
            }
        }

        Ok(results)
    }

    /// Find multiple solutions for a bitvector expression
    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let mut results = Vec::new();
        let mut solver = self.clone();

        // Try to find up to n solutions
        for _ in 0..n {
            // Check if solver is still satisfiable
            if !solver.satisfiable()? {
                break; // No more solutions
            }

            // Get current solution
            let solution = solver.eval_bitvec(expr)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution for next iteration
            // Don't do this for concrete solvers which don't support constraints
            if let Ok(()) = solver.add(&solver.context().neq(expr, &solution)?) {
                // Successfully added constraint, continue to next iteration
            } else {
                // If we can't add constraints, we can only get one solution
                break;
            }
        }

        Ok(results)
    }

    /// Find multiple solutions for a float expression
    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let mut results = Vec::new();
        let mut solver = self.clone();

        // Try to find up to n solutions
        for _ in 0..n {
            // Check if solver is still satisfiable
            if !solver.satisfiable()? {
                break; // No more solutions
            }

            // Get current solution
            let solution = solver.eval_float(expr)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution for next iteration
            // Don't do this for concrete solvers which don't support constraints
            if let Ok(()) = solver.add(&solver.context().neq(expr, &solution)?) {
                // Successfully added constraint, continue to next iteration
            } else {
                // If we can't add constraints, we can only get one solution
                break;
            }
        }

        Ok(results)
    }

    /// Find multiple solutions for a string expression
    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let mut results = Vec::new();
        let mut solver = self.clone();

        // Try to find up to n solutions
        for _ in 0..n {
            // Check if solver is still satisfiable
            if !solver.satisfiable()? {
                break; // No more solutions
            }

            // Get current solution
            let solution = solver.eval_string(expr)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution for next iteration
            // Don't do this for concrete solvers which don't support constraints
            if let Ok(()) = solver.add(&solver.context().neq(expr, &solution)?) {
                // Successfully added constraint, continue to next iteration
            } else {
                // If we can't add constraints, we can only get one solution
                break;
            }
        }

        Ok(results)
    }
}

/// A concrete solver. This solver is used to evaluate expressions in a concrete
/// context. It does not support adding constraints. It is a glorified
/// simplifier.
#[derive(Clone)]
pub struct ConcreteSolver<'c> {
    ctx: &'c Context<'c>,
}

impl<'c> HasContext<'c> for ConcreteSolver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> ConcreteSolver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self { ctx }
    }
}

impl<'c> Solver<'c> for ConcreteSolver<'c> {
    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(Vec::new())
    }

    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify()
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify()
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify()
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify()
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_true())
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_false())
    }

    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }

    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;

    use super::*;

    #[test]
    fn test_concrete_solver() -> Result<(), ClarirsError> {
        let context = Context::new();
        let mut solver = ConcreteSolver::new(&context);

        // Bool tests
        solver.eval_bool(&context.true_()?)?;
        solver.eval_bool(&context.false_()?)?;
        assert!(solver.eval_bool(&context.bools("test")?).is_err());

        // BV tests
        assert!(
            solver.eval_bitvec(&context.add(&context.bvv_prim(1u8)?, &context.bvv_prim(1u8)?)?)?
                == context.bvv_prim(2u8)?
        );
        assert!(solver.eval_bitvec(&context.bvs("test", 8)?).is_err());

        Ok(())
    }
}
