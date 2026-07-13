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
    fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError>;

    fn clear(&mut self) -> Result<(), ClarirsError>;

    fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError>;

    /// Simplify the constraints held internally by the solver
    fn simplify(&mut self) -> Result<(), ClarirsError>;

    /// Get all variables involved in the current set of constraints
    fn variables(&self) -> Result<BTreeSet<InternedString>, ClarirsError> {
        Ok(self
            .constraints()?
            .iter()
            .flat_map(|c| c.variables())
            .cloned()
            .collect())
    }

    /// Check if the current set of constraints is satisfiable
    fn satisfiable(&mut self) -> Result<bool, ClarirsError>;

    /// Check satisfiability with `extra` constraints temporarily added.
    /// The default clones the solver and adds the constraints; backends
    /// override this with cheaper scoped checks (e.g. Z3 assumptions on the
    /// persistent incremental solver). This is the hot path of symbolic
    /// execution: every branch feasibility check goes through it.
    fn satisfiable_with_extra(&mut self, extra: &[AstRef<'c>]) -> Result<bool, ClarirsError> {
        if extra.is_empty() {
            return self.satisfiable();
        }
        let mut solver = self.clone();
        for constraint in extra {
            solver.add(constraint)?;
        }
        solver.satisfiable()
    }

    /// Evaluate an expression in the current model. The result has the same
    /// sort as the input expression.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        let mut results = self.eval_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }

    /// Evaluate several expressions against a single, shared model, returning
    /// one value per input expression in order.
    ///
    /// Unlike calling [`Solver::eval`] in a loop, every value is drawn from the
    /// same satisfying assignment, so the results are mutually consistent. This
    /// is what makes the values usable as a *model*. Returns
    /// [`ClarirsError::Unsat`] if the constraints are unsatisfiable.
    ///
    /// The default implementation evaluates each expression independently,
    /// which is only consistent for solvers that admit a single model (e.g.
    /// [`ConcreteSolver`]). Only a backend that admits multiple models and can
    /// produce one (e.g. Z3) needs to override this; mixins inherit the default
    /// and need not forward it, since model extraction asks the backend
    /// directly. Callers that rely on consistency (e.g. the model cache)
    /// nonetheless verify a returned assignment before trusting it.
    fn batch_eval(&mut self, exprs: &[AstRef<'c>]) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        exprs.iter().map(|expr| self.eval(expr)).collect()
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError>;

    /// Find up to `n` solutions for an expression. The results have the same
    /// sort as the input expression.
    fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError>;
}

/// Test-only fake solvers shared by the solver and solver-mixin unit tests.
#[cfg(test)]
pub(crate) mod test_support {
    use std::collections::HashMap;

    use crate::prelude::*;

    /// A minimal constraint-storing solver used to exercise solver
    /// combinators (composite, hybrid, mixins) without a real backend.
    ///
    /// It builds a naive model from `var == <concrete>` equalities among its
    /// constraints (the first equality for a variable wins) and decides every
    /// query by substituting that model and simplifying. A constraint that
    /// simplifies to false under the model makes the solver unsatisfiable.
    #[derive(Clone, Debug)]
    pub(crate) struct EqModelSolver<'c> {
        ctx: &'c Context<'c>,
        constraints: Vec<AstRef<'c>>,
    }

    impl<'c> EqModelSolver<'c> {
        pub(crate) fn new(ctx: &'c Context<'c>) -> Self {
            Self {
                ctx,
                constraints: Vec::new(),
            }
        }

        fn model(&self) -> HashMap<u64, AstRef<'c>> {
            let mut model: HashMap<u64, AstRef<'c>> = HashMap::new();
            for c in &self.constraints {
                if let AstOp::Eq(lhs, rhs) = c.op() {
                    if lhs.symbolic() && rhs.concrete() {
                        model.entry(lhs.hash()).or_insert_with(|| rhs.clone());
                    } else if rhs.symbolic() && lhs.concrete() {
                        model.entry(rhs.hash()).or_insert_with(|| lhs.clone());
                    }
                }
            }
            model
        }

        fn resolve(&self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            expr.replace_many(&self.model())?.simplify()
        }
    }

    impl<'c> HasContext<'c> for EqModelSolver<'c> {
        fn context(&self) -> &'c Context<'c> {
            self.ctx
        }
    }

    impl<'c> Solver<'c> for EqModelSolver<'c> {
        fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
            self.constraints.push(constraint.clone());
            Ok(())
        }

        fn clear(&mut self) -> Result<(), ClarirsError> {
            self.constraints.clear();
            Ok(())
        }

        fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
            Ok(self.constraints.clone())
        }

        fn simplify(&mut self) -> Result<(), ClarirsError> {
            Ok(())
        }

        fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
            for c in &self.constraints {
                if self.resolve(c)?.is_false() {
                    return Ok(false);
                }
            }
            Ok(true)
        }

        fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(self.resolve(expr)?.is_true())
        }

        fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(self.resolve(expr)?.is_false())
        }

        fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.is_true(expr)
        }

        fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.is_false(expr)
        }

        fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.eval(expr)
        }

        fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.eval(expr)
        }

        fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.eval(expr)
        }

        fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.eval(expr)
        }

        fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
            if n == 0 {
                return Ok(Vec::new());
            }
            if !self.satisfiable()? {
                return Err(ClarirsError::Unsat);
            }
            let resolved = self.resolve(expr)?;
            if resolved.concrete() {
                Ok(vec![resolved])
            } else {
                Err(ClarirsError::UnsupportedOperation(
                    "EqModelSolver cannot enumerate unconstrained expressions".to_string(),
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::EqModelSolver;
    use crate::ast::AstFactory;
    use crate::prelude::*;

    /// A solver whose `eval_n` finds no solutions, used to exercise the
    /// default `eval` implementation's empty-result handling.
    #[derive(Clone, Debug)]
    struct NoSolutionSolver<'c> {
        ctx: &'c Context<'c>,
    }

    impl<'c> HasContext<'c> for NoSolutionSolver<'c> {
        fn context(&self) -> &'c Context<'c> {
            self.ctx
        }
    }

    impl<'c> Solver<'c> for NoSolutionSolver<'c> {
        fn add(&mut self, _: &AstRef<'c>) -> Result<(), ClarirsError> {
            Ok(())
        }
        fn clear(&mut self) -> Result<(), ClarirsError> {
            Ok(())
        }
        fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
            Ok(Vec::new())
        }
        fn simplify(&mut self) -> Result<(), ClarirsError> {
            Ok(())
        }
        fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
            Ok(false)
        }
        fn is_true(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(false)
        }
        fn is_false(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(false)
        }
        fn has_true(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(false)
        }
        fn has_false(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            Ok(false)
        }
        fn min_unsigned(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            Err(ClarirsError::Unsat)
        }
        fn max_unsigned(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            Err(ClarirsError::Unsat)
        }
        fn min_signed(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            Err(ClarirsError::Unsat)
        }
        fn max_signed(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            Err(ClarirsError::Unsat)
        }
        fn eval_n(&mut self, _: &AstRef<'c>, _: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
            Ok(Vec::new())
        }
    }

    #[test]
    fn test_default_variables_collects_from_constraints() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = EqModelSolver::new(&ctx);

        let x = ctx.bvs("x", 8)?;
        let y = ctx.bvs("y", 8)?;
        solver.add(&ctx.eq_(&x, &ctx.bvv(BitVec::from((1, 8)))?)?)?;
        solver.add(&ctx.eq_(&y, &ctx.bvv(BitVec::from((2, 8)))?)?)?;
        // A concrete constraint contributes no variables.
        solver.add(&ctx.true_()?)?;

        let variables = solver.variables()?;
        let vars: Vec<&str> = variables.iter().map(|v| v.as_str()).collect();
        assert_eq!(vars, vec!["x", "y"]);
        Ok(())
    }

    #[test]
    fn test_default_variables_empty_without_constraints() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let solver = EqModelSolver::new(&ctx);
        assert!(solver.variables()?.is_empty());
        Ok(())
    }

    #[test]
    fn test_default_satisfiable_with_extra() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = EqModelSolver::new(&ctx);

        let x = ctx.bvs("x", 8)?;
        let one = ctx.bvv(BitVec::from((1, 8)))?;
        let two = ctx.bvv(BitVec::from((2, 8)))?;
        solver.add(&ctx.eq_(&x, &one)?)?;

        // Empty extras delegate to plain satisfiable().
        assert!(solver.satisfiable_with_extra(&[])?);
        // Consistent extra: still satisfiable.
        assert!(solver.satisfiable_with_extra(&[ctx.eq_(&x, &one)?])?);
        // Contradictory extra: unsatisfiable.
        assert!(!solver.satisfiable_with_extra(&[ctx.eq_(&x, &two)?])?);

        // The default implementation works on a clone; the original solver is
        // unchanged and still satisfiable.
        assert_eq!(solver.constraints()?.len(), 1);
        assert!(solver.satisfiable()?);
        Ok(())
    }

    #[test]
    fn test_default_eval_takes_first_solution() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = EqModelSolver::new(&ctx);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv(BitVec::from((5, 8)))?;
        solver.add(&ctx.eq_(&x, &five)?)?;

        assert_eq!(solver.eval(&x)?, five);
        Ok(())
    }

    #[test]
    fn test_default_eval_maps_empty_solutions_to_unsat() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = NoSolutionSolver { ctx: &ctx };
        let x = ctx.bvs("x", 8)?;
        assert!(matches!(solver.eval(&x), Err(ClarirsError::Unsat)));
        Ok(())
    }

    #[test]
    fn test_default_batch_eval_evaluates_each_expression() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = EqModelSolver::new(&ctx);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv(BitVec::from((5, 8)))?;
        solver.add(&ctx.eq_(&x, &five)?)?;

        let one = ctx.bvv(BitVec::from((1, 8)))?;
        let results = solver.batch_eval(&[
            x.clone(),
            ctx.add(&x, &one)?,
            ctx.bvv(BitVec::from((2, 8)))?,
        ])?;
        assert_eq!(
            results,
            vec![
                five,
                ctx.bvv(BitVec::from((6, 8)))?,
                ctx.bvv(BitVec::from((2, 8)))?
            ]
        );
        Ok(())
    }

    #[test]
    fn test_default_batch_eval_empty_input() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = EqModelSolver::new(&ctx);
        assert!(solver.batch_eval(&[])?.is_empty());
        Ok(())
    }
}
