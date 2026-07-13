use crate::prelude::*;

/// A concrete solver. This solver is used to evaluate expressions in a concrete
/// context. It does not support adding constraints. It is a glorified
/// simplifier.
#[derive(Clone, Debug)]
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
        // ConcreteSolver has no constraints to simplify
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_true())
    }

    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_false())
    }

    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_true())
    }

    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_false())
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
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        Ok(vec![expr.simplify_ext(false, true)?])
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;
    use crate::prelude::*;

    #[test]
    fn test_concrete_solver() -> Result<(), ClarirsError> {
        let context = Context::new();
        let mut solver = ConcreteSolver::new(&context);

        // Bool tests
        solver.eval(&context.true_()?)?;
        solver.eval(&context.false_()?)?;
        assert!(solver.eval(&context.bools("test")?).is_err());

        // BV tests
        assert!(
            solver.eval(&context.add(
                &context.bvv(BitVec::from((1, 8)))?,
                &context.bvv(BitVec::from((1, 8)))?
            )?)? == context.bvv(BitVec::from((2, 8)))?
        );
        assert!(solver.eval(&context.bvs("test", 8)?).is_err());

        Ok(())
    }

    #[test]
    fn test_concrete_solver_constraint_management_is_noop() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = ConcreteSolver::new(&ctx);

        // add() accepts anything but stores nothing.
        let x = ctx.bools("x")?;
        solver.add(&x)?;
        solver.add(&ctx.false_()?)?;
        assert!(solver.constraints()?.is_empty());
        assert!(solver.variables()?.is_empty());

        // satisfiable() is always true, even after adding false.
        assert!(solver.satisfiable()?);

        // clear() and simplify() are no-ops that succeed.
        solver.clear()?;
        solver.simplify()?;
        assert!(solver.satisfiable()?);

        // HasContext returns the construction context.
        assert!(std::ptr::eq(solver.context(), &ctx));
        Ok(())
    }

    #[test]
    fn test_concrete_solver_truth_queries() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = ConcreteSolver::new(&ctx);

        // Expressions are simplified before the truth check.
        let tautology = ctx.or2(&ctx.true_()?, &ctx.false_()?)?;
        let contradiction = ctx.and2(&ctx.true_()?, &ctx.false_()?)?;

        assert!(solver.is_true(&tautology)?);
        assert!(!solver.is_false(&tautology)?);
        assert!(solver.has_true(&tautology)?);
        assert!(!solver.has_false(&tautology)?);

        assert!(!solver.is_true(&contradiction)?);
        assert!(solver.is_false(&contradiction)?);
        assert!(!solver.has_true(&contradiction)?);
        assert!(solver.has_false(&contradiction)?);

        // A symbolic boolean is neither definitely true nor definitely false,
        // and the concrete solver (single trivial model) reports has_* the
        // same way as is_*.
        let b = ctx.bools("b")?;
        assert!(!solver.is_true(&b)?);
        assert!(!solver.is_false(&b)?);
        assert!(!solver.has_true(&b)?);
        assert!(!solver.has_false(&b)?);
        Ok(())
    }

    #[test]
    fn test_concrete_solver_min_max() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = ConcreteSolver::new(&ctx);

        // For a concrete value, min == max == the value, in all four
        // signedness variants.
        let v = ctx.bvv(BitVec::from((42, 8)))?;
        assert_eq!(solver.min_unsigned(&v)?, v);
        assert_eq!(solver.max_unsigned(&v)?, v);
        assert_eq!(solver.min_signed(&v)?, v);
        assert_eq!(solver.max_signed(&v)?, v);

        // A compound concrete expression is folded first.
        let sum = ctx.add(
            &ctx.bvv(BitVec::from((40, 8)))?,
            &ctx.bvv(BitVec::from((2, 8)))?,
        )?;
        assert_eq!(solver.min_unsigned(&sum)?, v);
        assert_eq!(solver.max_signed(&sum)?, v);

        // Symbolic expressions are unsupported.
        let x = ctx.bvs("x", 8)?;
        assert!(solver.min_unsigned(&x).is_err());
        assert!(solver.max_unsigned(&x).is_err());
        assert!(solver.min_signed(&x).is_err());
        assert!(solver.max_signed(&x).is_err());
        Ok(())
    }

    #[test]
    fn test_concrete_solver_eval_n() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = ConcreteSolver::new(&ctx);

        let v = ctx.bvv(BitVec::from((7, 8)))?;

        // n == 0 returns no solutions.
        assert!(solver.eval_n(&v, 0)?.is_empty());

        // A concrete expression has exactly one solution, even when more are
        // requested.
        let results = solver.eval_n(&v, 5)?;
        assert_eq!(results, vec![v]);

        // Symbolic expressions are rejected with UnsupportedOperation.
        let x = ctx.bvs("x", 8)?;
        assert!(matches!(
            solver.eval_n(&x, 1),
            Err(ClarirsError::UnsupportedOperation(_))
        ));
        // ... but n == 0 short-circuits before the symbolic check.
        assert!(solver.eval_n(&x, 0)?.is_empty());
        Ok(())
    }

    #[test]
    fn test_concrete_solver_satisfiable_with_extra() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = ConcreteSolver::new(&ctx);

        // The concrete solver ignores constraints entirely, so even a false
        // extra leaves it satisfiable. This documents actual behavior.
        assert!(solver.satisfiable_with_extra(&[])?);
        assert!(solver.satisfiable_with_extra(&[ctx.false_()?])?);
        Ok(())
    }
}
