use crate::prelude::*;

/// A mixin that simplifies expressions before passing them to the underlying solver.
#[derive(Clone, Debug)]
pub struct SimplificationMixin<'c, S: Solver<'c>> {
    inner: S,
    _marker: std::marker::PhantomData<&'c ()>,
}

impl<'c, S: Solver<'c>> SimplificationMixin<'c, S> {
    pub fn new(inner: S) -> Self {
        Self {
            inner,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut S {
        &mut self.inner
    }
}

impl<'c, S: Solver<'c>> HasContext<'c> for SimplificationMixin<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for SimplificationMixin<'c, S> {
    fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
        let simplified = constraint.simplify()?;
        if simplified.is_true() {
            return Ok(());
        }
        self.inner.add(&simplified)
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.inner.clear()
    }

    fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        self.inner.constraints()
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        self.inner.simplify()
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        self.inner.satisfiable()
    }

    fn satisfiable_with_extra(&mut self, extra: &[AstRef<'c>]) -> Result<bool, ClarirsError> {
        let simplified = extra
            .iter()
            .map(|c| c.simplify())
            .collect::<Result<Vec<_>, _>>()?;
        self.inner.satisfiable_with_extra(&simplified)
    }

    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.inner.is_true(&expr.simplify()?)
    }

    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.inner.is_false(&expr.simplify()?)
    }

    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.inner.has_true(&expr.simplify()?)
    }

    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        self.inner.has_false(&expr.simplify()?)
    }

    fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.inner.min_unsigned(&expr.simplify()?)
    }

    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.inner.max_unsigned(&expr.simplify()?)
    }

    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.inner.min_signed(&expr.simplify()?)
    }

    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.inner.max_signed(&expr.simplify()?)
    }

    fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        self.inner.eval_n(&expr.simplify()?, n)
    }

    fn batch_eval(&mut self, exprs: &[AstRef<'c>]) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        let simplified = exprs
            .iter()
            .map(|expr| expr.simplify())
            .collect::<Result<Vec<_>, _>>()?;
        self.inner.batch_eval(&simplified)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::test_support::EqModelSolver;

    #[test]
    fn test_simplification_mixin_simplifies_before_passing() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = SimplificationMixin::new(base_solver);

        // Create an expression that needs simplification: 5 & 5 (should simplify to 5)
        let five = ctx.bvv(BitVec::from((5, 64))).unwrap();
        let and_expr = ctx.and2(&five, &five).unwrap();

        // The mixin should simplify this to just 5 before evaluation
        let results = solver.eval_n(&and_expr, 1).unwrap();
        assert_eq!(results.len(), 1);

        // Verify it was simplified to a concrete BVV
        assert!(matches!(results[0].op(), AstOp::BVV(_)));
    }

    #[test]
    fn test_simplification_mixin_is_true_with_tautology() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = SimplificationMixin::new(base_solver);

        // Create a tautology: true OR false (should simplify to true)
        let true_val = ctx.true_().unwrap();
        let false_val = ctx.false_().unwrap();
        let tautology = ctx.or2(&true_val, &false_val).unwrap();

        // Should simplify to true before checking
        assert!(solver.is_true(&tautology).unwrap());
    }

    #[test]
    fn test_simplification_mixin_add_simplifies_constraint() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = SimplificationMixin::new(base_solver);

        // Create a constraint that needs simplification: NOT(false) (should simplify to true)
        let false_val = ctx.false_().unwrap();
        let constraint = ctx.not(&false_val).unwrap();

        // Should simplify before adding
        assert!(solver.add(&constraint).is_ok());
    }

    #[test]
    fn test_add_skips_tautologies_and_stores_simplified_form() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(EqModelSolver::new(&ctx));

        // A constraint that simplifies to `true` is dropped entirely.
        let tautology = ctx.or2(&ctx.true_()?, &ctx.bools("b")?)?;
        solver.add(&tautology)?;
        assert!(solver.constraints()?.is_empty());

        // A real constraint is stored in simplified form.
        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv(BitVec::from((5, 8)))?;
        let eq = ctx.eq_(&x, &five)?;
        let wrapped = ctx.and2(&eq, &ctx.true_()?)?;
        solver.add(&wrapped)?;
        let constraints = solver.constraints()?;
        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0], eq.simplify()?);
        Ok(())
    }

    #[test]
    fn test_clear_and_simplify_forward_to_inner() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(EqModelSolver::new(&ctx));

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv(BitVec::from((5, 8)))?;
        solver.add(&ctx.eq_(&x, &five)?)?;
        assert_eq!(solver.constraints()?.len(), 1);

        solver.simplify()?;
        assert_eq!(solver.constraints()?.len(), 1);

        solver.clear()?;
        assert!(solver.constraints()?.is_empty());
        Ok(())
    }

    #[test]
    fn test_satisfiable_and_satisfiable_with_extra() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(EqModelSolver::new(&ctx));

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv(BitVec::from((5, 8)))?;
        let six = ctx.bvv(BitVec::from((6, 8)))?;
        solver.add(&ctx.eq_(&x, &five)?)?;
        assert!(solver.satisfiable()?);

        // The extras are simplified before the inner check.
        let consistent = ctx.and2(&ctx.eq_(&x, &five)?, &ctx.true_()?)?;
        assert!(solver.satisfiable_with_extra(&[consistent])?);
        let contradictory = ctx.eq_(&x, &six)?;
        assert!(!solver.satisfiable_with_extra(&[contradictory])?);
        Ok(())
    }

    #[test]
    fn test_truth_queries_simplify_first() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(ConcreteSolver::new(&ctx));

        // and(true, false) simplifies to false.
        let contradiction = ctx.and2(&ctx.true_()?, &ctx.false_()?)?;
        assert!(solver.is_false(&contradiction)?);
        assert!(!solver.is_true(&contradiction)?);
        assert!(solver.has_false(&contradiction)?);
        assert!(!solver.has_true(&contradiction)?);

        // or(true, false) simplifies to true.
        let tautology = ctx.or2(&ctx.true_()?, &ctx.false_()?)?;
        assert!(solver.has_true(&tautology)?);
        assert!(!solver.has_false(&tautology)?);
        Ok(())
    }

    #[test]
    fn test_min_max_simplify_first() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(ConcreteSolver::new(&ctx));

        // 40 + 2 simplifies to 42, which the concrete solver can answer.
        let expr = ctx.add(
            &ctx.bvv(BitVec::from((40, 8)))?,
            &ctx.bvv(BitVec::from((2, 8)))?,
        )?;
        let expected = ctx.bvv(BitVec::from((42, 8)))?;
        assert_eq!(solver.min_unsigned(&expr)?, expected);
        assert_eq!(solver.max_unsigned(&expr)?, expected);
        assert_eq!(solver.min_signed(&expr)?, expected);
        assert_eq!(solver.max_signed(&expr)?, expected);
        Ok(())
    }

    #[test]
    fn test_batch_eval_simplifies_each_expression() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(ConcreteSolver::new(&ctx));

        let sum = ctx.add(
            &ctx.bvv(BitVec::from((1, 8)))?,
            &ctx.bvv(BitVec::from((2, 8)))?,
        )?;
        let tautology = ctx.or2(&ctx.true_()?, &ctx.false_()?)?;
        let results = solver.batch_eval(&[sum, tautology])?;
        assert_eq!(
            results,
            vec![ctx.bvv(BitVec::from((3, 8)))?, ctx.true_()?]
        );
        Ok(())
    }

    #[test]
    fn test_accessors() {
        let ctx = Context::new();
        let mut solver = SimplificationMixin::new(ConcreteSolver::new(&ctx));
        assert!(std::ptr::eq(solver.context(), &ctx));
        assert!(std::ptr::eq(solver.inner().context(), &ctx));
        assert!(std::ptr::eq(solver.inner_mut().context(), &ctx));
    }
}
