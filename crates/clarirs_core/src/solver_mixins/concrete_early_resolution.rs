use crate::prelude::*;

/// A mixin that checks if expressions are concrete and returns them directly
/// without invoking the underlying solver. This can significantly improve
/// performance when working with concrete values.
///
/// Note: This mixin assumes that expressions are already simplified. It is
/// designed to be used inside the SimplificationMixin to avoid redundant
/// simplification calls.
#[derive(Clone, Debug)]
pub struct ConcreteEarlyResolutionMixin<'c, S: Solver<'c>> {
    inner: S,
    _marker: std::marker::PhantomData<&'c ()>,
}

impl<'c, S: Solver<'c>> ConcreteEarlyResolutionMixin<'c, S> {
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

impl<'c, S: Solver<'c>> HasContext<'c> for ConcreteEarlyResolutionMixin<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for ConcreteEarlyResolutionMixin<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.inner.add(constraint)
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.inner.clear()
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        self.inner.constraints()
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        self.inner.simplify()
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        self.inner.satisfiable()
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        // If the expression is concrete, we can determine the result without the solver
        // Assumes the expression is already simplified
        if expr.concrete() {
            return Ok(matches!(expr.op(), BooleanOp::BoolV(true)));
        }
        self.inner.is_true(expr)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        // If the expression is concrete, we can determine the result without the solver
        // Assumes the expression is already simplified
        if expr.concrete() {
            return Ok(matches!(expr.op(), BooleanOp::BoolV(false)));
        }
        self.inner.is_false(expr)
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        // If the expression is concrete, has_true is equivalent to is_true
        if expr.concrete() {
            return self.is_true(expr);
        }
        self.inner.has_true(expr)
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        // If the expression is concrete, has_false is equivalent to is_false
        if expr.concrete() {
            return self.is_false(expr);
        }
        self.inner.has_false(expr)
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        // If concrete, the min is the value itself
        if expr.concrete() {
            return expr.simplify_ext(false, true);
        }
        self.inner.min_unsigned(expr)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        // If concrete, the max is the value itself
        if expr.concrete() {
            return expr.simplify_ext(false, true);
        }
        self.inner.max_unsigned(expr)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        // If concrete, the min is the value itself
        if expr.concrete() {
            return expr.simplify_ext(false, true);
        }
        self.inner.min_signed(expr)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        // If concrete, the max is the value itself
        if expr.concrete() {
            return expr.simplify_ext(false, true);
        }
        self.inner.max_signed(expr)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        // If concrete, return the value without invoking the solver
        if expr.concrete() {
            if n == 0 {
                return Ok(Vec::new());
            }
            return Ok(vec![expr.simplify_ext(false, true)?]);
        }
        self.inner.eval_bool_n(expr, n)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        // If concrete, return the value without invoking the solver
        if expr.concrete() {
            if n == 0 {
                return Ok(Vec::new());
            }
            return Ok(vec![expr.simplify_ext(false, true)?]);
        }
        self.inner.eval_bitvec_n(expr, n)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        // If concrete, return the value without invoking the solver
        if expr.concrete() {
            if n == 0 {
                return Ok(Vec::new());
            }
            return Ok(vec![expr.simplify_ext(false, true)?]);
        }
        self.inner.eval_float_n(expr, n)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        // If concrete, return the value without invoking the solver (assumes already simplified)
        if expr.concrete() {
            if n == 0 {
                return Ok(Vec::new());
            }
            return Ok(vec![expr.simplify_ext(false, true)?]);
        }
        self.inner.eval_string_n(expr, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A solver that panics on any operation - used to verify early resolution
    #[derive(Clone, Debug)]
    struct PanickingSolver<'c> {
        ctx: &'c Context<'c>,
    }

    impl<'c> PanickingSolver<'c> {
        fn new(ctx: &'c Context<'c>) -> Self {
            Self { ctx }
        }
    }

    impl<'c> HasContext<'c> for PanickingSolver<'c> {
        fn context(&self) -> &'c Context<'c> {
            self.ctx
        }
    }

    impl<'c> Solver<'c> for PanickingSolver<'c> {
        fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
            panic!("PanickingSolver::add should not be called");
        }

        fn clear(&mut self) -> Result<(), ClarirsError> {
            panic!("PanickingSolver::clear should not be called");
        }

        fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
            panic!("PanickingSolver::constraints should not be called");
        }

        fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
            panic!("PanickingSolver::satisfiable should not be called");
        }

        fn is_true(&mut self, _: &BoolAst<'c>) -> Result<bool, ClarirsError> {
            panic!("PanickingSolver::is_true should not be called");
        }

        fn is_false(&mut self, _: &BoolAst<'c>) -> Result<bool, ClarirsError> {
            panic!("PanickingSolver::is_false should not be called");
        }

        fn has_true(&mut self, _: &BoolAst<'c>) -> Result<bool, ClarirsError> {
            panic!("PanickingSolver::has_true should not be called");
        }

        fn has_false(&mut self, _: &BoolAst<'c>) -> Result<bool, ClarirsError> {
            panic!("PanickingSolver::has_false should not be called");
        }

        fn min_unsigned(&mut self, _: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
            panic!("PanickingSolver::min_unsigned should not be called");
        }

        fn max_unsigned(&mut self, _: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
            panic!("PanickingSolver::max_unsigned should not be called");
        }

        fn min_signed(&mut self, _: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
            panic!("PanickingSolver::min_signed should not be called");
        }

        fn max_signed(&mut self, _: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
            panic!("PanickingSolver::max_signed should not be called");
        }

        fn eval_bool_n(
            &mut self,
            _: &BoolAst<'c>,
            _: u32,
        ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
            panic!("PanickingSolver::eval_bool_n should not be called");
        }

        fn eval_bitvec_n(
            &mut self,
            _: &BitVecAst<'c>,
            _: u32,
        ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
            panic!("PanickingSolver::eval_bitvec_n should not be called");
        }

        fn eval_float_n(
            &mut self,
            _: &FloatAst<'c>,
            _: u32,
        ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
            panic!("PanickingSolver::eval_float_n should not be called");
        }

        fn eval_string_n(
            &mut self,
            _: &StringAst<'c>,
            _: u32,
        ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
            panic!("PanickingSolver::eval_string_n should not be called");
        }

        fn simplify(&mut self) -> Result<(), ClarirsError> {
            panic!("PanickingSolver::simplify should not be called");
        }
    }

    #[test]
    fn test_concrete_early_resolution_avoids_solver_is_true() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test concrete true value - should NOT call underlying solver
        let true_expr = ctx.true_().unwrap();
        assert!(solver.is_true(&true_expr).unwrap());

        // Test concrete false value - should NOT call underlying solver
        let false_expr = ctx.false_().unwrap();
        assert!(!solver.is_true(&false_expr).unwrap());
    }

    #[test]
    fn test_concrete_early_resolution_avoids_solver_is_false() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test concrete false value - should NOT call underlying solver
        let false_expr = ctx.false_().unwrap();
        assert!(solver.is_false(&false_expr).unwrap());

        // Test concrete true value - should NOT call underlying solver
        let true_expr = ctx.true_().unwrap();
        assert!(!solver.is_false(&true_expr).unwrap());
    }

    #[test]
    fn test_concrete_early_resolution_avoids_solver_eval_bitvec() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test concrete bitvec value - should NOT call underlying solver
        let value = ctx.bvv_prim(42u64).unwrap();
        let results = solver.eval_bitvec_n(&value, 1).unwrap();

        assert_eq!(results.len(), 1);
        assert!(results[0].concrete());
        assert!(matches!(results[0].op(), BitVecOp::BVV(_)));
    }

    #[test]
    fn test_concrete_early_resolution_avoids_solver_min_max() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // For concrete values, min/max should return the value itself WITHOUT calling solver
        let value = ctx.bvv_prim(42u64).unwrap();

        let min = solver.min_unsigned(&value).unwrap();
        let max = solver.max_unsigned(&value).unwrap();

        assert!(min.concrete());
        assert!(max.concrete());
        // Verify they're the same as the input
        assert!(matches!(min.op(), BitVecOp::BVV(_)));
        assert!(matches!(max.op(), BitVecOp::BVV(_)));
    }

    #[test]
    fn test_concrete_early_resolution_avoids_solver_has_true_false() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test has_true with concrete values - should NOT call underlying solver
        let true_expr = ctx.true_().unwrap();
        assert!(solver.has_true(&true_expr).unwrap());

        let false_expr = ctx.false_().unwrap();
        assert!(!solver.has_true(&false_expr).unwrap());

        // Test has_false with concrete values - should NOT call underlying solver
        assert!(solver.has_false(&false_expr).unwrap());
        assert!(!solver.has_false(&true_expr).unwrap());
    }

    #[test]
    fn test_concrete_early_resolution_eval_n_zero() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test that requesting 0 results returns empty vec WITHOUT calling solver
        let value = ctx.bvv_prim(42u64).unwrap();
        let results = solver.eval_bitvec_n(&value, 0).unwrap();

        assert_eq!(results.len(), 0);
    }

    #[test]
    fn test_concrete_early_resolution_eval_bool() {
        let ctx = Context::new();
        let panicking_solver = PanickingSolver::new(&ctx);
        let mut solver = ConcreteEarlyResolutionMixin::new(panicking_solver);

        // Test concrete bool evaluation - should NOT call underlying solver
        let true_expr = ctx.true_().unwrap();
        let results = solver.eval_bool_n(&true_expr, 1).unwrap();

        assert_eq!(results.len(), 1);
        assert!(results[0].concrete());
        assert!(matches!(results[0].op(), BooleanOp::BoolV(true)));
    }
}
