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
}

impl<'c, S: Solver<'c>> HasContext<'c> for SimplificationMixin<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for SimplificationMixin<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.inner.add(&constraint.simplify()?)
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
        self.inner.is_true(&expr.simplify()?)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.inner.is_false(&expr.simplify()?)
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.inner.has_true(&expr.simplify()?)
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        self.inner.has_false(&expr.simplify()?)
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.inner.min_unsigned(&expr.simplify()?)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.inner.max_unsigned(&expr.simplify()?)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.inner.min_signed(&expr.simplify()?)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.inner.max_signed(&expr.simplify()?)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        self.inner.eval_bool_n(&expr.simplify()?, n)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        self.inner.eval_bitvec_n(&expr.simplify()?, n)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        self.inner.eval_float_n(&expr.simplify()?, n)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        self.inner.eval_string_n(&expr.simplify()?, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplification_mixin_simplifies_before_passing() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = SimplificationMixin::new(base_solver);

        // Create an expression that needs simplification: 5 & 5 (should simplify to 5)
        let five = ctx.bvv_prim(5u64).unwrap();
        let and_expr = ctx.and(&five, &five).unwrap();

        // The mixin should simplify this to just 5 before evaluation
        let results = solver.eval_bitvec_n(&and_expr, 1).unwrap();
        assert_eq!(results.len(), 1);

        // Verify it was simplified to a concrete BVV
        assert!(matches!(results[0].op(), BitVecOp::BVV(_)));
    }

    #[test]
    fn test_simplification_mixin_is_true_with_tautology() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = SimplificationMixin::new(base_solver);

        // Create a tautology: true OR false (should simplify to true)
        let true_val = ctx.true_().unwrap();
        let false_val = ctx.false_().unwrap();
        let tautology = ctx.or(&true_val, &false_val).unwrap();

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
}
