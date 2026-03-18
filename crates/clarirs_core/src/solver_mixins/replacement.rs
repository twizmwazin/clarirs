use std::collections::HashMap;

use crate::{algorithms::Replace, prelude::*};

/// A solver mixin that applies expression replacements before delegating to
/// the inner solver. This mirrors claripy's `ReplacementFrontend`.
///
/// When constraints of the form `x == <concrete>` are added, the replacement
/// solver automatically extracts the mapping and uses it to simplify future
/// queries. Explicit replacements can also be added via [`add_replacement`].
///
/// The replacement dictionary maps AST hashes to their replacement `DynAst`
/// values. When a query is made, all known replacements are applied to the
/// expression in a single pass before forwarding to the inner solver.
#[derive(Clone, Debug)]
pub struct ReplacementSolver<'c, S: Solver<'c>> {
    inner: S,
    /// The canonical set of replacements (hash → replacement AST).
    replacements: HashMap<u64, DynAst<'c>>,
    /// Cache that includes derived replacements from sub-expression traversal.
    replacement_cache: HashMap<u64, DynAst<'c>>,
    /// Whether to automatically extract replacements from `x == <concrete>` constraints.
    auto_replace: bool,
    _marker: std::marker::PhantomData<&'c ()>,
}

impl<'c, S: Solver<'c>> ReplacementSolver<'c, S> {
    pub fn new(inner: S) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace: true,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn new_with_options(inner: S, auto_replace: bool) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut S {
        &mut self.inner
    }

    /// Add an explicit replacement mapping: occurrences of `old` will be
    /// replaced with `new` in all future queries.
    pub fn add_replacement(&mut self, old: DynAst<'c>, new: DynAst<'c>) {
        let hash = old.inner_hash();
        self.replacements.insert(hash, new.clone());
        self.replacement_cache.insert(hash, new);
    }

    /// Remove specific replacements by their hashes.
    pub fn remove_replacements(&mut self, hashes: &[u64]) {
        for hash in hashes {
            self.replacements.remove(hash);
        }
        // Rebuild cache from canonical replacements
        self.replacement_cache = self.replacements.clone();
    }

    /// Clear all replacements.
    pub fn clear_replacements(&mut self) {
        self.replacements.clear();
        self.replacement_cache.clear();
    }

    /// Get the current replacement map (hash → DynAst).
    pub fn replacements(&self) -> &HashMap<u64, DynAst<'c>> {
        &self.replacements
    }

    /// Apply known replacements to a BoolAst.
    fn replace_bool(&self, ast: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        ast.replace_many(&self.replacement_cache)
    }

    /// Apply known replacements to a BitVecAst.
    fn replace_bitvec(&self, ast: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        ast.replace_many(&self.replacement_cache)
    }

    /// Apply known replacements to a FloatAst.
    fn replace_float(&self, ast: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        ast.replace_many(&self.replacement_cache)
    }

    /// Apply known replacements to a StringAst.
    fn replace_string(&self, ast: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        ast.replace_many(&self.replacement_cache)
    }

    /// Try to extract a replacement from an equality constraint like `sym == concrete`.
    fn try_extract_replacement(&mut self, constraint: &BoolAst<'c>) {
        match constraint.op() {
            BooleanOp::BoolEq(lhs, rhs) => {
                if lhs.symbolic() && !rhs.symbolic() {
                    self.add_replacement(
                        DynAst::Boolean(lhs.clone()),
                        DynAst::Boolean(rhs.clone()),
                    );
                } else if !lhs.symbolic() && rhs.symbolic() {
                    self.add_replacement(
                        DynAst::Boolean(rhs.clone()),
                        DynAst::Boolean(lhs.clone()),
                    );
                }
            }
            BooleanOp::Eq(lhs, rhs) => {
                if lhs.symbolic() && !rhs.symbolic() {
                    self.add_replacement(DynAst::BitVec(lhs.clone()), DynAst::BitVec(rhs.clone()));
                } else if !lhs.symbolic() && rhs.symbolic() {
                    self.add_replacement(DynAst::BitVec(rhs.clone()), DynAst::BitVec(lhs.clone()));
                }
            }
            BooleanOp::Not(inner) => {
                // Not(x) means x is false
                if inner.symbolic()
                    && let Ok(false_val) = constraint.context().false_()
                {
                    self.add_replacement(
                        DynAst::Boolean(inner.clone()),
                        DynAst::Boolean(false_val),
                    );
                }
            }
            _ => {}
        }
    }
}

impl<'c, S: Solver<'c>> HasContext<'c> for ReplacementSolver<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for ReplacementSolver<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        if self.auto_replace {
            self.try_extract_replacement(constraint);
        }

        let replaced = self.replace_bool(constraint)?;
        self.inner.add(&replaced)
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
        let replaced = self.replace_bool(expr)?;
        self.inner.is_true(&replaced)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.is_false(&replaced)
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.has_true(&replaced)
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.has_false(&replaced)
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        self.inner.min_unsigned(&replaced)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        self.inner.max_unsigned(&replaced)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        self.inner.min_signed(&replaced)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        self.inner.max_signed(&replaced)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.eval_bool_n(&replaced, n)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        self.inner.eval_bitvec_n(&replaced, n)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let replaced = self.replace_float(expr)?;
        self.inner.eval_float_n(&replaced, n)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let replaced = self.replace_string(expr)?;
        self.inner.eval_string_n(&replaced, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::AstFactory;

    #[test]
    fn test_replacement_solver_basic() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let inner = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementSolver::new(inner);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv_prim(5u8)?;

        // Add explicit replacement: x -> 5
        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));

        // Evaluating x should now return 5
        let result = solver.eval_bitvec(&x)?;
        assert_eq!(result, five);

        Ok(())
    }

    #[test]
    fn test_replacement_solver_auto_extract() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let inner = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementSolver::new(inner);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv_prim(5u8)?;

        // Add constraint: x == 5 (should auto-extract replacement)
        let eq_constraint = ctx.eq_(&x, &five)?;
        solver.add(&eq_constraint)?;

        // Evaluating x should now return 5
        let result = solver.eval_bitvec(&x)?;
        assert_eq!(result, five);

        Ok(())
    }

    #[test]
    fn test_replacement_solver_expression() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let inner = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementSolver::new(inner);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv_prim(5u8)?;
        let three = ctx.bvv_prim(3u8)?;

        // Replace x with 5
        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));

        // Evaluating x + 3 should return 8
        let expr = ctx.add(&x, &three)?;
        let result = solver.eval_bitvec(&expr)?;
        let expected = ctx.bvv_prim(8u8)?;
        assert_eq!(result, expected);

        Ok(())
    }

    #[test]
    fn test_replacement_solver_clear() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let inner = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementSolver::new(inner);

        let x = ctx.bvs("x", 8)?;
        let five = ctx.bvv_prim(5u8)?;

        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));
        assert!(!solver.replacements().is_empty());

        solver.clear_replacements();
        assert!(solver.replacements().is_empty());

        Ok(())
    }

    #[test]
    fn test_replacement_solver_bool() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let inner = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementSolver::new(inner);

        let x = ctx.bools("x")?;

        // Replace x with true
        solver.add_replacement(DynAst::Boolean(x.clone()), DynAst::Boolean(ctx.true_()?));

        assert!(solver.is_true(&x)?);
        assert!(!solver.is_false(&x)?);

        Ok(())
    }
}
