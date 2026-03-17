use std::collections::HashMap;

use crate::algorithms::replace_all;
use crate::prelude::*;

/// A solver mixin that applies expression replacements before delegating to the
/// inner solver.
///
/// Replacements map symbolic (sub-)expressions to simpler or concrete values.
/// When constraints of the form `x == val` (where one side is symbolic and the
/// other concrete) are added, the mixin can automatically record a replacement.
/// All solver queries then transparently substitute known replacements before
/// reaching the underlying solver, which can dramatically speed up solving.
#[derive(Clone, Debug)]
pub struct ReplacementMixin<'c, S: Solver<'c>> {
    inner: S,
    /// Canonical replacement map: AST hash → replacement DynAst.
    replacements: HashMap<u64, DynAst<'c>>,
    /// Expanded cache (includes transitive replacements).
    replacement_cache: HashMap<u64, DynAst<'c>>,
    /// Whether to automatically extract replacements from added constraints.
    auto_replace: bool,
    /// Whether to record solve results as replacements (less safe but faster).
    unsafe_replacement: bool,
    _marker: std::marker::PhantomData<&'c ()>,
}

impl<'c, S: Solver<'c>> ReplacementMixin<'c, S> {
    pub fn new(inner: S) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace: true,
            unsafe_replacement: false,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn new_with_options(inner: S, auto_replace: bool, unsafe_replacement: bool) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace,
            unsafe_replacement,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut S {
        &mut self.inner
    }

    // ------------------------------------------------------------------
    // Replacement management
    // ------------------------------------------------------------------

    /// Register a replacement: future occurrences of `old` will be replaced
    /// with `new` before reaching the inner solver.
    pub fn add_replacement(&mut self, old: DynAst<'c>, new: DynAst<'c>) {
        let hash = old.inner_hash();
        self.replacements.insert(hash, new.clone());
        // Invalidate the transitive cache – rebuild from scratch.
        self.replacement_cache = self.replacements.clone();
    }

    /// Remove specific replacements by their original-expression hashes.
    pub fn remove_replacements(&mut self, hashes: &[u64]) {
        for h in hashes {
            self.replacements.remove(h);
        }
        self.replacement_cache = self.replacements.clone();
    }

    /// Drop all recorded replacements.
    pub fn clear_replacements(&mut self) {
        self.replacements.clear();
        self.replacement_cache.clear();
    }

    /// Return a read-only view of the current replacements.
    pub fn replacements(&self) -> &HashMap<u64, DynAst<'c>> {
        &self.replacements
    }

    // ------------------------------------------------------------------
    // Internal helpers
    // ------------------------------------------------------------------

    /// Apply all known replacements to a boolean AST.
    fn replace_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_bool()
                .ok_or_else(|| ClarirsError::TypeError("Expected BoolAst in cache".to_string()));
        }
        let dyn_ast = DynAst::Boolean(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_bool().ok_or_else(|| {
            ClarirsError::TypeError("Expected BoolAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::Boolean(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a bitvec AST.
    fn replace_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_bitvec()
                .ok_or_else(|| ClarirsError::TypeError("Expected BitVecAst in cache".to_string()));
        }
        let dyn_ast = DynAst::BitVec(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_bitvec().ok_or_else(|| {
            ClarirsError::TypeError("Expected BitVecAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::BitVec(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a float AST.
    fn replace_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_float()
                .ok_or_else(|| ClarirsError::TypeError("Expected FloatAst in cache".to_string()));
        }
        let dyn_ast = DynAst::Float(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_float().ok_or_else(|| {
            ClarirsError::TypeError("Expected FloatAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::Float(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a string AST.
    fn replace_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_string()
                .ok_or_else(|| ClarirsError::TypeError("Expected StringAst in cache".to_string()));
        }
        let dyn_ast = DynAst::String(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_string().ok_or_else(|| {
            ClarirsError::TypeError("Expected StringAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::String(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to an AST using the replace algorithm.
    fn apply_replacements(&self, ast: DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        replace_all(ast, &self.replacement_cache)
    }

    /// Try to extract a replacement from a constraint of the form `x == val`
    /// where one side is symbolic and the other is concrete, or `Not(x)` which
    /// implies `x == false`.
    fn extract_replacement(&mut self, constraint: &BoolAst<'c>) {
        if !constraint.symbolic() {
            return;
        }

        match constraint.op() {
            // Not(x) → replace x with false
            BooleanOp::Not(inner) => {
                if inner.symbolic() {
                    let ctx = constraint.context();
                    if let Ok(false_val) = ctx.false_() {
                        self.add_replacement(
                            DynAst::Boolean(inner.clone()),
                            DynAst::Boolean(false_val),
                        );
                    }
                }
            }
            // bool_a == bool_b where one is symbolic and one is concrete
            BooleanOp::BoolEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::Boolean(old), DynAst::Boolean(new));
                }
            }
            // bv_a == bv_b where one is symbolic and one is concrete
            BooleanOp::Eq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::BitVec(old), DynAst::BitVec(new));
                }
            }
            // fp_a == fp_b where one is symbolic and one is concrete
            BooleanOp::FpEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::Float(old), DynAst::Float(new));
                }
            }
            // str_a == str_b where one is symbolic and one is concrete
            BooleanOp::StrEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::String(old), DynAst::String(new));
                }
            }
            _ => {}
        }
    }
}

impl<'c, S: Solver<'c>> HasContext<'c> for ReplacementMixin<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for ReplacementMixin<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        // Extract replacements from simple equality constraints before adding.
        if self.auto_replace {
            self.extract_replacement(constraint);
        }

        // Apply existing replacements to the constraint before passing to inner.
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
        let result = self.inner.min_unsigned(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.max_unsigned(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.min_signed(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.max_signed(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        let results = self.inner.eval_bool_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(
                DynAst::Boolean(expr.clone()),
                DynAst::Boolean(first.clone()),
            );
        }
        Ok(results)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let results = self.inner.eval_bitvec_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(first.clone()));
        }
        Ok(results)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let replaced = self.replace_float(expr)?;
        let results = self.inner.eval_float_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::Float(expr.clone()), DynAst::Float(first.clone()));
        }
        Ok(results)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let replaced = self.replace_string(expr)?;
        let results = self.inner.eval_string_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::String(expr.clone()), DynAst::String(first.clone()));
        }
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_replacement_mixin_basic_bitvec_replacement() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create a symbolic variable and a concrete value
        let x = ctx.bvs("x", 8).unwrap();
        let five = ctx.bvv_prim(5u8).unwrap();

        // Manually add a replacement: x → 5
        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));

        // Evaluating x should now return 5 (after replacement makes it concrete)
        let result = solver.eval_bitvec(&x).unwrap();
        assert!(result.concrete());
        assert_eq!(result, five);
    }

    #[test]
    fn test_replacement_mixin_auto_replace_from_eq_constraint() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create x == 42
        let x = ctx.bvs("x", 64).unwrap();
        let forty_two = ctx.bvv_prim(42u64).unwrap();
        let constraint = ctx.eq_(&x, &forty_two).unwrap();

        // Adding this constraint should auto-extract x → 42
        solver.add(&constraint).unwrap();

        // Now evaluating x should return 42
        let result = solver.eval_bitvec(&x).unwrap();
        assert!(result.concrete());
        assert_eq!(result, forty_two);
    }

    #[test]
    fn test_replacement_mixin_auto_replace_from_not_constraint() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create Not(b) where b is symbolic
        let b = ctx.bools("b").unwrap();
        let not_b = ctx.not(&b).unwrap();

        // Adding Not(b) should auto-extract b → false
        solver.add(&not_b).unwrap();

        // Now evaluating b should return false
        let result = solver.eval_bool(&b).unwrap();
        assert!(result.concrete());
        assert!(result.is_false());
    }

    #[test]
    fn test_replacement_mixin_clear_replacements() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        let x = ctx.bvs("x", 8).unwrap();
        let five = ctx.bvv_prim(5u8).unwrap();

        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));
        assert!(!solver.replacements().is_empty());

        solver.clear_replacements();
        assert!(solver.replacements().is_empty());
    }

    #[test]
    fn test_replacement_mixin_no_replace_concrete() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Concrete expressions should pass through without replacement
        let five = ctx.bvv_prim(5u8).unwrap();
        let result = solver.eval_bitvec(&five).unwrap();
        assert_eq!(result, five);
    }

    #[test]
    fn test_replacement_mixin_bool_eq_auto_replace() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create b == true where b is symbolic
        let b = ctx.bools("b").unwrap();
        let true_val = ctx.true_().unwrap();
        let constraint = ctx.eq_(&b, &true_val).unwrap();

        solver.add(&constraint).unwrap();

        let result = solver.eval_bool(&b).unwrap();
        assert!(result.is_true());
    }
}
