use std::collections::BTreeSet;

use crate::prelude::*;

/// A hybrid solver that combines an approximate solver with an exact solver.
///
/// Modeled after claripy's HybridFrontend, this solver maintains two backends:
/// - An **approximate** solver (e.g., VSA) for fast but imprecise results
/// - An **exact** solver (e.g., Z3) for precise constraint solving
///
/// Constraints are added to both solvers. For evaluation, the solver first
/// tries the approximate backend and falls back to the exact backend when:
/// - The approximate solver returns an error
/// - The approximate solver returns results that need validation
///
/// For operations requiring correctness (satisfiability, is_true, is_false),
/// the exact solver is always consulted when the approximate solver cannot
/// give a definitive answer.
#[derive(Clone, Debug)]
pub struct HybridSolver<'c, A: Solver<'c>, E: Solver<'c>> {
    approximate: A,
    exact: E,
    ctx: &'c Context<'c>,
    /// When true, `eval_n` for more than two solutions asks the approximate
    /// backend first and only consults the exact backend when the
    /// approximation is inexact (claripy's `approximate_first`).
    approximate_first: bool,
}

impl<'c, A: Solver<'c>, E: Solver<'c>> HybridSolver<'c, A, E> {
    /// Create a new hybrid solver with the given approximate and exact backends.
    pub fn new(ctx: &'c Context<'c>, approximate: A, exact: E) -> Self {
        Self::new_with_options(ctx, approximate, exact, false)
    }

    /// Create a new hybrid solver, optionally preferring approximate results
    /// for multi-solution `eval_n` queries.
    pub fn new_with_options(
        ctx: &'c Context<'c>,
        approximate: A,
        exact: E,
        approximate_first: bool,
    ) -> Self {
        Self {
            approximate,
            exact,
            ctx,
            approximate_first,
        }
    }

    /// Whether this solver prefers approximate results for multi-solution
    /// `eval_n` queries.
    pub fn approximate_first(&self) -> bool {
        self.approximate_first
    }

    /// claripy's approximate-first heuristic: draw n + 1 solutions from the
    /// approximate backend; the extra solution tells us whether the
    /// approximation is exhaustive. If it is (<= n solutions), or no
    /// constraint mentions the expression's variables (so the approximation
    /// cannot be refined by solving), use it. Otherwise ask the exact backend
    /// too and use whichever found fewer solutions.
    fn eval_n_approximate_first(
        &mut self,
        expr: &AstRef<'c>,
        n: u32,
    ) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        let mut approx = match self.approximate.eval_n(expr, n + 1) {
            Ok(approx) if !approx.is_empty() => approx,
            _ => return self.exact.eval_n(expr, n),
        };

        if approx.len() > n as usize
            && self.constraints_mention(expr)?
            && let Ok(exact) = self.exact.eval_n(expr, n + 1)
            && exact.len() < approx.len()
        {
            approx = exact;
        }

        approx.truncate(n as usize);
        Ok(approx)
    }

    /// Whether any asserted constraint shares a variable with `expr`.
    fn constraints_mention(&self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        let expr_vars = expr.variables();
        Ok(self
            .exact
            .constraints()?
            .iter()
            .any(|c| c.variables().iter().any(|v| expr_vars.contains(v))))
    }

    /// Get a reference to the approximate solver.
    pub fn approximate(&self) -> &A {
        &self.approximate
    }

    /// Get a mutable reference to the approximate solver.
    pub fn approximate_mut(&mut self) -> &mut A {
        &mut self.approximate
    }

    /// Get a reference to the exact solver.
    pub fn exact(&self) -> &E {
        &self.exact
    }

    /// Get a mutable reference to the exact solver.
    pub fn exact_mut(&mut self) -> &mut E {
        &mut self.exact
    }
}

impl<'c, A: Solver<'c>, E: Solver<'c>> HasContext<'c> for HybridSolver<'c, A, E> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, A: Solver<'c>, E: Solver<'c>> Solver<'c> for HybridSolver<'c, A, E> {
    fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
        // Add constraints to both backends. The approximate solver may ignore
        // them (as VSA does), but the exact solver tracks them.
        let _ = self.approximate.add(constraint);
        self.exact.add(constraint)
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        let _ = self.approximate.clear();
        self.exact.clear()
    }

    fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        self.exact.constraints()
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        let _ = self.approximate.simplify();
        self.exact.simplify()
    }

    fn variables(&self) -> Result<BTreeSet<InternedString>, ClarirsError> {
        self.exact.variables()
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        // Try approximate first - if it says definitely unsat, trust it.
        // Otherwise, fall back to exact.
        if let Ok(false) = self.approximate.satisfiable() {
            return Ok(false);
        }
        self.exact.satisfiable()
    }

    fn satisfiable_with_extra(&mut self, extra: &[AstRef<'c>]) -> Result<bool, ClarirsError> {
        if let Ok(false) = self.approximate.satisfiable_with_extra(extra) {
            return Ok(false);
        }
        self.exact.satisfiable_with_extra(extra)
    }

    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.is_true(expr);
        }
        // For symbolic expressions, always consult exact solver
        self.exact.is_true(expr)
    }

    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.is_false(expr);
        }
        self.exact.is_false(expr)
    }

    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.has_true(expr);
        }
        // If approximate says definitely true, trust it (over-approximation is safe here)
        match self.approximate.has_true(expr) {
            Ok(true) => Ok(true),
            _ => self.exact.has_true(expr),
        }
    }

    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.has_false(expr);
        }
        match self.approximate.has_false(expr) {
            Ok(true) => Ok(true),
            _ => self.exact.has_false(expr),
        }
    }

    fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.min_unsigned(expr);
        }
        self.exact.min_unsigned(expr)
    }

    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.max_unsigned(expr);
        }
        self.exact.max_unsigned(expr)
    }

    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.min_signed(expr);
        }
        self.exact.min_signed(expr)
    }

    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.max_signed(expr);
        }
        self.exact.max_signed(expr)
    }

    fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if self.approximate_first && n > 2 {
            return self.eval_n_approximate_first(expr, n);
        }
        // Try the approximate solver first; verify symbolic results against
        // the exact solver, and fall back to it whenever the approximate
        // solver fails or produces nothing.
        if !expr.symbolic() {
            if let Ok(result) = self.approximate.eval_n(expr, n)
                && !result.is_empty()
            {
                return Ok(result);
            }
            return self.exact.eval_n(expr, n);
        }
        match self.approximate.eval_n(expr, n) {
            Ok(approx_results) if !approx_results.is_empty() => match self.exact.eval_n(expr, n) {
                Ok(exact) => Ok(exact),
                Err(_) => Ok(approx_results),
            },
            _ => self.exact.eval_n(expr, n),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use crate::ast::AstFactory;
    use crate::prelude::*;

    /// A scripted solver with preset answers and per-query call counters, so
    /// tests can pin down exactly which backend the hybrid solver consults.
    /// Counters are shared across clones (the trait's default methods clone).
    #[derive(Clone, Debug)]
    struct ScriptedSolver<'c> {
        ctx: &'c Context<'c>,
        constraints: Vec<AstRef<'c>>,
        /// Scripted satisfiable() answer; None means "return an error".
        sat: Option<bool>,
        /// Solution pool: eval_n returns the first min(n, len) entries.
        solutions: Vec<AstRef<'c>>,
        /// When set, eval_n/min/max return an error instead.
        fail_eval: bool,
        /// When set, add() returns an error.
        fail_add: bool,
        /// Scripted has_true()/has_false() answer; None means "return an error".
        has_answer: Option<bool>,
        sat_calls: Rc<Cell<usize>>,
        eval_calls: Rc<Cell<usize>>,
        truth_calls: Rc<Cell<usize>>,
        minmax_calls: Rc<Cell<usize>>,
    }

    impl<'c> ScriptedSolver<'c> {
        fn new(ctx: &'c Context<'c>) -> Self {
            Self {
                ctx,
                constraints: Vec::new(),
                sat: Some(true),
                solutions: Vec::new(),
                fail_eval: false,
                fail_add: false,
                has_answer: Some(false),
                sat_calls: Rc::new(Cell::new(0)),
                eval_calls: Rc::new(Cell::new(0)),
                truth_calls: Rc::new(Cell::new(0)),
                minmax_calls: Rc::new(Cell::new(0)),
            }
        }

        fn scripted_error() -> ClarirsError {
            ClarirsError::UnsupportedOperation("scripted failure".to_string())
        }
    }

    impl<'c> HasContext<'c> for ScriptedSolver<'c> {
        fn context(&self) -> &'c Context<'c> {
            self.ctx
        }
    }

    impl<'c> Solver<'c> for ScriptedSolver<'c> {
        fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
            if self.fail_add {
                return Err(Self::scripted_error());
            }
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
            self.sat_calls.set(self.sat_calls.get() + 1);
            self.sat.ok_or_else(Self::scripted_error)
        }

        fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.truth_calls.set(self.truth_calls.get() + 1);
            Ok(expr.simplify()?.is_true())
        }

        fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.truth_calls.set(self.truth_calls.get() + 1);
            Ok(expr.simplify()?.is_false())
        }

        fn has_true(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.truth_calls.set(self.truth_calls.get() + 1);
            self.has_answer.ok_or_else(Self::scripted_error)
        }

        fn has_false(&mut self, _: &AstRef<'c>) -> Result<bool, ClarirsError> {
            self.truth_calls.set(self.truth_calls.get() + 1);
            self.has_answer.ok_or_else(Self::scripted_error)
        }

        fn min_unsigned(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.minmax_calls.set(self.minmax_calls.get() + 1);
            if self.fail_eval {
                return Err(Self::scripted_error());
            }
            self.solutions.first().cloned().ok_or(ClarirsError::Unsat)
        }

        fn max_unsigned(&mut self, _: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.minmax_calls.set(self.minmax_calls.get() + 1);
            if self.fail_eval {
                return Err(Self::scripted_error());
            }
            self.solutions.last().cloned().ok_or(ClarirsError::Unsat)
        }

        fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.min_unsigned(expr)
        }

        fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
            self.max_unsigned(expr)
        }

        fn eval_n(&mut self, _: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
            self.eval_calls.set(self.eval_calls.get() + 1);
            if self.fail_eval {
                return Err(Self::scripted_error());
            }
            Ok(self.solutions.iter().take(n as usize).cloned().collect())
        }
    }

    /// Build `count` distinct 8-bit constants starting at `start`.
    fn values<'c>(
        ctx: &'c Context<'c>,
        start: u64,
        count: u64,
    ) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        (start..start + count)
            .map(|v| ctx.bvv(BitVec::from((v, 8))))
            .collect()
    }

    #[test]
    fn test_hybrid_solver_concrete() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let approx = ConcreteSolver::new(&ctx);
        let exact = ConcreteSolver::new(&ctx);
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let t = ctx.true_()?;
        let f = ctx.false_()?;
        assert!(solver.is_true(&t)?);
        assert!(solver.is_false(&f)?);
        assert!(!solver.is_true(&f)?);
        assert!(!solver.is_false(&t)?);

        let a = ctx.bvv(BitVec::from((10, 8)))?;
        let b = ctx.bvv(BitVec::from((20, 8)))?;
        let sum = ctx.add(&a, &b)?;
        let result = solver.eval(&sum)?;
        assert_eq!(result, ctx.bvv(BitVec::from((30, 8)))?);

        assert!(solver.satisfiable()?);

        Ok(())
    }

    #[test]
    fn test_add_ignores_approximate_failure() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.fail_add = true;
        let exact = ScriptedSolver::new(&ctx);
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let x = ctx.bvs("x", 8)?;
        let constraint = ctx.eq_(&x, &ctx.bvv(BitVec::from((1, 8)))?)?;
        // The approximate backend's failure is swallowed; the exact backend
        // tracks the constraint and defines constraints()/variables().
        solver.add(&constraint)?;
        assert!(solver.approximate().constraints.is_empty());
        assert_eq!(solver.exact().constraints, vec![constraint.clone()]);
        assert_eq!(solver.constraints()?.len(), 1);
        let variables = solver.variables()?;
        let vars: Vec<&str> = variables.iter().map(|v| v.as_str()).collect();
        assert_eq!(vars, vec!["x"]);

        // A failure in the exact backend propagates.
        solver.exact_mut().fail_add = true;
        assert!(solver.add(&constraint).is_err());
        Ok(())
    }

    #[test]
    fn test_clear_resets_both_backends() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let approx = ScriptedSolver::new(&ctx);
        let exact = ScriptedSolver::new(&ctx);
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let constraint = ctx.eq_(&ctx.bvs("x", 8)?, &ctx.bvv(BitVec::from((1, 8)))?)?;
        solver.add(&constraint)?;
        solver.clear()?;
        assert!(solver.constraints()?.is_empty());
        assert!(solver.approximate().constraints.is_empty());
        assert!(solver.exact().constraints.is_empty());
        Ok(())
    }

    #[test]
    fn test_satisfiable_trusts_approximate_unsat() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.sat = Some(false);
        let exact = ScriptedSolver::new(&ctx);
        let exact_sat_calls = exact.sat_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        // Approximate unsat is definitive; the exact backend is not consulted.
        assert!(!solver.satisfiable()?);
        assert_eq!(exact_sat_calls.get(), 0);
        Ok(())
    }

    #[test]
    fn test_satisfiable_falls_back_to_exact() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Approximate sat is not definitive: the exact answer (unsat) wins.
        let approx = ScriptedSolver::new(&ctx);
        let mut exact = ScriptedSolver::new(&ctx);
        exact.sat = Some(false);
        let mut solver = HybridSolver::new(&ctx, approx, exact);
        assert!(!solver.satisfiable()?);

        // An approximate error also falls back to the exact backend.
        let mut approx = ScriptedSolver::new(&ctx);
        approx.sat = None;
        let exact = ScriptedSolver::new(&ctx);
        let mut solver = HybridSolver::new(&ctx, approx, exact);
        assert!(solver.satisfiable()?);
        Ok(())
    }

    #[test]
    fn test_satisfiable_with_extra_trusts_approximate_unsat() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.sat = Some(false);
        let exact = ScriptedSolver::new(&ctx);
        let exact_sat_calls = exact.sat_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let extra = ctx.eq_(&ctx.bvs("x", 8)?, &ctx.bvv(BitVec::from((1, 8)))?)?;
        assert!(!solver.satisfiable_with_extra(&[extra.clone()])?);
        assert_eq!(exact_sat_calls.get(), 0);

        // When the approximation is inconclusive, the exact backend decides.
        solver.approximate_mut().sat = Some(true);
        solver.exact_mut().sat = Some(false);
        assert!(!solver.satisfiable_with_extra(&[extra])?);
        Ok(())
    }

    #[test]
    fn test_concrete_queries_use_approximate_backend() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.has_answer = Some(true);
        approx.solutions = values(&ctx, 42, 1)?;
        let exact = ScriptedSolver::new(&ctx);
        let exact_truth = exact.truth_calls.clone();
        let exact_minmax = exact.minmax_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let t = ctx.true_()?;
        let f = ctx.false_()?;
        let v = ctx.bvv(BitVec::from((42, 8)))?;

        assert!(solver.is_true(&t)?);
        assert!(solver.is_false(&f)?);
        assert!(solver.has_true(&t)?);
        assert!(solver.has_false(&f)?);
        assert_eq!(solver.min_unsigned(&v)?, v);
        assert_eq!(solver.max_unsigned(&v)?, v);
        assert_eq!(solver.min_signed(&v)?, v);
        assert_eq!(solver.max_signed(&v)?, v);

        // Every concrete query was answered by the approximate backend.
        assert_eq!(exact_truth.get(), 0);
        assert_eq!(exact_minmax.get(), 0);
        Ok(())
    }

    #[test]
    fn test_symbolic_queries_use_exact_backend() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let approx = ScriptedSolver::new(&ctx);
        let approx_minmax = approx.minmax_calls.clone();
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 7, 2)?;
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let x = ctx.bvs("x", 8)?;
        // is_true/is_false on symbolic expressions go straight to exact.
        assert!(!solver.is_true(&x.clone())?);
        assert!(!solver.is_false(&x.clone())?);
        // min/max on symbolic expressions go straight to exact.
        assert_eq!(solver.min_unsigned(&x)?, ctx.bvv(BitVec::from((7, 8)))?);
        assert_eq!(solver.max_unsigned(&x)?, ctx.bvv(BitVec::from((8, 8)))?);
        assert_eq!(solver.min_signed(&x)?, ctx.bvv(BitVec::from((7, 8)))?);
        assert_eq!(solver.max_signed(&x)?, ctx.bvv(BitVec::from((8, 8)))?);
        assert_eq!(approx_minmax.get(), 0);
        Ok(())
    }

    #[test]
    fn test_has_true_symbolic_trusts_approximate_yes() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.has_answer = Some(true);
        let exact = ScriptedSolver::new(&ctx);
        let exact_truth = exact.truth_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let b = ctx.bools("b")?;
        // Approximate "could be true" is trusted without consulting exact.
        assert!(solver.has_true(&b)?);
        assert!(solver.has_false(&b)?);
        assert_eq!(exact_truth.get(), 0);

        // Approximate "no" is not trusted: the exact answer is used.
        solver.approximate_mut().has_answer = Some(false);
        solver.exact_mut().has_answer = Some(true);
        assert!(solver.has_true(&b)?);
        assert!(solver.has_false(&b)?);

        // An approximate error also falls back to exact.
        solver.approximate_mut().has_answer = None;
        solver.exact_mut().has_answer = Some(false);
        assert!(!solver.has_true(&b)?);
        assert!(!solver.has_false(&b)?);
        Ok(())
    }

    #[test]
    fn test_eval_n_zero_returns_empty() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let approx = ScriptedSolver::new(&ctx);
        let approx_calls = approx.eval_calls.clone();
        let exact = ScriptedSolver::new(&ctx);
        let exact_calls = exact.eval_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        assert!(solver.eval_n(&ctx.bvs("x", 8)?, 0)?.is_empty());
        assert_eq!(approx_calls.get(), 0);
        assert_eq!(exact_calls.get(), 0);
        Ok(())
    }

    #[test]
    fn test_eval_n_symbolic_prefers_exact_results() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 1, 2)?;
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 100, 1)?;
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let x = ctx.bvs("x", 8)?;
        // Both backends produce values; the exact result wins.
        assert_eq!(solver.eval_n(&x, 2)?, values(&ctx, 100, 1)?);

        // If the exact backend fails, the approximate results are kept.
        solver.exact_mut().fail_eval = true;
        assert_eq!(solver.eval_n(&x, 2)?, values(&ctx, 1, 2)?);

        // If the approximate backend fails, the exact backend answers alone.
        solver.approximate_mut().fail_eval = true;
        solver.exact_mut().fail_eval = false;
        assert_eq!(solver.eval_n(&x, 2)?, values(&ctx, 100, 1)?);

        // If the approximate backend finds nothing, exact answers too.
        solver.approximate_mut().fail_eval = false;
        solver.approximate_mut().solutions = Vec::new();
        assert_eq!(solver.eval_n(&x, 2)?, values(&ctx, 100, 1)?);
        Ok(())
    }

    #[test]
    fn test_eval_n_concrete_uses_approximate_without_validation() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 42, 1)?;
        let exact = ScriptedSolver::new(&ctx);
        let exact_calls = exact.eval_calls.clone();
        let mut solver = HybridSolver::new(&ctx, approx, exact);

        let v = ctx.bvv(BitVec::from((42, 8)))?;
        assert_eq!(solver.eval_n(&v, 1)?, values(&ctx, 42, 1)?);
        assert_eq!(exact_calls.get(), 0);

        // An empty approximate result falls back to exact.
        solver.approximate_mut().solutions = Vec::new();
        solver.exact_mut().solutions = values(&ctx, 42, 1)?;
        assert_eq!(solver.eval_n(&v, 1)?, values(&ctx, 42, 1)?);
        assert_eq!(exact_calls.get(), 1);
        Ok(())
    }

    #[test]
    fn test_approximate_first_accessors() {
        let ctx = Context::new();
        let solver = HybridSolver::new(&ctx, ScriptedSolver::new(&ctx), ScriptedSolver::new(&ctx));
        assert!(!solver.approximate_first());
        let solver = HybridSolver::new_with_options(
            &ctx,
            ScriptedSolver::new(&ctx),
            ScriptedSolver::new(&ctx),
            true,
        );
        assert!(solver.approximate_first());
    }

    /// When the approximation is exhaustive (fewer than n+1 solutions), it is
    /// used directly and the exact backend is never asked (mirrors
    /// test_approximate_first_exhaustive).
    #[test]
    fn test_approximate_first_exhaustive_skips_exact() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 253, 3)?;
        let exact = ScriptedSolver::new(&ctx);
        let exact_calls = exact.eval_calls.clone();
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        let x = ctx.bvs("x", 8)?;
        assert_eq!(solver.eval_n(&x, 10)?, values(&ctx, 253, 3)?);
        assert_eq!(exact_calls.get(), 0);
        Ok(())
    }

    /// When the approximation is inexact and a constraint mentions the
    /// expression, the exact backend refines the result if it found fewer
    /// solutions.
    #[test]
    fn test_approximate_first_refined_by_exact() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 0, 10)?; // more than n+1: inexact
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 254, 2)?; // exact knows only 2 solutions
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        // The constraint mentions x, so refinement is possible.
        let x = ctx.bvs("x", 8)?;
        solver.add(&ctx.ugt(&x, &ctx.bvv(BitVec::from((253, 8)))?)?)?;

        assert_eq!(solver.eval_n(&x, 4)?, values(&ctx, 254, 2)?);
        Ok(())
    }

    /// When no constraint mentions the expression, the (inexact)
    /// approximation is used as-is, truncated to n.
    #[test]
    fn test_approximate_first_unconstrained_keeps_approximation() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 0, 10)?;
        let exact = ScriptedSolver::new(&ctx);
        let exact_calls = exact.eval_calls.clone();
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        // Constraint mentions y, not x: no refinement for x.
        let y = ctx.bvs("y", 8)?;
        solver.add(&ctx.ugt(&y, &ctx.bvv(BitVec::from((3, 8)))?)?)?;

        let x = ctx.bvs("x", 8)?;
        assert_eq!(solver.eval_n(&x, 4)?, values(&ctx, 0, 4)?);
        assert_eq!(exact_calls.get(), 0);
        Ok(())
    }

    /// When the exact backend cannot narrow the approximation (it finds at
    /// least as many solutions), the approximation is kept, truncated to n.
    #[test]
    fn test_approximate_first_exact_no_better() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 0, 10)?;
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 100, 10)?;
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        let x = ctx.bvs("x", 8)?;
        solver.add(&ctx.ugt(&x, &ctx.bvv(BitVec::from((3, 8)))?)?)?;

        assert_eq!(solver.eval_n(&x, 4)?, values(&ctx, 0, 4)?);
        Ok(())
    }

    /// A failing or empty approximation falls straight through to exact.
    #[test]
    fn test_approximate_first_falls_back_on_failure() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.fail_eval = true;
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 5, 2)?;
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        let x = ctx.bvs("x", 8)?;
        assert_eq!(solver.eval_n(&x, 4)?, values(&ctx, 5, 2)?);

        solver.approximate_mut().fail_eval = false;
        solver.approximate_mut().solutions = Vec::new();
        assert_eq!(solver.eval_n(&x, 4)?, values(&ctx, 5, 2)?);
        Ok(())
    }

    /// n <= 2 does not trigger the approximate-first path even when enabled
    /// (mirrors test_small_n_stays_exact).
    #[test]
    fn test_approximate_first_small_n_stays_exact() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut approx = ScriptedSolver::new(&ctx);
        approx.solutions = values(&ctx, 0, 10)?;
        let mut exact = ScriptedSolver::new(&ctx);
        exact.solutions = values(&ctx, 7, 1)?;
        let mut solver = HybridSolver::new_with_options(&ctx, approx, exact, true);

        let x = ctx.bvs("x", 8)?;
        // The normal (verify-against-exact) path returns the exact result.
        assert_eq!(solver.eval_n(&x, 1)?, values(&ctx, 7, 1)?);
        assert_eq!(solver.eval_n(&x, 2)?, values(&ctx, 7, 1)?);
        Ok(())
    }
}
