use std::collections::BTreeSet;

use crate::prelude::*;

pub trait Solver<'c>: Clone + HasContext<'c> {
    // Constraint management
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError>;

    fn clear(&mut self) -> Result<(), ClarirsError>;

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError>;

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

    /// Evaluate an expression in the current model.
    ///
    /// If the constraints are unsatisfiable, an error is returned.
    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        let mut results = self.eval_bool_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let mut results = self.eval_bitvec_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        let mut results = self.eval_float_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }
    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        let mut results = self.eval_string_n(expr, 1)?;
        results.pop().ok_or(ClarirsError::Unsat)
    }

    /// Check if an expression is true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression is false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be true in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.true_()`
    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Check if an expression could be false in the current model. If the constraints are unsatisfiable, an
    /// error is returned. Equivalent to `eval(expr) == ctx.false_()`
    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as unsigned.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the minimum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Get the maximum value of an expression in the current model, interpreting the bitvector as signed.
    /// If the constraints are unsatisfiable, an error is returned.
    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError>;

    /// Find multiple solutions for a boolean expression
    fn eval_bool_n(&mut self, expr: &BoolAst<'c>, n: u32)
    -> Result<Vec<BoolAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a bitvector expression
    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a float expression
    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError>;

    /// Find multiple solutions for a string expression
    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError>;
}

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
    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(Vec::new())
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        // ConcreteSolver has no constraints to simplify
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
        expr.simplify_ext(false, true)
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify_ext(false, true)
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify_ext(false, true)
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation(
                "Concrete solver does not support symbolic expressions".to_string(),
            ));
        }
        expr.simplify_ext(false, true)
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_true())
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_false())
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_true())
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Ok(expr.simplify()?.is_false())
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.eval_bitvec(expr)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        let val = self.eval_bool(expr)?;
        Ok(vec![val])
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        let val = self.eval_bitvec(expr)?;
        Ok(vec![val])
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        let val = self.eval_float(expr)?;
        Ok(vec![val])
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        let val = self.eval_string(expr)?;
        Ok(vec![val])
    }
}

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
}

impl<'c, A: Solver<'c>, E: Solver<'c>> HybridSolver<'c, A, E> {
    /// Create a new hybrid solver with the given approximate and exact backends.
    pub fn new(ctx: &'c Context<'c>, approximate: A, exact: E) -> Self {
        Self {
            approximate,
            exact,
            ctx,
        }
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
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        // Add constraints to both backends. The approximate solver may ignore
        // them (as VSA does), but the exact solver tracks them.
        let _ = self.approximate.add(constraint);
        self.exact.add(constraint)
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        let _ = self.approximate.clear();
        self.exact.clear()
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
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

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.is_true(expr);
        }
        // For symbolic expressions, always consult exact solver
        self.exact.is_true(expr)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.is_false(expr);
        }
        self.exact.is_false(expr)
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.has_true(expr);
        }
        // If approximate says definitely true, trust it (over-approximation is safe here)
        match self.approximate.has_true(expr) {
            Ok(true) => Ok(true),
            _ => self.exact.has_true(expr),
        }
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.has_false(expr);
        }
        match self.approximate.has_false(expr) {
            Ok(true) => Ok(true),
            _ => self.exact.has_false(expr),
        }
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.min_unsigned(expr);
        }
        self.exact.min_unsigned(expr)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.max_unsigned(expr);
        }
        self.exact.max_unsigned(expr)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.min_signed(expr);
        }
        self.exact.min_signed(expr)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if !expr.symbolic() {
            return self.approximate.max_signed(expr);
        }
        self.exact.max_signed(expr)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if !expr.symbolic() {
            return self.approximate.eval_bool_n(expr, n);
        }
        // Try approximate first, fall back to exact for symbolic
        match self.approximate.eval_bool_n(expr, n) {
            Ok(approx_results) if !approx_results.is_empty() => {
                match self.exact.eval_bool_n(expr, n) {
                    Ok(exact) => Ok(exact),
                    Err(_) => Ok(approx_results),
                }
            }
            _ => self.exact.eval_bool_n(expr, n),
        }
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if !expr.symbolic() {
            return self.approximate.eval_bitvec_n(expr, n);
        }
        match self.approximate.eval_bitvec_n(expr, n) {
            Ok(approx_results) if !approx_results.is_empty() => {
                match self.exact.eval_bitvec_n(expr, n) {
                    Ok(exact) => Ok(exact),
                    Err(_) => Ok(approx_results),
                }
            }
            _ => self.exact.eval_bitvec_n(expr, n),
        }
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if !expr.symbolic()
            && let Ok(result) = self.approximate.eval_float_n(expr, n)
        {
            return Ok(result);
        }
        self.exact.eval_float_n(expr, n)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if !expr.symbolic()
            && let Ok(result) = self.approximate.eval_string_n(expr, n)
        {
            return Ok(result);
        }
        self.exact.eval_string_n(expr, n)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;

    use super::*;

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

        let a = ctx.bvv_prim(10u8)?;
        let b = ctx.bvv_prim(20u8)?;
        let sum = ctx.add(&a, &b)?;
        let result = solver.eval_bitvec(&sum)?;
        assert_eq!(result, ctx.bvv_prim(30u8)?);

        assert!(solver.satisfiable()?);

        Ok(())
    }

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
