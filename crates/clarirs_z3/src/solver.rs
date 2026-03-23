use crate::astext::{AstExtZ3, DynamicExt};
use clarirs_core::ast::bitvec::BitVecOpExt;
use clarirs_core::prelude::*;
use std::collections::HashMap;
use z3::ast::Dynamic;

#[derive(Clone, Debug)]
pub struct Z3Solver<'c> {
    ctx: &'c Context<'c>,
    assertions: Vec<BoolAst<'c>>,
    timeout: Option<u32>,
    unsat_core: bool,
    // Maps constraint index to tracking variable
    tracking_vars: HashMap<usize, BoolAst<'c>>,
}

impl<'c> Z3Solver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self::new_with_options(ctx, None, false)
    }

    pub fn new_with_timeout(ctx: &'c Context<'c>, timeout: Option<u32>) -> Self {
        Self::new_with_options(ctx, timeout, false)
    }

    pub fn new_with_options(ctx: &'c Context<'c>, timeout: Option<u32>, unsat_core: bool) -> Self {
        Self {
            ctx,
            assertions: vec![],
            timeout,
            unsat_core,
            tracking_vars: HashMap::new(),
        }
    }

    /// Get the unsat core from the last unsatisfiable check.
    /// Returns a vector of constraint indices that form the unsat core.
    ///
    /// This method only works if the solver was created with unsat_core enabled
    /// and the last satisfiability check returned UNSAT.
    pub fn unsat_core(&mut self) -> Result<Vec<usize>, ClarirsError> {
        if !self.unsat_core {
            return Err(ClarirsError::UnsupportedOperation(
                "Unsat core tracking is not enabled. Use new_with_options with unsat_core=true"
                    .to_string(),
            ));
        }

        let z3_solver = self.make_filled_solver()?;

        // Check if UNSAT
        if z3_solver.check() != z3::SatResult::Unsat {
            return Err(ClarirsError::UnsupportedOperation(
                "Can only get unsat core after an UNSAT result".to_string(),
            ));
        }

        let core_asts = z3_solver.get_unsat_core();
        let mut core_indices = Vec::new();

        // Build a reverse map from tracking variable to index
        let mut track_to_idx: HashMap<String, usize> = HashMap::new();
        for (idx, track_var) in &self.tracking_vars {
            // Extract the variable name
            if let Some(vars) = track_var.variables().iter().next() {
                track_to_idx.insert(vars.to_string(), *idx);
            }
        }

        for core_ast in &core_asts {
            // Convert the Z3 AST back to a BoolAst to get its variable name
            let bool_ast = BoolAst::from_z3(self.ctx, Dynamic::from(core_ast.clone()))?;
            if let Some(vars) = bool_ast.variables().iter().next()
                && let Some(idx) = track_to_idx.get(&vars.to_string())
            {
                core_indices.push(*idx);
            }
        }

        Ok(core_indices)
    }
}

impl<'c> HasContext<'c> for Z3Solver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Z3Solver<'c> {
    fn optimize_eval(
        z3_optimize: &z3::Optimize,
        expr: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        if z3_optimize.check(&[]) != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }
        let model = z3_optimize
            .get_model()
            .ok_or_else(|| ClarirsError::BackendError("Z3", "failed to get model".to_string()))?;
        let eval_result = Self::eval_model(&model, &expr.to_z3()?)?;
        match DynAst::from_z3(expr.context(), eval_result)? {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn optimize_unsigned(
        &self,
        expr: &BitVecAst<'c>,
        minimize: bool,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        let z3_optimize = self.mk_filled_optimize()?;
        let expr_z3 = expr.to_z3()?;
        if minimize {
            z3_optimize.minimize(&expr_z3);
        } else {
            z3_optimize.maximize(&expr_z3);
        }
        Self::optimize_eval(&z3_optimize, expr)
    }

    fn optimize_signed(
        &self,
        expr: &BitVecAst<'c>,
        minimize: bool,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        let z3_optimize = self.mk_filled_optimize()?;
        let size = expr.size();

        // Extract the sign bit
        let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
        // For signed minimization, the sign bit should be 1 (for negative numbers)
        // For signed maximization, the sign bit should be 0 (for positive numbers)
        let target_bit = self.ctx.bvv_prim_with_size(u64::from(minimize), 1)?;

        // Create a target variable equal to the expression
        let label = if minimize { "min" } else { "max" };
        let target = self
            .ctx
            .bvs(format!("{label}_signed_target_{size}"), size)?;
        let eq_z3 = self.ctx.eq_(&target, expr)?.to_z3()?;
        z3_optimize.assert(&eq_z3.to_bool()?);

        // First, maximize the sign bit preference with a high weight
        // This will prefer the correct sign for min/max
        let sign_z3 = self.ctx.eq_(&sign_bit, &target_bit)?.to_z3()?;
        z3_optimize.assert_soft(&sign_z3.to_bool()?, 1000000, None);

        // Then minimize/maximize the target value
        let target_z3 = target.to_z3()?;
        if minimize {
            z3_optimize.minimize(&target_z3);
        } else {
            z3_optimize.maximize(&target_z3);
        }

        Self::optimize_eval(&z3_optimize, expr)
    }

    fn eval_dyn_n(&self, expr: DynAst<'c>, n: u32) -> Result<Vec<DynAst<'c>>, ClarirsError> {
        // Simplify and check if concrete
        let expr = Self::simplify_dynast(&expr.simplify()?)?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        // Convert to Z3 once
        let z3_expr = expr.to_z3()?;

        // Create and fill the Z3 solver once
        let z3_solver = z3::Solver::new();
        for assertion in &self.assertions {
            z3_solver.assert(&assertion.to_z3()?.to_bool()?);
        }

        let mut results = Vec::new();
        for _ in 0..n {
            if z3_solver.check() != z3::SatResult::Sat {
                break;
            }
            let model = z3_solver.get_model().ok_or_else(|| {
                ClarirsError::BackendError("Z3", "failed to get model".to_string())
            })?;
            let solution = DynAst::from_z3(self.ctx, Self::eval_model(&model, &z3_expr)?)?;
            let neq_constraint = match (&expr, &solution) {
                (DynAst::Boolean(a), DynAst::Boolean(b)) => self.ctx.neq(a, b)?,
                (DynAst::BitVec(a), DynAst::BitVec(b)) => self.ctx.neq(a, b)?,
                (DynAst::Float(a), DynAst::Float(b)) => self.ctx.neq(a, b)?,
                (DynAst::String(a), DynAst::String(b)) => self.ctx.neq(a, b)?,
                _ => unreachable!(),
            };
            // Add constraint to exclude this solution
            z3_solver.assert(&neq_constraint.to_z3()?.to_bool()?);
            results.push(solution);
        }
        Ok(results)
    }

    fn make_filled_solver(&self) -> Result<z3::Solver, ClarirsError> {
        let z3_solver = z3::Solver::new();

        let mut params = z3::Params::new();
        if let Some(timeout) = self.timeout {
            params.set_u32("timeout", timeout);
        }
        if self.unsat_core {
            params.set_bool("unsat_core", true);
        }
        z3_solver.set_params(&params);

        for (idx, assertion) in self.assertions.iter().enumerate() {
            let converted = assertion.to_z3()?;
            let bool_ast = converted.to_bool()?;
            if self.unsat_core {
                // Use assert_and_track with a tracking variable
                if let Some(track_var) = self.tracking_vars.get(&idx) {
                    let track_z3 = track_var.to_z3()?;
                    let track_bool = track_z3.to_bool()?;
                    z3_solver.assert_and_track(&bool_ast, &track_bool);
                } else {
                    z3_solver.assert(&bool_ast);
                }
            } else {
                z3_solver.assert(&bool_ast);
            }
        }

        Ok(z3_solver)
    }

    fn mk_filled_optimize(&self) -> Result<z3::Optimize, ClarirsError> {
        let z3_optimize = z3::Optimize::new();

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            let bool_ast = converted.to_bool()?;
            z3_optimize.assert(&bool_ast);
        }

        Ok(z3_optimize)
    }

    fn make_model(&self) -> Result<z3::Model, ClarirsError> {
        let z3_solver = self.make_filled_solver()?;
        if z3_solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        z3_solver
            .get_model()
            .ok_or_else(|| ClarirsError::BackendError("Z3", "failed to get model".to_string()))
    }

    fn simplify_dynast(expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        Ok(match expr {
            DynAst::Boolean(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::BitVec(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::Float(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::String(expr) => DynAst::from(&expr.simplify_z3()?),
        })
    }

    fn eval_model(model: &z3::Model, expr_z3: &Dynamic) -> Result<Dynamic, ClarirsError> {
        model
            .eval(expr_z3, true)
            .ok_or_else(|| ClarirsError::BackendError("Z3", "Model evaluation failed".to_string()))
    }

    fn eval(&self, expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let expr = Z3Solver::simplify_dynast(&expr.simplify()?)?;

        // If the expression is concrete, we can return it directly
        if expr.concrete() {
            return Ok(expr);
        }

        // Expression is not concrete, we need to get a model from Z3 and
        // replace the variables with the values from the model
        let model = self.make_model()?;
        let expr_z3 = expr.to_z3()?;
        let eval_result = Self::eval_model(&model, &expr_z3)?;
        DynAst::from_z3(expr.context(), eval_result)
    }
}

impl<'c> Solver<'c> for Z3Solver<'c> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        let idx = self.assertions.len();
        self.assertions.push(constraint.clone());

        // Create a tracking variable if unsat_core is enabled
        if self.unsat_core {
            let track_name = format!("__track_{idx}");
            let track_var = self.ctx.bools(&track_name)?;
            self.tracking_vars.insert(idx, track_var);
        }

        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.assertions.clear();
        self.tracking_vars.clear();
        Ok(())
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(self.assertions.clone())
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        self.assertions = self
            .assertions
            .iter()
            .filter_map(|c| {
                let simplified = c.simplify_z3().ok()?;
                if simplified.is_true() {
                    None
                } else {
                    Some(Ok(simplified))
                }
            })
            .collect::<Result<Vec<_>, ClarirsError>>()?;
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        let z3_solver = self.make_filled_solver()?;
        Ok(z3_solver.check() == z3::SatResult::Sat)
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        match self.eval(&DynAst::from(expr))? {
            DynAst::Boolean(a) => Ok(a),
            _ => unreachable!(),
        }
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        match self.eval(&DynAst::from(expr))? {
            DynAst::BitVec(a) => Ok(a),
            _ => unreachable!(),
        }
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        match self.eval(&DynAst::from(expr))? {
            DynAst::Float(a) => Ok(a),
            _ => unreachable!(),
        }
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        match self.eval(&DynAst::from(expr))? {
            DynAst::String(a) => Ok(a),
            _ => unreachable!(),
        }
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let expr = expr.simplify_z3()?;
        Ok(expr.concrete() && expr.is_true())
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let expr = expr.simplify_z3()?;
        Ok(expr.concrete() && expr.is_false())
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let mut solver = self.clone();
        solver.add(expr)?;
        solver.satisfiable()
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let mut solver = self.clone();
        solver.add(&self.context().not(expr)?)?;
        solver.satisfiable()
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.optimize_unsigned(expr, true)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.optimize_unsigned(expr, false)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.optimize_signed(expr, true)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.optimize_signed(expr, false)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        self.eval_dyn_n(DynAst::from(expr), n)?
            .into_iter()
            .map(|d| match d {
                DynAst::Boolean(a) => Ok(a),
                _ => unreachable!(),
            })
            .collect()
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        self.eval_dyn_n(DynAst::from(expr), n)?
            .into_iter()
            .map(|d| match d {
                DynAst::BitVec(a) => Ok(a),
                _ => unreachable!(),
            })
            .collect()
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        self.eval_dyn_n(DynAst::from(expr), n)?
            .into_iter()
            .map(|d| match d {
                DynAst::Float(a) => Ok(a),
                _ => unreachable!(),
            })
            .collect()
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        self.eval_dyn_n(DynAst::from(expr), n)?
            .into_iter()
            .map(|d| match d {
                DynAst::String(a) => Ok(a),
                _ => unreachable!(),
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solver_simple() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.neq(&x, &y)?)?;

        let x_val = solver.eval_bool(&x).unwrap();
        let y_val = solver.eval_bool(&y).unwrap();

        assert_ne!(x_val, y_val);

        Ok(())
    }

    #[test]
    fn test_solver_unsat() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.eq_(&x, &y)?)?;
        solver.add(&ctx.neq(&x, &y)?)?;

        assert!(!solver.satisfiable()?);

        Ok(())
    }

    #[test]
    fn test_solver_bool() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.not(&ctx.eq_(&x, &y)?)?).unwrap();
        solver.add(&ctx.eq_(&x, &ctx.true_()?)?).unwrap();

        let x_val = solver.eval_bool(&x).unwrap();
        let y_val = solver.eval_bool(&y).unwrap();

        assert_ne!(x_val, y_val);
        assert!(x_val.is_true());
        assert!(y_val.is_false());

        Ok(())
    }

    mod test_eval_bool {
        use super::*;

        #[test]
        fn test_eval_bool_symbol() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bools("x")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;

            let result = solver.eval_bool(&x)?;
            assert!(result.is_true());

            Ok(())
        }

        #[test]
        fn test_eval_bool_value() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let t = ctx.true_()?;
            let f = ctx.false_()?;

            assert!(solver.satisfiable()?);
            let t_result = solver.eval_bool(&t)?;
            let f_result = solver.eval_bool(&f)?;

            assert!(t_result.is_true());
            assert!(f_result.is_false());

            Ok(())
        }

        #[test]
        fn test_eval_bool_not() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete value
            let t = ctx.true_()?;
            let not_t = ctx.not(&t)?;
            let result = solver.eval_bool(&not_t)?;
            assert!(result.is_false());

            // Test with symbolic value
            let x = ctx.bools("x")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            let not_x = ctx.not(&x)?;
            let result = solver.eval_bool(&not_x)?;
            assert!(result.is_false());

            Ok(())
        }

        #[test]
        fn test_eval_bool_and() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values - truth table
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.and2(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.and2(&t, &f)?)?;
            let ft = solver.eval_bool(&ctx.and2(&f, &t)?)?;
            let ff = solver.eval_bool(&ctx.and2(&f, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());
            assert!(ft.is_false());
            assert!(ff.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.false_()?)?)?;

            let result = solver.eval_bool(&ctx.and2(&x, &y)?)?;
            assert!(result.is_false());

            Ok(())
        }

        #[test]
        fn test_eval_bool_or() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values - truth table
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.or2(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.or2(&t, &f)?)?;
            let ft = solver.eval_bool(&ctx.or2(&f, &t)?)?;
            let ff = solver.eval_bool(&ctx.or2(&f, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_true());
            assert!(ft.is_true());
            assert!(ff.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.false_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?;

            let result = solver.eval_bool(&ctx.or2(&x, &y)?)?;
            assert!(result.is_true());

            Ok(())
        }

        #[test]
        fn test_eval_bool_xor() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values - truth table
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.xor(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.xor(&t, &f)?)?;
            let ft = solver.eval_bool(&ctx.xor(&f, &t)?)?;
            let ff = solver.eval_bool(&ctx.xor(&f, &f)?)?;

            assert!(tt.is_false());
            assert!(tf.is_true());
            assert!(ft.is_true());
            assert!(ff.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?;

            let result = solver.eval_bool(&ctx.xor(&x, &y)?)?;
            assert!(result.is_false());

            Ok(())
        }

        #[test]
        fn test_eval_bool_eq() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.eq_(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.eq_(&t, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?;

            let result = solver.eval_bool(&ctx.eq_(&x, &y)?)?;
            assert!(result.is_true());

            Ok(())
        }

        #[test]
        fn test_eval_bool_neq() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.neq(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.neq(&t, &f)?)?;

            assert!(tt.is_false());
            assert!(tf.is_true());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.false_()?)?)?;

            let result = solver.eval_bool(&ctx.neq(&x, &y)?)?;
            assert!(result.is_true());

            Ok(())
        }

        #[test]
        fn test_eval_bool_if() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Test with concrete values
            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.ite(&t, &t, &f)?)?;
            let tf = solver.eval_bool(&ctx.ite(&f, &t, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());

            // Test with symbolic values
            let c = ctx.bools("c")?;
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;

            solver.add(&ctx.eq_(&c, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.false_()?)?)?;

            let result = solver.eval_bool(&ctx.ite(c, x, y)?)?;
            assert!(result.is_true());

            Ok(())
        }
    }

    mod test_bitvec_optimize {
        use super::*;

        #[test]
        fn test_min_unsigned_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Using a concrete value should return the same value
            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.min_unsigned(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Using a concrete value should return the same value
            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.max_unsigned(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_min_unsigned_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 64)?;

            // Add constraints: 10 <= x <= 20
            let lower_bound = ctx.bvv_prim(10u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.uge(&x, &lower_bound)?)?;
            solver.add(&ctx.ule(&x, &upper_bound)?)?;

            // Min value should be 10
            let result = solver.min_unsigned(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 64)?;

            // Add constraints: 10 <= x <= 20
            let lower_bound = ctx.bvv_prim(10u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.uge(&x, &lower_bound)?)?;
            solver.add(&ctx.ule(&x, &upper_bound)?)?;

            // Max value should be 20
            let result = solver.max_unsigned(&x)?;
            assert_eq!(result, upper_bound);

            Ok(())
        }

        #[test]
        fn test_min_unsigned_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create variables
            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            // Add constraints:
            // x must be greater than 5
            // y must be less than 10
            // x + y must be even (lowest bit is 0)
            let five = ctx.bvv_prim(5u8)?;
            let ten = ctx.bvv_prim(10u8)?;

            solver.add(&ctx.ugt(&x, &five)?)?;
            solver.add(&ctx.ult(&y, &ten)?)?;

            // x + y must be even
            let sum = ctx.add(&x, &y)?;
            let zero = ctx.bvv_prim_with_size(0u64, 1)?;
            solver.add(&ctx.eq_(&ctx.extract(&sum, 0, 0)?, &zero)?)?;

            // Find min value of x
            let result = solver.min_unsigned(&x)?;

            // Min value should be 6
            // Because x > 5, and if x = 6 and y = 0, then 6+0=6 which is even
            let six = ctx.bvv_prim(6u8)?;
            assert_eq!(result, six);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create variables
            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            // Add constraints:
            // x must be less than 100
            // y must be greater than 20
            // x must be greater than y
            let hundred = ctx.bvv_prim(100u8)?;
            let twenty = ctx.bvv_prim(20u8)?;

            solver.add(&ctx.ult(&x, &hundred)?)?;
            solver.add(&ctx.ugt(&y, &twenty)?)?;
            solver.add(&ctx.ugt(&x, &y)?)?;

            // Find max value of x
            let result = solver.max_unsigned(&x)?;

            // Max value should be 99 (since x < 100)
            let ninety_nine = ctx.bvv_prim(99u8)?;
            assert_eq!(result, ninety_nine);

            Ok(())
        }

        // Tests for signed bitvector operations

        #[test]
        fn test_min_signed_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Using a concrete value should return the same value
            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.min_signed(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_max_signed_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Using a concrete value should return the same value
            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.max_signed(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_min_signed_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 64)?;

            // Add constraints: -10 <= x <= 20 (in signed interpretation)
            // -10 in 64-bit two's complement is 0xfffffffffffffff6
            let lower_bound = ctx.bvv_prim(0xfffffffffffffff6u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            // Min value should be -10
            let result = solver.min_signed(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_signed_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 64)?;

            // Add constraints: -10 <= x <= 20 (in signed interpretation)
            // -10 in 64-bit two's complement is 0xfffffffffffffff6
            let lower_bound = ctx.bvv_prim(0xfffffffffffffff6u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            // Max value should be 20
            let result = solver.max_signed(&x)?;
            assert_eq!(result, upper_bound);

            Ok(())
        }

        #[test]
        fn test_min_signed_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create variables
            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            // Add constraints:
            // x must be greater than -5 (signed)
            // y must be less than 10 (signed)
            // x + y must be even (lowest bit is 0)

            // -5 in 8-bit two's complement is 0xfb (251 in unsigned)
            let neg_five = ctx.bvv_prim(0xfbu8)?;
            let ten = ctx.bvv_prim(10u8)?;

            solver.add(&ctx.sgt(&x, &neg_five)?)?;
            solver.add(&ctx.slt(&y, &ten)?)?;

            // x + y must be even
            let sum = ctx.add(&x, &y)?;
            let zero = ctx.bvv_prim_with_size(0u64, 1)?;
            solver.add(&ctx.eq_(&ctx.extract(&sum, 0, 0)?, &zero)?)?;

            // Find min value of x
            let result = solver.min_signed(&x)?;

            // Min value should be -4 (0xfc in 8-bit two's complement)
            // Because x > -5, and if x = -4 and y = 0, then -4+0=-4 which is even
            let neg_four = ctx.bvv_prim(0xfcu8)?;
            assert_eq!(result, neg_four);

            Ok(())
        }

        #[test]
        fn test_max_signed_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create variables
            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            // Add constraints:
            // x must be less than 100 (signed)
            // y must be greater than -20 (signed)
            // x must be greater than y (signed)
            let hundred = ctx.bvv_prim(100u8)?;

            // -20 in 8-bit two's complement is 0xec (236 in unsigned)
            let neg_twenty = ctx.bvv_prim(0xecu8)?;

            solver.add(&ctx.slt(&x, &hundred)?)?;
            solver.add(&ctx.sgt(&y, &neg_twenty)?)?;
            solver.add(&ctx.sgt(&x, &y)?)?;

            // Find max value of x
            let result = solver.max_signed(&x)?;

            // Max value should be 99 (since x < 100)
            let ninety_nine = ctx.bvv_prim(99u8)?;
            assert_eq!(result, ninety_nine);

            Ok(())
        }

        #[test]
        fn test_min_signed_negative_range() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 8)?;

            // Add constraints: -100 <= x <= -10 (in signed interpretation)
            // -100 in 8-bit two's complement is 0x9c (156 in unsigned)
            // -10 in 8-bit two's complement is 0xf6 (246 in unsigned)
            let lower_bound = ctx.bvv_prim(0x9cu8)?;
            let upper_bound = ctx.bvv_prim(0xf6u8)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            // Min value should be -100
            let result = solver.min_signed(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_signed_negative_range() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            // Create a variable with constraints
            let x = ctx.bvs("x", 8)?;

            // Add constraints: -100 <= x <= -10 (in signed interpretation)
            // -100 in 8-bit two's complement is 0x9c (156 in unsigned)
            // -10 in 8-bit two's complement is 0xf6 (246 in unsigned)
            let lower_bound = ctx.bvv_prim(0x9cu8)?;
            let upper_bound = ctx.bvv_prim(0xf6u8)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            // Max value should be -10
            let result = solver.max_signed(&x)?;
            assert_eq!(result, upper_bound);

            Ok(())
        }
    }

    #[test]
    fn test_unsat_core_simple() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new_with_options(&ctx, None, true);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        // Add contradictory constraints
        solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?; // constraint 0
        solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?; // constraint 1
        solver.add(&ctx.eq_(&x, &y)?)?; // constraint 2
        solver.add(&ctx.neq(&x, &y)?)?; // constraint 3 - contradicts with 0, 1, and 2

        // Should be unsat
        assert!(!solver.satisfiable()?);

        // Get unsat core
        let core = solver.unsat_core()?;

        // The core should contain the contradictory constraints
        // At minimum, it should contain constraint 2 and 3 (or 0, 1, and 3)
        assert!(!core.is_empty());
        assert!(core.len() <= 4); // Should be a subset of all constraints

        Ok(())
    }

    #[test]
    fn test_unsat_core_minimal() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new_with_options(&ctx, None, true);

        let x = ctx.bvs("x", 8)?;

        // Add constraints
        let c0 = ctx.ugt(&x, &ctx.bvv_prim(10u8)?)?; // x > 10
        let c1 = ctx.ult(&x, &ctx.bvv_prim(5u8)?)?; // x < 5 - contradicts c0
        let c2 = ctx.ugt(&x, &ctx.bvv_prim(0u8)?)?; // x > 0 - doesn't contribute to unsat

        solver.add(&c0)?; // constraint 0
        solver.add(&c1)?; // constraint 1
        solver.add(&c2)?; // constraint 2

        // Should be unsat
        assert!(!solver.satisfiable()?);

        // Get unsat core
        let core = solver.unsat_core()?;

        // The core should contain constraints 0 and 1, but not necessarily 2
        assert!(!core.is_empty());
        assert!(core.contains(&0));
        assert!(core.contains(&1));

        Ok(())
    }

    #[test]
    fn test_unsat_core_not_enabled() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new(&ctx); // unsat_core not enabled

        let x = ctx.bools("x")?;

        solver.add(&x)?;
        solver.add(&ctx.not(&x)?)?;

        // Should be unsat
        assert!(!solver.satisfiable()?);

        // Getting unsat core should fail because it's not enabled
        assert!(solver.unsat_core().is_err());

        Ok(())
    }

    #[test]
    fn test_unsat_core_on_sat() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new_with_options(&ctx, None, true);

        let x = ctx.bools("x")?;
        solver.add(&x)?;

        // Should be sat
        assert!(solver.satisfiable()?);

        // Getting unsat core on a SAT result should fail
        assert!(solver.unsat_core().is_err());

        Ok(())
    }
}
