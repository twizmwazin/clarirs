use crate::astext::AstExtZ3;
use crate::{Z3_CONTEXT, check_z3_error};
use clarirs_core::ast::bitvec::BitVecOpExt;
use clarirs_core::prelude::*;
use crate::z3_compat as z3;
use std::collections::HashMap;

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
        Self {
            ctx,
            assertions: vec![],
            timeout: None,
            unsat_core: false,
            tracking_vars: HashMap::new(),
        }
    }

    pub fn new_with_timeout(ctx: &'c Context<'c>, timeout: Option<u32>) -> Self {
        Self {
            ctx,
            assertions: vec![],
            timeout,
            unsat_core: false,
            tracking_vars: HashMap::new(),
        }
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
        if solver_check(z3_solver)? != z3::Lbool::False {
            return Err(ClarirsError::UnsupportedOperation(
                "Can only get unsat core after an UNSAT result".to_string(),
            ));
        }

        let core_vector = Z3_CONTEXT.with(|&ctx| unsafe {
            let v = z3::solver_get_unsat_core(ctx, z3_solver);
            check_z3_error()?;
            Ok::<_, ClarirsError>(v)
        })?;
        let core_size = Z3_CONTEXT.with(|&ctx| unsafe { z3::ast_vector_size(ctx, core_vector) });

        let mut core_indices = Vec::new();

        // Build a reverse map from tracking variable to index
        let mut track_to_idx: HashMap<String, usize> = HashMap::new();
        for (idx, track_var) in &self.tracking_vars {
            if let Some(vars) = track_var.variables().iter().next() {
                track_to_idx.insert(vars.to_string(), *idx);
            }
        }

        for i in 0..core_size {
            let core_ast = Z3_CONTEXT.with(|&ctx| unsafe {
                let ast = z3::ast_vector_get(ctx, core_vector, i);
                check_z3_error()?;
                Ok::<_, ClarirsError>(ast)
            })?;
            let bool_ast = BoolAst::from_z3(self.ctx, core_ast)?;
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

/// Create a Z3 solver, check for errors, and return the raw handle.
fn mk_solver() -> Result<z3::Solver, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let solver = z3::mk_solver(ctx);
        z3::solver_inc_ref(ctx, solver);
        check_z3_error()?;
        Ok(solver)
    })
}

/// Assert a constraint in the solver.
fn solver_assert(solver: z3::Solver, ast: z3::Ast) -> Result<(), ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_assert(ctx, solver, ast) });
    check_z3_error()
}

/// Assert and track a constraint.
fn solver_assert_and_track(solver: z3::Solver, ast: z3::Ast, track: z3::Ast) -> Result<(), ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_assert_and_track(ctx, solver, ast, track) });
    check_z3_error()
}

/// Check satisfiability.
fn solver_check(solver: z3::Solver) -> Result<z3::Lbool, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let result = z3::solver_check(ctx, solver);
        check_z3_error()?;
        Ok(result)
    })
}

/// Get the model from a solver.
fn solver_get_model(solver: z3::Solver) -> Result<z3::Model, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let model = z3::solver_get_model(ctx, solver);
        z3::model_inc_ref(ctx, model);
        check_z3_error()?;
        Ok(model)
    })
}

/// Evaluate an AST in a model.
fn model_eval(model: z3::Model, ast: z3::Ast) -> Result<z3::Ast, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let mut eval_result = std::mem::MaybeUninit::<z3::Ast>::uninit();
        let eval_ret = z3::model_eval(ctx, model, ast, true, eval_result.as_mut_ptr());
        check_z3_error()?;
        if !eval_ret {
            return Err(ClarirsError::BackendError(
                "Z3",
                "Model evaluation failed".into(),
            ));
        }
        Ok(eval_result.assume_init())
    })
}

/// Create a Z3 optimize instance.
fn mk_optimize() -> Result<z3::Optimize, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let opt = z3::mk_optimize(ctx);
        z3::optimize_inc_ref(ctx, opt);
        check_z3_error()?;
        Ok(opt)
    })
}

/// Assert in optimize.
fn optimize_assert(opt: z3::Optimize, ast: z3::Ast) -> Result<(), ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_assert(ctx, opt, ast) });
    check_z3_error()
}

/// Assert soft in optimize.
fn optimize_assert_soft(opt: z3::Optimize, ast: z3::Ast, weight: u32) -> Result<(), ClarirsError> {
    let weight_string = std::ffi::CString::new(weight.to_string()).map_err(|_| {
        ClarirsError::BackendError("Z3", "Failed to convert weight to CString".into())
    })?;
    Z3_CONTEXT.with(|&ctx| unsafe {
        z3::optimize_assert_soft(ctx, opt, ast, weight_string.as_ptr(), None);
    });
    check_z3_error()
}

/// Minimize in optimize.
fn optimize_minimize(opt: z3::Optimize, ast: z3::Ast) -> Result<(), ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_minimize(ctx, opt, ast) });
    check_z3_error()
}

/// Maximize in optimize.
fn optimize_maximize(opt: z3::Optimize, ast: z3::Ast) -> Result<(), ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_maximize(ctx, opt, ast) });
    check_z3_error()
}

/// Check optimize.
fn optimize_check(opt: z3::Optimize) -> Result<z3::Lbool, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let result = z3::optimize_check(ctx, opt, 0, std::ptr::null());
        check_z3_error()?;
        Ok(result)
    })
}

/// Get model from optimize.
fn optimize_get_model(opt: z3::Optimize) -> Result<z3::Model, ClarirsError> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let model = z3::optimize_get_model(ctx, opt);
        z3::model_inc_ref(ctx, model);
        check_z3_error()?;
        Ok(model)
    })
}

impl<'c> Z3Solver<'c> {
    fn make_filled_solver(&self) -> Result<z3::Solver, ClarirsError> {
        let z3_solver = mk_solver()?;

        // Set params
        Z3_CONTEXT.with(|&ctx| unsafe {
            let params = z3::mk_params(ctx);
            z3::params_inc_ref(ctx, params);
            if let Some(timeout) = self.timeout {
                let key_cstr = std::ffi::CString::new("timeout").unwrap();
                let symbol = z3::mk_string_symbol(ctx, key_cstr.as_ptr());
                z3::params_set_uint(ctx, params, symbol, timeout);
            }
            if self.unsat_core {
                let key_cstr = std::ffi::CString::new("unsat_core").unwrap();
                let symbol = z3::mk_string_symbol(ctx, key_cstr.as_ptr());
                z3::params_set_bool(ctx, params, symbol, true);
            }
            z3::solver_set_params(ctx, z3_solver, params);
            z3::params_dec_ref(ctx, params);
        });
        check_z3_error()?;

        for (idx, assertion) in self.assertions.iter().enumerate() {
            let converted = assertion.to_z3()?;
            if self.unsat_core {
                if let Some(track_var) = self.tracking_vars.get(&idx) {
                    let track_z3 = track_var.to_z3()?;
                    solver_assert_and_track(z3_solver, converted, track_z3)?;
                } else {
                    solver_assert(z3_solver, converted)?;
                }
            } else {
                solver_assert(z3_solver, converted)?;
            }
        }

        Ok(z3_solver)
    }

    fn mk_filled_optimize(&self) -> Result<z3::Optimize, ClarirsError> {
        let opt = mk_optimize()?;

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            optimize_assert(opt, converted)?;
        }

        Ok(opt)
    }

    fn make_model(&self) -> Result<z3::Model, ClarirsError> {
        let z3_solver = self.make_filled_solver()?;
        if solver_check(z3_solver)? != z3::Lbool::True {
            return Err(ClarirsError::Unsat);
        }

        solver_get_model(z3_solver)
    }

    fn simplify_dynast(expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        Ok(match expr {
            DynAst::Boolean(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::BitVec(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::Float(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::String(expr) => DynAst::from(&expr.simplify_z3()?),
        })
    }

    fn eval(&self, expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let expr = Z3Solver::simplify_dynast(&expr.simplify()?)?;

        if expr.concrete() {
            return Ok(expr);
        }

        let model = self.make_model()?;

        DynAst::from_z3(expr.context(), model_eval(model, expr.to_z3()?)?)
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
        Ok(solver_check(z3_solver)? == z3::Lbool::True)
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        let result = self.eval(&DynAst::from(expr))?;
        match result {
            DynAst::Boolean(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let result = self.eval(&DynAst::from(expr))?;
        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        let result = self.eval(&DynAst::from(expr))?;
        match result {
            DynAst::Float(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        let result = self.eval(&DynAst::from(expr))?;
        match result {
            DynAst::String(ast) => Ok(ast),
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
        let opt = self.mk_filled_optimize()?;
        optimize_minimize(opt, expr.to_z3()?)?;
        if optimize_check(opt)? != z3::Lbool::True {
            return Err(ClarirsError::Unsat);
        }

        let model = optimize_get_model(opt)?;
        let result = DynAst::from_z3(expr.context(), model_eval(model, expr.to_z3()?)?)?;

        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let opt = self.mk_filled_optimize()?;
        optimize_maximize(opt, expr.to_z3()?)?;
        if optimize_check(opt)? != z3::Lbool::True {
            return Err(ClarirsError::Unsat);
        }

        let model = optimize_get_model(opt)?;
        let result = DynAst::from_z3(expr.context(), model_eval(model, expr.to_z3()?)?)?;

        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let opt = self.mk_filled_optimize()?;
        let size = expr.size();

        let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
        let one_bit = self.ctx.bvv_prim_with_size(1u64, 1)?;

        let target_name = format!("min_signed_target_{size}");
        let target = self.ctx.bvs(&target_name, size)?;
        let equality = self.ctx.eq_(&target, expr)?;
        optimize_assert(opt, equality.to_z3()?)?;

        let sign_equality = self.ctx.eq_(&sign_bit, &one_bit)?;
        optimize_assert_soft(opt, sign_equality.to_z3()?, 1000000)?;

        optimize_minimize(opt, target.to_z3()?)?;

        if optimize_check(opt)? != z3::Lbool::True {
            return Err(ClarirsError::Unsat);
        }

        let model = optimize_get_model(opt)?;
        let result = DynAst::from_z3(expr.context(), model_eval(model, expr.to_z3()?)?)?;
        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let opt = self.mk_filled_optimize()?;
        let size = expr.size();

        let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
        let zero_bit = self.ctx.bvv_prim_with_size(0u64, 1)?;

        let target_name = format!("max_signed_target_{size}");
        let target = self.ctx.bvs(&target_name, size)?;
        let equality = self.ctx.eq_(&target, expr)?;
        optimize_assert(opt, equality.to_z3()?)?;

        let sign_equality = self.ctx.eq_(&sign_bit, &zero_bit)?;
        optimize_assert_soft(opt, sign_equality.to_z3()?, 1000000)?;

        optimize_maximize(opt, target.to_z3()?)?;

        if optimize_check(opt)? != z3::Lbool::True {
            return Err(ClarirsError::Unsat);
        }

        let model = optimize_get_model(opt)?;
        let result = DynAst::from_z3(expr.context(), model_eval(model, expr.to_z3()?)?)?;
        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        // Simplify and check if concrete
        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        // Convert to Z3 once
        let z3_expr = expr.to_z3()?;

        // Create and fill the Z3 solver once
        let z3_solver = mk_solver()?;

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            solver_assert(z3_solver, converted)?;
        }

        for _ in 0..n {
            if solver_check(z3_solver)? != z3::Lbool::True {
                break;
            }

            let model = solver_get_model(z3_solver)?;
            let eval_result = model_eval(model, z3_expr)?;

            let solution = BoolAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution
            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            solver_assert(z3_solver, z3_neq)?;
        }

        Ok(results)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        // Simplify and check if concrete
        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        // Convert to Z3 once
        let z3_expr = expr.to_z3()?;

        // Create and fill the Z3 solver once
        let z3_solver = mk_solver()?;

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            solver_assert(z3_solver, converted)?;
        }

        for _ in 0..n {
            if solver_check(z3_solver)? != z3::Lbool::True {
                break;
            }

            let model = solver_get_model(z3_solver)?;
            let eval_result = model_eval(model, z3_expr)?;

            let solution = BitVecAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution
            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            solver_assert(z3_solver, z3_neq)?;
        }

        Ok(results)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        // Simplify and check if concrete
        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        // Convert to Z3 once
        let z3_expr = expr.to_z3()?;

        // Create and fill the Z3 solver once
        let z3_solver = mk_solver()?;

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            solver_assert(z3_solver, converted)?;
        }

        for _ in 0..n {
            if solver_check(z3_solver)? != z3::Lbool::True {
                break;
            }

            let model = solver_get_model(z3_solver)?;
            let eval_result = model_eval(model, z3_expr)?;

            let solution = FloatAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution
            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            solver_assert(z3_solver, z3_neq)?;
        }

        Ok(results)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        // Simplify and check if concrete
        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        // Convert to Z3 once
        let z3_expr = expr.to_z3()?;

        // Create and fill the Z3 solver once
        let z3_solver = mk_solver()?;

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            solver_assert(z3_solver, converted)?;
        }

        for _ in 0..n {
            if solver_check(z3_solver)? != z3::Lbool::True {
                break;
            }

            let model = solver_get_model(z3_solver)?;
            let eval_result = model_eval(model, z3_expr)?;

            let solution = StringAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            // Add constraint to exclude this solution
            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            solver_assert(z3_solver, z3_neq)?;
        }

        Ok(results)
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
