mod convert;

use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;
use convert::{
    convert_bool_from_z3, convert_bool_to_z3, convert_bv_from_z3, convert_bv_to_z3,
    convert_float_from_z3, convert_float_to_z3, convert_string_from_z3, convert_string_to_z3,
};

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config();
        let ctx = z3::mk_context(cfg);
        z3::del_config(cfg);
        ctx
    }
}

#[derive(Clone)]
pub struct Z3Solver<'c> {
    ctx: &'c Context<'c>,
    assertions: Vec<BoolAst<'c>>,
}

impl<'c> Z3Solver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self {
            ctx,
            assertions: vec![],
        }
    }
}

impl<'c> HasContext<'c> for Z3Solver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Solver<'c> for Z3Solver<'c> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.assertions.push(constraint.clone());
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);
            
            for assertion in &converted_assertions {
                z3::solver_assert(z3_ctx, z3_solver, *assertion);
            }

            let sat = z3::solver_check(z3_ctx, z3_solver) == z3::Lbool::True;

            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);

            Ok(sat)
        })
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bool_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);
            for assertion in &converted_assertions {
                z3::solver_assert(z3_ctx, z3_solver, *assertion);
            }

            if z3::solver_check(z3_ctx, z3_solver) != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::solver_dec_ref(z3_ctx, z3_solver);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::solver_get_model(z3_ctx, z3_solver);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_bool_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bv_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);
            for assertion in &converted_assertions {
                z3::solver_assert(z3_ctx, z3_solver, *assertion);
            }

            let check_result = z3::solver_check(z3_ctx, z3_solver);
            if check_result != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::solver_dec_ref(z3_ctx, z3_solver);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::solver_get_model(z3_ctx, z3_solver);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_bv_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_float_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);
            for assertion in &converted_assertions {
                z3::solver_assert(z3_ctx, z3_solver, *assertion);
            }

            let check_result = z3::solver_check(z3_ctx, z3_solver);
            if check_result != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::solver_dec_ref(z3_ctx, z3_solver);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::solver_get_model(z3_ctx, z3_solver);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_float_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_string_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);
            for assertion in &converted_assertions {
                z3::solver_assert(z3_ctx, z3_solver, *assertion);
            }

            let check_result = z3::solver_check(z3_ctx, z3_solver);
            if check_result != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::solver_dec_ref(z3_ctx, z3_solver);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::solver_get_model(z3_ctx, z3_solver);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_string_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bool_to_z3(z3_ctx, expr)?;
            let result = z3::get_bool_value(z3_ctx, converted_expr) == z3::Lbool::True;
            z3::dec_ref(z3_ctx, converted_expr);
            Ok(result)
        })
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bool_to_z3(z3_ctx, expr)?;
            let result = z3::get_bool_value(z3_ctx, converted_expr) == z3::Lbool::False;
            z3::dec_ref(z3_ctx, converted_expr);
            Ok(result)
        })
    }

    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bv_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_optimize = z3::mk_optimize(z3_ctx);
            z3::optimize_inc_ref(z3_ctx, z3_optimize);
            for assertion in &converted_assertions {
                z3::optimize_assert(z3_ctx, z3_optimize, *assertion);
            }
            z3::optimize_maximize(z3_ctx, z3_optimize, converted_expr);

            let check_result = z3::optimize_check(z3_ctx, z3_optimize, 0, std::ptr::null_mut());
            if check_result != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::optimize_dec_ref(z3_ctx, z3_optimize);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::optimize_get_model(z3_ctx, z3_optimize);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_bv_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            z3::optimize_dec_ref(z3_ctx, z3_optimize);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }

    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bv_to_z3(z3_ctx, expr)?;
            let app = z3::to_app(z3_ctx, converted_expr);
            let expr_decl = z3::get_app_decl(z3_ctx, app);

            let converted_assertions: Vec<_> = self
                .assertions
                .iter()
                .map(|assertion| convert_bool_to_z3(z3_ctx, assertion))
                .collect::<Result<_, _>>()?;

            let z3_optimize = z3::mk_optimize(z3_ctx);
            z3::optimize_inc_ref(z3_ctx, z3_optimize);
            for assertion in &converted_assertions {
                z3::optimize_assert(z3_ctx, z3_optimize, *assertion);
            }
            z3::optimize_maximize(z3_ctx, z3_optimize, converted_expr);

            let check_result = z3::optimize_check(z3_ctx, z3_optimize, 0, std::ptr::null_mut());
            if check_result != z3::Lbool::True {
                z3::dec_ref(z3_ctx, converted_expr);
                for assertion in &converted_assertions {
                    z3::dec_ref(z3_ctx, *assertion);
                }
                z3::optimize_dec_ref(z3_ctx, z3_optimize);
                return Err(ClarirsError::Unsat);
            }

            let model = z3::optimize_get_model(z3_ctx, z3_optimize);
            z3::model_inc_ref(z3_ctx, model);
            let result = z3::model_get_const_interp(z3_ctx, model, expr_decl);
            let result_convered = convert_bv_from_z3(self.ctx, result);

            z3::dec_ref(z3_ctx, converted_expr);
            z3::optimize_dec_ref(z3_ctx, z3_optimize);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_convered
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solver() -> Result<(), ClarirsError> {
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
}
