use crate::convert::{
    convert_bool_from_z3, convert_bool_to_z3, convert_bv_from_z3, convert_bv_to_z3,
    convert_float_from_z3, convert_float_to_z3, convert_string_from_z3, convert_string_to_z3,
};
use crate::simplify::simplify;
use crate::Z3_CONTEXT;
use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

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
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let app = z3::to_app(z3_ctx, simplified_expr);
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

            let result_converted = convert_bool_from_z3(
                self.ctx,
                if result.is_null() {
                    simplified_expr
                } else {
                    result
                },
            );

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_converted
        })
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bv_to_z3(z3_ctx, expr)?;
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let app = z3::to_app(z3_ctx, simplified_expr);
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

            let result_converted = convert_bv_from_z3(
                self.ctx,
                if result.is_null() {
                    simplified_expr
                } else {
                    result
                },
            );

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_converted
        })
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_float_to_z3(z3_ctx, expr)?;
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let app = z3::to_app(z3_ctx, simplified_expr);
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

            let result_converted = convert_float_from_z3(
                self.ctx,
                if result.is_null() {
                    simplified_expr
                } else {
                    result
                },
            );

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_converted
        })
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_string_to_z3(z3_ctx, expr)?;
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let app = z3::to_app(z3_ctx, simplified_expr);
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

            let result_converted = convert_string_from_z3(
                self.ctx,
                if result.is_null() {
                    simplified_expr
                } else {
                    result
                },
            );

            z3::dec_ref(z3_ctx, converted_expr);
            for assertion in &converted_assertions {
                z3::dec_ref(z3_ctx, *assertion);
            }
            z3::solver_dec_ref(z3_ctx, z3_solver);
            z3::model_dec_ref(z3_ctx, model);
            z3::dec_ref(z3_ctx, result);

            result_converted
        })
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bool_to_z3(z3_ctx, expr)?;
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let result = z3::get_bool_value(z3_ctx, simplified_expr) == z3::Lbool::True;
            z3::dec_ref(z3_ctx, converted_expr);
            z3::dec_ref(z3_ctx, simplified_expr);
            Ok(result)
        })
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let converted_expr = convert_bool_to_z3(z3_ctx, expr)?;
            let simplified_expr = simplify(z3_ctx, converted_expr);
            let result = z3::get_bool_value(z3_ctx, simplified_expr) == z3::Lbool::False;
            z3::dec_ref(z3_ctx, converted_expr);
            z3::dec_ref(z3_ctx, simplified_expr);
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

            let tt = solver.eval_bool(&ctx.and(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.and(&t, &f)?)?;
            let ft = solver.eval_bool(&ctx.and(&f, &t)?)?;
            let ff = solver.eval_bool(&ctx.and(&f, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());
            assert!(ft.is_false());
            assert!(ff.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.false_()?)?)?;

            let result = solver.eval_bool(&ctx.and(&x, &y)?)?;
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

            let tt = solver.eval_bool(&ctx.or(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.or(&t, &f)?)?;
            let ft = solver.eval_bool(&ctx.or(&f, &t)?)?;
            let ff = solver.eval_bool(&ctx.or(&f, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_true());
            assert!(ft.is_true());
            assert!(ff.is_false());

            // Test with symbolic values
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;
            solver.add(&ctx.eq_(&x, &ctx.false_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?;

            let result = solver.eval_bool(&ctx.or(&x, &y)?)?;
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

            let tt = solver.eval_bool(&ctx.if_(&t, &t, &f)?)?;
            let tf = solver.eval_bool(&ctx.if_(&f, &t, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());

            // Test with symbolic values
            let c = ctx.bools("c")?;
            let x = ctx.bools("x")?;
            let y = ctx.bools("y")?;

            solver.add(&ctx.eq_(&c, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
            solver.add(&ctx.eq_(&y, &ctx.false_()?)?)?;

            let result = solver.eval_bool(&ctx.if_(&c, &x, &y)?)?;
            assert!(result.is_true());

            Ok(())
        }
    }
}
