use crate::astext::AstExtZ3;
use crate::rc::{RcModel, RcOptimize, RcSolver};
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

impl<'c> Z3Solver<'c> {

    fn make_filled_solver(&self) -> Result<RcSolver, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *converted);
            }

            Ok(RcSolver::from(z3_solver))
        })
    }

    fn mk_filled_optimize(&self) -> Result<RcOptimize, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let z3_optimize = z3::mk_optimize(z3_ctx);
            z3::optimize_inc_ref(z3_ctx, z3_optimize);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::optimize_assert(z3_ctx, z3_optimize, *converted);
            }

            Ok(RcOptimize::from(z3_optimize))
        })
    }

    fn make_model(&self) -> Result<RcModel, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let z3_solver = self.make_filled_solver()?;
            if z3::solver_check(z3_ctx, *z3_solver) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            Ok(RcModel::from(z3::solver_get_model(z3_ctx, *z3_solver)))
        })
    }

    fn eval_expr_with_model(model: z3::Model, expr: &VarAst<'c>) -> Result<VarAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            match expr {
                VarAst::Boolean(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    let result = if eval_ret {
                        Ok(VarAst::from(&BoolAst::from_z3(expr.context(), eval_result)?))
                    } else {
                        Err(ClarirsError::Unsat)
                    };

                    result
                }
                VarAst::BitVec(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    let result = if eval_ret {
                        Ok(VarAst::from(&BitVecAst::from_z3(expr.context(), eval_result)?))
                    } else {
                        Err(ClarirsError::Unsat)
                    };

                    result
                }
                VarAst::Float(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    let result = if eval_ret {
                        Ok(VarAst::from(&FloatAst::from_z3(expr.context(), eval_result)?))
                    } else {
                        Err(ClarirsError::Unsat)
                    };

                    result
                }
                VarAst::String(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    let result = if eval_ret {
                        Ok(VarAst::from(&StringAst::from_z3(expr.context(), eval_result)?))
                    } else {
                        Err(ClarirsError::Unsat)
                    };

                    result
                }
            }
        })
    }

    fn simplify_varast(expr: &VarAst<'c>) -> Result<VarAst<'c>, ClarirsError> {
        Ok(match expr {
            VarAst::Boolean(expr) => VarAst::from(&expr.simplify_z3()?),
            VarAst::BitVec(expr) => VarAst::from(&expr.simplify_z3()?),
            VarAst::Float(expr) => VarAst::from(&expr.simplify_z3()?),
            VarAst::String(expr) => VarAst::from(&expr.simplify_z3()?),
        })

    }

    fn eval(&self, expr: &VarAst<'c>) -> Result<VarAst<'c>, ClarirsError> {
        let expr = Z3Solver::simplify_varast(expr)?;

        // If the expression is concrete, we can return it directly
        if expr.concrete() {
            return Ok(expr);
        }

        // Expression is not concrete, we need to get a model from Z3 and
        // replace the variables with the values from the model
        let model = self.make_model()?;

        Z3Solver::eval_expr_with_model(*model, &expr)
    }
}

impl<'c> Solver<'c> for Z3Solver<'c> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.assertions.push(constraint.clone());
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let z3_solver = self.make_filled_solver()?;
            Ok(z3::solver_check(z3_ctx, *z3_solver) == z3::Lbool::True)
        })
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        let result = self.eval(&VarAst::from(expr))?;
        match result {
            VarAst::Boolean(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let result = self.eval(&VarAst::from(expr))?;
        match result {
            VarAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        let result = self.eval(&VarAst::from(expr))?;
        match result {
            VarAst::Float(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        let result = self.eval(&VarAst::from(expr))?;
        match result {
            VarAst::String(ast) => Ok(ast),
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

    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            z3::optimize_minimize(z3_ctx, *optimize, *expr.to_z3()?);
            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &VarAst::from(expr))?;
            match result {
                VarAst::BitVec(ast) => Ok(ast),
                _ => unreachable!(),
            }
        })
    }

    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            z3::optimize_maximize(z3_ctx, *optimize, *expr.to_z3()?);
            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &VarAst::from(expr))?;
            match result {
                VarAst::BitVec(ast) => Ok(ast),
                _ => unreachable!(),
            }
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
