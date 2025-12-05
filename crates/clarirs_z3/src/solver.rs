use crate::Z3_CONTEXT;
use crate::astext::AstExtZ3;
use crate::rc::{RcModel, RcOptimize, RcSolver};
use clarirs_core::ast::bitvec::BitVecOpExt;
use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

#[derive(Clone, Debug)]
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

    fn eval_expr_with_model(
        model: z3::Model,
        expr: &DynAst<'c>,
    ) -> Result<DynAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            match expr {
                DynAst::Boolean(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    if eval_ret {
                        Ok(DynAst::from(&BoolAst::from_z3(
                            expr.context(),
                            eval_result,
                        )?))
                    } else {
                        Err(ClarirsError::Unsat)
                    }
                }
                DynAst::BitVec(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    if eval_ret {
                        Ok(DynAst::from(&BitVecAst::from_z3(
                            expr.context(),
                            eval_result,
                        )?))
                    } else {
                        Err(ClarirsError::Unsat)
                    }
                }
                DynAst::Float(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    if eval_ret {
                        Ok(DynAst::from(&FloatAst::from_z3(
                            expr.context(),
                            eval_result,
                        )?))
                    } else {
                        Err(ClarirsError::Unsat)
                    }
                }
                DynAst::String(a) => {
                    let z3_expr = a.to_z3()?;
                    let mut eval_result: z3::Ast = std::mem::zeroed();
                    let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);
                    if eval_ret {
                        Ok(DynAst::from(&StringAst::from_z3(
                            expr.context(),
                            eval_result,
                        )?))
                    } else {
                        Err(ClarirsError::Unsat)
                    }
                }
            }
        })
    }

    fn simplify_varast(expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        Ok(match expr {
            DynAst::Boolean(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::BitVec(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::Float(expr) => DynAst::from(&expr.simplify_z3()?),
            DynAst::String(expr) => DynAst::from(&expr.simplify_z3()?),
        })
    }

    fn eval(&self, expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let expr = Z3Solver::simplify_varast(&expr.simplify()?)?;

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

        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Create and fill the Z3 solver once
            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *converted);
            }

            for _ in 0..n {
                if z3::solver_check(z3_ctx, z3_solver) != z3::Lbool::True {
                    break;
                }

                let model = z3::solver_get_model(z3_ctx, z3_solver);
                let mut eval_result: z3::Ast = std::mem::zeroed();
                let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);

                if !eval_ret {
                    break;
                }

                let solution = BoolAst::from_z3(self.context(), eval_result)?;
                results.push(solution.clone());

                // Add constraint to exclude this solution
                let neq_constraint = self.context().neq(&expr, &solution)?;
                let z3_neq = neq_constraint.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *z3_neq);
            }

            Ok(results)
        })
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

        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Create and fill the Z3 solver once
            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *converted);
            }

            for _ in 0..n {
                if z3::solver_check(z3_ctx, z3_solver) != z3::Lbool::True {
                    break;
                }

                let model = z3::solver_get_model(z3_ctx, z3_solver);
                let mut eval_result: z3::Ast = std::mem::zeroed();
                let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);

                if !eval_ret {
                    break;
                }

                let solution = BitVecAst::from_z3(self.context(), eval_result)?;
                results.push(solution.clone());

                // Add constraint to exclude this solution
                let neq_constraint = self.context().neq(&expr, &solution)?;
                let z3_neq = neq_constraint.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *z3_neq);
            }

            Ok(results)
        })
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

        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Create and fill the Z3 solver once
            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *converted);
            }

            for _ in 0..n {
                if z3::solver_check(z3_ctx, z3_solver) != z3::Lbool::True {
                    break;
                }

                let model = z3::solver_get_model(z3_ctx, z3_solver);
                let mut eval_result: z3::Ast = std::mem::zeroed();
                let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);

                if !eval_ret {
                    break;
                }

                let solution = FloatAst::from_z3(self.context(), eval_result)?;
                results.push(solution.clone());

                // Add constraint to exclude this solution
                let neq_constraint = self.context().neq(&expr, &solution)?;
                let z3_neq = neq_constraint.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *z3_neq);
            }

            Ok(results)
        })
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

        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Create and fill the Z3 solver once
            let z3_solver = z3::mk_solver(z3_ctx);
            z3::solver_inc_ref(z3_ctx, z3_solver);

            for assertion in &self.assertions {
                let converted = assertion.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *converted);
            }

            for _ in 0..n {
                if z3::solver_check(z3_ctx, z3_solver) != z3::Lbool::True {
                    break;
                }

                let model = z3::solver_get_model(z3_ctx, z3_solver);
                let mut eval_result: z3::Ast = std::mem::zeroed();
                let eval_ret = z3::model_eval(z3_ctx, model, *z3_expr, true, &mut eval_result);

                if !eval_ret {
                    break;
                }

                let solution = StringAst::from_z3(self.context(), eval_result)?;
                results.push(solution.clone());

                // Add constraint to exclude this solution
                let neq_constraint = self.context().neq(&expr, &solution)?;
                let z3_neq = neq_constraint.to_z3()?;
                z3::solver_assert(z3_ctx, z3_solver, *z3_neq);
            }

            Ok(results)
        })
    }
    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(self.assertions.clone())
    }

    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.assertions.push(constraint.clone());
        Ok(())
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
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let z3_solver = self.make_filled_solver()?;
            Ok(z3::solver_check(z3_ctx, *z3_solver) == z3::Lbool::True)
        })
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
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            z3::optimize_minimize(z3_ctx, *optimize, *expr.to_z3()?);
            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &DynAst::from(expr))?;
            match result {
                DynAst::BitVec(ast) => Ok(ast),
                _ => unreachable!(),
            }
        })
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            z3::optimize_maximize(z3_ctx, *optimize, *expr.to_z3()?);
            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &DynAst::from(expr))?;
            match result {
                DynAst::BitVec(ast) => Ok(ast),
                _ => unreachable!(),
            }
        })
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Get the size of the bitvector
            let size = expr.size();

            // For signed minimization, the sign bit should be 1 (for negative numbers)
            // Extract the sign bit
            let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
            let one_bit = self.ctx.bvv_prim_with_size(1u64, 1)?;

            // Create a target variable equal to the expression
            let target_name = format!("min_signed_target_{size}");
            let target = self.ctx.bvs(&target_name, size)?;
            let equality = self.ctx.eq_(&target, expr)?;
            z3::optimize_assert(z3_ctx, *optimize, *equality.to_z3()?);

            // First, maximize the sign bit with a high weight
            // This will prefer negative numbers (sign bit = 1) over positive ones
            let sign_equality = self.ctx.eq_(&sign_bit, &one_bit)?;
            let weight = std::ffi::CString::new("1000000").unwrap();
            z3::optimize_assert_soft(
                z3_ctx,
                *optimize,
                *sign_equality.to_z3()?,
                weight.as_ptr(),
                std::ptr::null_mut(),
            );

            // Then minimize the target value (with lower weight)
            // This will find the smallest value among those with the preferred sign bit
            z3::optimize_minimize(z3_ctx, *optimize, *target.to_z3()?);

            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &DynAst::from(expr))?;
            match result {
                DynAst::BitVec(ast) => Ok(ast),
                _ => unreachable!(),
            }
        })
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = self.mk_filled_optimize()?;
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            // Get the size of the bitvector
            let size = expr.size();

            // For signed maximization, the sign bit should be 0 (for positive numbers)
            // Extract the sign bit
            let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
            let zero_bit = self.ctx.bvv_prim_with_size(0u64, 1)?;

            // Create a target variable equal to the expression
            let target_name = format!("max_signed_target_{size}");
            let target = self.ctx.bvs(&target_name, size)?;
            let equality = self.ctx.eq_(&target, expr)?;
            z3::optimize_assert(z3_ctx, *optimize, *equality.to_z3()?);

            // First, maximize making the sign bit 0 with a high weight
            // This will prefer positive numbers (sign bit = 0) over negative ones
            let sign_equality = self.ctx.eq_(&sign_bit, &zero_bit)?;
            let weight = std::ffi::CString::new("1000000").unwrap();
            z3::optimize_assert_soft(
                z3_ctx,
                *optimize,
                *sign_equality.to_z3()?,
                weight.as_ptr(),
                std::ptr::null_mut(),
            );

            // Then maximize the target value (with lower weight)
            // This will find the largest value among those with the preferred sign bit
            z3::optimize_maximize(z3_ctx, *optimize, *target.to_z3()?);

            if z3::optimize_check(z3_ctx, *optimize, 0, std::ptr::null_mut()) != z3::Lbool::True {
                return Err(ClarirsError::Unsat);
            }

            let model = RcModel::from(z3::optimize_get_model(z3_ctx, *optimize));
            let result = Z3Solver::eval_expr_with_model(*model, &DynAst::from(expr))?;
            match result {
                DynAst::BitVec(ast) => Ok(ast),
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

            let result = solver.eval_bool(&ctx.if_(c, x, y)?)?;
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
}
