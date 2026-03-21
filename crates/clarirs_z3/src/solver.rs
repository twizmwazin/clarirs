use crate::astext::AstExtZ3;
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

    pub fn unsat_core(&mut self) -> Result<Vec<usize>, ClarirsError> {
        if !self.unsat_core {
            return Err(ClarirsError::UnsupportedOperation(
                "Unsat core tracking is not enabled. Use new_with_options with unsat_core=true"
                    .to_string(),
            ));
        }

        let z3_solver = self.make_filled_solver()?;

        if z3_solver.check() != z3::SatResult::Unsat {
            return Err(ClarirsError::UnsupportedOperation(
                "Can only get unsat core after an UNSAT result".to_string(),
            ));
        }

        let core_asts = z3_solver.get_unsat_core();
        let mut core_indices = Vec::new();

        let mut track_to_idx: HashMap<String, usize> = HashMap::new();
        for (idx, track_var) in &self.tracking_vars {
            if let Some(vars) = track_var.variables().iter().next() {
                track_to_idx.insert(vars.to_string(), *idx);
            }
        }

        for core_ast in &core_asts {
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
            let bool_ast = converted.as_bool().ok_or_else(|| {
                ClarirsError::ConversionError("expected bool for assertion".to_string())
            })?;
            if self.unsat_core {
                if let Some(track_var) = self.tracking_vars.get(&idx) {
                    let track_z3 = track_var.to_z3()?;
                    let track_bool = track_z3.as_bool().unwrap();
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
            let bool_ast = converted.as_bool().ok_or_else(|| {
                ClarirsError::ConversionError("expected bool for assertion".to_string())
            })?;
            z3_optimize.assert(&bool_ast);
        }

        Ok(z3_optimize)
    }

    fn make_model(&self) -> Result<z3::Model, ClarirsError> {
        let z3_solver = self.make_filled_solver()?;
        if z3_solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        z3_solver.get_model().ok_or_else(|| {
            ClarirsError::BackendError("Z3", "failed to get model".to_string())
        })
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
        model.eval(expr_z3, true).ok_or_else(|| {
            ClarirsError::BackendError("Z3", "Model evaluation failed".to_string())
        })
    }

    fn eval(&self, expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let expr = Z3Solver::simplify_dynast(&expr.simplify()?)?;

        if expr.concrete() {
            return Ok(expr);
        }

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
        let z3_optimize = self.mk_filled_optimize()?;
        let expr_z3 = expr.to_z3()?;
        z3_optimize.minimize(&expr_z3);
        if z3_optimize.check(&[]) != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        let model = z3_optimize.get_model().ok_or_else(|| {
            ClarirsError::BackendError("Z3", "failed to get model".to_string())
        })?;
        let eval_result = Self::eval_model(&model, &expr_z3)?;
        let result = DynAst::from_z3(expr.context(), eval_result)?;

        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let z3_optimize = self.mk_filled_optimize()?;
        let expr_z3 = expr.to_z3()?;
        z3_optimize.maximize(&expr_z3);
        if z3_optimize.check(&[]) != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        let model = z3_optimize.get_model().ok_or_else(|| {
            ClarirsError::BackendError("Z3", "failed to get model".to_string())
        })?;
        let eval_result = Self::eval_model(&model, &expr_z3)?;
        let result = DynAst::from_z3(expr.context(), eval_result)?;

        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let z3_optimize = self.mk_filled_optimize()?;
        let size = expr.size();

        let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
        let one_bit = self.ctx.bvv_prim_with_size(1u64, 1)?;

        let target_name = format!("min_signed_target_{size}");
        let target = self.ctx.bvs(&target_name, size)?;
        let equality = self.ctx.eq_(&target, expr)?;
        let eq_z3 = equality.to_z3()?;
        z3_optimize.assert(&eq_z3.as_bool().unwrap());

        let sign_equality = self.ctx.eq_(&sign_bit, &one_bit)?;
        let sign_z3 = sign_equality.to_z3()?;
        z3_optimize.assert_soft(&sign_z3.as_bool().unwrap(), 1000000, None);

        let target_z3 = target.to_z3()?;
        z3_optimize.minimize(&target_z3);

        if z3_optimize.check(&[]) != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        let model = z3_optimize.get_model().ok_or_else(|| {
            ClarirsError::BackendError("Z3", "failed to get model".to_string())
        })?;
        let expr_z3 = expr.to_z3()?;
        let eval_result = Self::eval_model(&model, &expr_z3)?;
        let result = DynAst::from_z3(expr.context(), eval_result)?;
        match result {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let z3_optimize = self.mk_filled_optimize()?;
        let size = expr.size();

        let sign_bit = self.ctx.extract(expr, size - 1, size - 1)?;
        let zero_bit = self.ctx.bvv_prim_with_size(0u64, 1)?;

        let target_name = format!("max_signed_target_{size}");
        let target = self.ctx.bvs(&target_name, size)?;
        let equality = self.ctx.eq_(&target, expr)?;
        let eq_z3 = equality.to_z3()?;
        z3_optimize.assert(&eq_z3.as_bool().unwrap());

        let sign_equality = self.ctx.eq_(&sign_bit, &zero_bit)?;
        let sign_z3 = sign_equality.to_z3()?;
        z3_optimize.assert_soft(&sign_z3.as_bool().unwrap(), 1000000, None);

        let target_z3 = target.to_z3()?;
        z3_optimize.maximize(&target_z3);

        if z3_optimize.check(&[]) != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        let model = z3_optimize.get_model().ok_or_else(|| {
            ClarirsError::BackendError("Z3", "failed to get model".to_string())
        })?;
        let expr_z3 = expr.to_z3()?;
        let eval_result = Self::eval_model(&model, &expr_z3)?;
        let result = DynAst::from_z3(expr.context(), eval_result)?;
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

        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let z3_expr = expr.to_z3()?;

        let z3_solver = z3::Solver::new();

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            z3_solver.assert(&converted.as_bool().unwrap());
        }

        for _ in 0..n {
            if z3_solver.check() != z3::SatResult::Sat {
                break;
            }

            let model = z3_solver.get_model().ok_or_else(|| {
                ClarirsError::BackendError("Z3", "failed to get model".to_string())
            })?;
            let eval_result = Self::eval_model(&model, &z3_expr)?;

            let solution = BoolAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            z3_solver.assert(&z3_neq.as_bool().unwrap());
        }

        Ok(results)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let z3_expr = expr.to_z3()?;

        let z3_solver = z3::Solver::new();

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            z3_solver.assert(&converted.as_bool().unwrap());
        }

        for _ in 0..n {
            if z3_solver.check() != z3::SatResult::Sat {
                break;
            }

            let model = z3_solver.get_model().ok_or_else(|| {
                ClarirsError::BackendError("Z3", "failed to get model".to_string())
            })?;
            let eval_result = Self::eval_model(&model, &z3_expr)?;

            let solution = BitVecAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            z3_solver.assert(&z3_neq.as_bool().unwrap());
        }

        Ok(results)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let z3_expr = expr.to_z3()?;

        let z3_solver = z3::Solver::new();

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            z3_solver.assert(&converted.as_bool().unwrap());
        }

        for _ in 0..n {
            if z3_solver.check() != z3::SatResult::Sat {
                break;
            }

            let model = z3_solver.get_model().ok_or_else(|| {
                ClarirsError::BackendError("Z3", "failed to get model".to_string())
            })?;
            let eval_result = Self::eval_model(&model, &z3_expr)?;

            let solution = FloatAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            z3_solver.assert(&z3_neq.as_bool().unwrap());
        }

        Ok(results)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify_z3()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let z3_expr = expr.to_z3()?;

        let z3_solver = z3::Solver::new();

        for assertion in &self.assertions {
            let converted = assertion.to_z3()?;
            z3_solver.assert(&converted.as_bool().unwrap());
        }

        for _ in 0..n {
            if z3_solver.check() != z3::SatResult::Sat {
                break;
            }

            let model = z3_solver.get_model().ok_or_else(|| {
                ClarirsError::BackendError("Z3", "failed to get model".to_string())
            })?;
            let eval_result = Self::eval_model(&model, &z3_expr)?;

            let solution = StringAst::from_z3(self.context(), eval_result)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let z3_neq = neq_constraint.to_z3()?;
            z3_solver.assert(&z3_neq.as_bool().unwrap());
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

            let t = ctx.true_()?;
            let not_t = ctx.not(&t)?;
            let result = solver.eval_bool(&not_t)?;
            assert!(result.is_false());

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

            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.eq_(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.eq_(&t, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());

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

            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.neq(&t, &t)?)?;
            let tf = solver.eval_bool(&ctx.neq(&t, &f)?)?;

            assert!(tt.is_false());
            assert!(tf.is_true());

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

            let t = ctx.true_()?;
            let f = ctx.false_()?;

            let tt = solver.eval_bool(&ctx.ite(&t, &t, &f)?)?;
            let tf = solver.eval_bool(&ctx.ite(&f, &t, &f)?)?;

            assert!(tt.is_true());
            assert!(tf.is_false());

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

            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.min_unsigned(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.max_unsigned(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_min_unsigned_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 64)?;

            let lower_bound = ctx.bvv_prim(10u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.uge(&x, &lower_bound)?)?;
            solver.add(&ctx.ule(&x, &upper_bound)?)?;

            let result = solver.min_unsigned(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 64)?;

            let lower_bound = ctx.bvv_prim(10u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.uge(&x, &lower_bound)?)?;
            solver.add(&ctx.ule(&x, &upper_bound)?)?;

            let result = solver.max_unsigned(&x)?;
            assert_eq!(result, upper_bound);

            Ok(())
        }

        #[test]
        fn test_min_unsigned_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            let five = ctx.bvv_prim(5u8)?;
            let ten = ctx.bvv_prim(10u8)?;

            solver.add(&ctx.ugt(&x, &five)?)?;
            solver.add(&ctx.ult(&y, &ten)?)?;

            let sum = ctx.add(&x, &y)?;
            let zero = ctx.bvv_prim_with_size(0u64, 1)?;
            solver.add(&ctx.eq_(&ctx.extract(&sum, 0, 0)?, &zero)?)?;

            let result = solver.min_unsigned(&x)?;

            let six = ctx.bvv_prim(6u8)?;
            assert_eq!(result, six);

            Ok(())
        }

        #[test]
        fn test_max_unsigned_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            let hundred = ctx.bvv_prim(100u8)?;
            let twenty = ctx.bvv_prim(20u8)?;

            solver.add(&ctx.ult(&x, &hundred)?)?;
            solver.add(&ctx.ugt(&y, &twenty)?)?;
            solver.add(&ctx.ugt(&x, &y)?)?;

            let result = solver.max_unsigned(&x)?;

            let ninety_nine = ctx.bvv_prim(99u8)?;
            assert_eq!(result, ninety_nine);

            Ok(())
        }

        #[test]
        fn test_min_signed_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.min_signed(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_max_signed_concrete() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let bv = ctx.bvv_prim(42u64)?;
            let result = solver.max_signed(&bv)?;

            assert_eq!(result, bv);

            Ok(())
        }

        #[test]
        fn test_min_signed_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 64)?;

            let lower_bound = ctx.bvv_prim(0xfffffffffffffff6u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            let result = solver.min_signed(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_signed_constrained() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 64)?;

            let lower_bound = ctx.bvv_prim(0xfffffffffffffff6u64)?;
            let upper_bound = ctx.bvv_prim(20u64)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            let result = solver.max_signed(&x)?;
            assert_eq!(result, upper_bound);

            Ok(())
        }

        #[test]
        fn test_min_signed_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            let neg_five = ctx.bvv_prim(0xfbu8)?;
            let ten = ctx.bvv_prim(10u8)?;

            solver.add(&ctx.sgt(&x, &neg_five)?)?;
            solver.add(&ctx.slt(&y, &ten)?)?;

            let sum = ctx.add(&x, &y)?;
            let zero = ctx.bvv_prim_with_size(0u64, 1)?;
            solver.add(&ctx.eq_(&ctx.extract(&sum, 0, 0)?, &zero)?)?;

            let result = solver.min_signed(&x)?;

            let neg_four = ctx.bvv_prim(0xfcu8)?;
            assert_eq!(result, neg_four);

            Ok(())
        }

        #[test]
        fn test_max_signed_complex() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            let hundred = ctx.bvv_prim(100u8)?;
            let neg_twenty = ctx.bvv_prim(0xecu8)?;

            solver.add(&ctx.slt(&x, &hundred)?)?;
            solver.add(&ctx.sgt(&y, &neg_twenty)?)?;
            solver.add(&ctx.sgt(&x, &y)?)?;

            let result = solver.max_signed(&x)?;

            let ninety_nine = ctx.bvv_prim(99u8)?;
            assert_eq!(result, ninety_nine);

            Ok(())
        }

        #[test]
        fn test_min_signed_negative_range() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;

            let lower_bound = ctx.bvv_prim(0x9cu8)?;
            let upper_bound = ctx.bvv_prim(0xf6u8)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

            let result = solver.min_signed(&x)?;
            assert_eq!(result, lower_bound);

            Ok(())
        }

        #[test]
        fn test_max_signed_negative_range() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = Z3Solver::new(&ctx);

            let x = ctx.bvs("x", 8)?;

            let lower_bound = ctx.bvv_prim(0x9cu8)?;
            let upper_bound = ctx.bvv_prim(0xf6u8)?;

            solver.add(&ctx.sge(&x, &lower_bound)?)?;
            solver.add(&ctx.sle(&x, &upper_bound)?)?;

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

        solver.add(&ctx.eq_(&x, &ctx.true_()?)?)?;
        solver.add(&ctx.eq_(&y, &ctx.true_()?)?)?;
        solver.add(&ctx.eq_(&x, &y)?)?;
        solver.add(&ctx.neq(&x, &y)?)?;

        assert!(!solver.satisfiable()?);

        let core = solver.unsat_core()?;

        assert!(!core.is_empty());
        assert!(core.len() <= 4);

        Ok(())
    }

    #[test]
    fn test_unsat_core_minimal() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new_with_options(&ctx, None, true);

        let x = ctx.bvs("x", 8)?;

        let c0 = ctx.ugt(&x, &ctx.bvv_prim(10u8)?)?;
        let c1 = ctx.ult(&x, &ctx.bvv_prim(5u8)?)?;
        let c2 = ctx.ugt(&x, &ctx.bvv_prim(0u8)?)?;

        solver.add(&c0)?;
        solver.add(&c1)?;
        solver.add(&c2)?;

        assert!(!solver.satisfiable()?);

        let core = solver.unsat_core()?;

        assert!(!core.is_empty());
        assert!(core.contains(&0));
        assert!(core.contains(&1));

        Ok(())
    }

    #[test]
    fn test_unsat_core_not_enabled() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;

        solver.add(&x)?;
        solver.add(&ctx.not(&x)?)?;

        assert!(!solver.satisfiable()?);

        assert!(solver.unsat_core().is_err());

        Ok(())
    }

    #[test]
    fn test_unsat_core_on_sat() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let mut solver = Z3Solver::new_with_options(&ctx, None, true);

        let x = ctx.bools("x")?;
        solver.add(&x)?;

        assert!(solver.satisfiable()?);

        assert!(solver.unsat_core().is_err());

        Ok(())
    }
}
