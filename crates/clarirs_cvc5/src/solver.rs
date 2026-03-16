use crate::astext::AstExtCvc5;
use clarirs_core::prelude::*;
use cvc5_rs::{Kind, TermManager};

#[derive(Clone, Debug)]
pub struct Cvc5Solver<'c> {
    ctx: &'c Context<'c>,
    assertions: Vec<BoolAst<'c>>,
    timeout: Option<u32>,
}

impl<'c> Cvc5Solver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self {
            ctx,
            assertions: vec![],
            timeout: None,
        }
    }

    pub fn new_with_timeout(ctx: &'c Context<'c>, timeout: Option<u32>) -> Self {
        Self {
            ctx,
            assertions: vec![],
            timeout,
        }
    }
}

impl<'c> HasContext<'c> for Cvc5Solver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

/// Helper struct that owns both TermManager and Solver with correct lifetimes.
/// We use this pattern because cvc5's Solver borrows from TermManager.
struct SolverSession {
    tm: TermManager,
}

impl SolverSession {
    fn new() -> Self {
        Self {
            tm: TermManager::new(),
        }
    }
}

impl<'c> Cvc5Solver<'c> {
    fn eval(&self, expr: &DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let expr = expr.simplify()?;

        // If the expression is concrete, return it directly
        if expr.concrete() {
            return Ok(expr);
        }

        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let result = solver.check_sat();
        if !result.is_sat() {
            return Err(ClarirsError::Unsat);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;
        let value = solver.get_value(cvc5_expr);
        DynAst::from_cvc5(expr.context(), &session.tm, &value)
    }
}

impl<'c> Solver<'c> for Cvc5Solver<'c> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.assertions.push(constraint.clone());
        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.assertions.clear();
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
                let simplified = c.simplify().ok()?;
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
        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let result = solver.check_sat();
        Ok(result.is_sat())
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
        let expr = expr.simplify()?;
        Ok(expr.concrete() && expr.is_true())
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let expr = expr.simplify()?;
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
        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        // First check if satisfiable
        let result = solver.check_sat();
        if !result.is_sat() {
            return Err(ClarirsError::Unsat);
        }

        // Get initial value
        let mut current_value = solver.get_value(cvc5_expr.clone());

        // Iterative search: keep asking for smaller values
        loop {
            solver.push(1);
            // Assert expr < current_value (unsigned)
            let lt = session.tm.mk_term(
                Kind::CVC5_KIND_BITVECTOR_ULT,
                &[cvc5_expr.clone(), current_value.clone()],
            );
            solver.assert_formula(lt);

            let result = solver.check_sat();
            if !result.is_sat() {
                solver.pop(1);
                break;
            }

            current_value = solver.get_value(cvc5_expr.clone());
            solver.pop(1);
        }

        let result_ast = DynAst::from_cvc5(expr.context(), &session.tm, &current_value)?;
        match result_ast {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        let result = solver.check_sat();
        if !result.is_sat() {
            return Err(ClarirsError::Unsat);
        }

        let mut current_value = solver.get_value(cvc5_expr.clone());

        loop {
            solver.push(1);
            let gt = session.tm.mk_term(
                Kind::CVC5_KIND_BITVECTOR_UGT,
                &[cvc5_expr.clone(), current_value.clone()],
            );
            solver.assert_formula(gt);

            let result = solver.check_sat();
            if !result.is_sat() {
                solver.pop(1);
                break;
            }

            current_value = solver.get_value(cvc5_expr.clone());
            solver.pop(1);
        }

        let result_ast = DynAst::from_cvc5(expr.context(), &session.tm, &current_value)?;
        match result_ast {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        let result = solver.check_sat();
        if !result.is_sat() {
            return Err(ClarirsError::Unsat);
        }

        let mut current_value = solver.get_value(cvc5_expr.clone());

        loop {
            solver.push(1);
            let lt = session.tm.mk_term(
                Kind::CVC5_KIND_BITVECTOR_SLT,
                &[cvc5_expr.clone(), current_value.clone()],
            );
            solver.assert_formula(lt);

            let result = solver.check_sat();
            if !result.is_sat() {
                solver.pop(1);
                break;
            }

            current_value = solver.get_value(cvc5_expr.clone());
            solver.pop(1);
        }

        let result_ast = DynAst::from_cvc5(expr.context(), &session.tm, &current_value)?;
        match result_ast {
            DynAst::BitVec(ast) => Ok(ast),
            _ => unreachable!(),
        }
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        let result = solver.check_sat();
        if !result.is_sat() {
            return Err(ClarirsError::Unsat);
        }

        let mut current_value = solver.get_value(cvc5_expr.clone());

        loop {
            solver.push(1);
            let gt = session.tm.mk_term(
                Kind::CVC5_KIND_BITVECTOR_SGT,
                &[cvc5_expr.clone(), current_value.clone()],
            );
            solver.assert_formula(gt);

            let result = solver.check_sat();
            if !result.is_sat() {
                solver.pop(1);
                break;
            }

            current_value = solver.get_value(cvc5_expr.clone());
            solver.pop(1);
        }

        let result_ast = DynAst::from_cvc5(expr.context(), &session.tm, &current_value)?;
        match result_ast {
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

        let expr = expr.simplify()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        for _ in 0..n {
            let result = solver.check_sat();
            if !result.is_sat() {
                break;
            }

            let value = solver.get_value(cvc5_expr.clone());
            let solution = BoolAst::from_cvc5(self.context(), &session.tm, &value)?;
            results.push(solution.clone());

            // Exclude this solution
            let neq_constraint = self.context().neq(&expr, &solution)?;
            let cvc5_neq = neq_constraint.to_cvc5(&session.tm)?;
            solver.assert_formula(cvc5_neq);
        }

        Ok(results)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        for _ in 0..n {
            let result = solver.check_sat();
            if !result.is_sat() {
                break;
            }

            let value = solver.get_value(cvc5_expr.clone());
            let solution = BitVecAst::from_cvc5(self.context(), &session.tm, &value)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let cvc5_neq = neq_constraint.to_cvc5(&session.tm)?;
            solver.assert_formula(cvc5_neq);
        }

        Ok(results)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        for _ in 0..n {
            let result = solver.check_sat();
            if !result.is_sat() {
                break;
            }

            let value = solver.get_value(cvc5_expr.clone());
            let solution = FloatAst::from_cvc5(self.context(), &session.tm, &value)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let cvc5_neq = neq_constraint.to_cvc5(&session.tm)?;
            solver.assert_formula(cvc5_neq);
        }

        Ok(results)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let mut results = Vec::new();

        let expr = expr.simplify()?;
        if expr.concrete() {
            return Ok(vec![expr; n as usize]);
        }

        let session = SolverSession::new();
        let mut solver = cvc5_rs::Solver::new(&session.tm);
        solver.set_logic("ALL");
        solver.set_option("produce-models", "true");

        if let Some(timeout) = self.timeout {
            solver.set_option("tlimit-per", &timeout.to_string());
        }

        for assertion in &self.assertions {
            let converted = assertion.to_cvc5(&session.tm)?;
            solver.assert_formula(converted);
        }

        let cvc5_expr = expr.to_cvc5(&session.tm)?;

        for _ in 0..n {
            let result = solver.check_sat();
            if !result.is_sat() {
                break;
            }

            let value = solver.get_value(cvc5_expr.clone());
            let solution = StringAst::from_cvc5(self.context(), &session.tm, &value)?;
            results.push(solution.clone());

            let neq_constraint = self.context().neq(&expr, &solution)?;
            let cvc5_neq = neq_constraint.to_cvc5(&session.tm)?;
            solver.assert_formula(cvc5_neq);
        }

        Ok(results)
    }
}
