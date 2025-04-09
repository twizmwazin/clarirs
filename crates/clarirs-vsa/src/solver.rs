use clarirs_core::prelude::*;

/// A solver that uses Value Set Analysis (VSA) for symbolic computation
#[derive(Clone)]
pub struct VSASolver<'c> {
    ctx: &'c Context<'c>,
}

impl<'c> VSASolver<'c> {
    /// Create a new VSA solver
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self { ctx }
    }
}

impl<'c> HasContext<'c> for VSASolver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Solver<'c> for VSASolver<'c> {
    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(vec![])
    }

    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Adding constraints is not supported in VSASolver".to_string(),
        ))
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_bool_n(
        &mut self,
        _expr: &BoolAst<'c>,
        _n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        todo!("Implement eval_bool_n for VSASolver")
    }

    fn eval_bitvec_n(
        &mut self,
        _expr: &BitVecAst<'c>,
        _n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        todo!("Implement eval_bitvec_n for VSASolver")
    }

    fn eval_float_n(
        &mut self,
        _expr: &FloatAst<'c>,
        _n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        todo!("Implement eval_float_n for VSASolver")
    }

    fn eval_string_n(
        &mut self,
        _expr: &StringAst<'c>,
        _n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        todo!("Implement eval_string_n for VSASolver")
    }

    fn is_true(&mut self, _expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        todo!("Implement is_true for VSASolver")
    }

    fn is_false(&mut self, _expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        todo!("Implement is_false for VSASolver")
    }

    fn min_unsigned(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement min_unsigned for VSASolver")
    }

    fn max_unsigned(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement max_unsigned for VSASolver")
    }

    fn min_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement min_signed for VSASolver")
    }

    fn max_signed(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement max_signed for VSASolver")
    }
}
