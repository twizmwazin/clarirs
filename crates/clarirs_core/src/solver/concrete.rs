use crate::prelude::*;

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

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;
    use crate::prelude::*;

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
