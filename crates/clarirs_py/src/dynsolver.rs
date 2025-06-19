use clarirs_core::prelude::*;
use clarirs_vsa::{Denormalize, VSASolver};
use clarirs_z3::Z3Solver;

#[derive(Clone, Debug)]
pub(crate) enum DynSolver {
    Concrete(ConcreteSolver<'static>),
    Z3(Z3Solver<'static>),
    Vsa(VSASolver<'static>),
}

impl HasContext<'static> for DynSolver {
    fn context(&self) -> &'static Context<'static> {
        match self {
            DynSolver::Concrete(solver) => solver.context(),
            DynSolver::Z3(solver) => solver.context(),
            DynSolver::Vsa(solver) => solver.context(),
        }
    }
}

impl Solver<'static> for DynSolver {
    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'static>,
        n: u32,
    ) -> Result<Vec<BoolAst<'static>>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_bool_n(expr, n),
            DynSolver::Z3(solver) => solver.eval_bool_n(expr, n),
            DynSolver::Vsa(solver) => solver.eval_bool_n(expr, n),
        }
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'static>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'static>>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_bitvec_n(expr, n),
            DynSolver::Z3(solver) => solver.eval_bitvec_n(expr, n),
            DynSolver::Vsa(solver) => solver.eval_bitvec_n(expr, n),
        }
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'static>,
        n: u32,
    ) -> Result<Vec<FloatAst<'static>>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_float_n(expr, n),
            DynSolver::Z3(solver) => solver.eval_float_n(expr, n),
            DynSolver::Vsa(solver) => solver.eval_float_n(expr, n),
        }
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'static>,
        n: u32,
    ) -> Result<Vec<StringAst<'static>>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_string_n(expr, n),
            DynSolver::Z3(solver) => solver.eval_string_n(expr, n),
            DynSolver::Vsa(solver) => solver.eval_string_n(expr, n),
        }
    }
    fn constraints(&self) -> Result<Vec<BoolAst<'static>>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.constraints(),
            DynSolver::Z3(solver) => solver.constraints(),
            DynSolver::Vsa(solver) => solver.constraints(),
        }
    }

    fn add(&mut self, constraint: &BoolAst<'static>) -> Result<(), ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.add(constraint),
            DynSolver::Z3(solver) => solver.add(constraint),
            DynSolver::Vsa(solver) => solver.add(constraint),
        }
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.satisfiable(),
            DynSolver::Z3(solver) => solver.satisfiable(),
            DynSolver::Vsa(solver) => solver.satisfiable(),
        }
    }

    fn eval_bool(&mut self, expr: &BoolAst<'static>) -> Result<BoolAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_bool(expr),
            DynSolver::Z3(solver) => solver.eval_bool(expr),
            DynSolver::Vsa(solver) => solver.eval_bool(expr).and_then(Denormalize::denormalize),
        }
    }

    fn eval_bitvec(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_bitvec(expr),
            DynSolver::Z3(solver) => solver.eval_bitvec(expr),
            DynSolver::Vsa(solver) => solver.eval_bitvec(expr).and_then(Denormalize::denormalize),
        }
    }

    fn eval_float(&mut self, expr: &FloatAst<'static>) -> Result<FloatAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_float(expr),
            DynSolver::Z3(solver) => solver.eval_float(expr),
            DynSolver::Vsa(solver) => solver.eval_float(expr),
        }
    }

    fn eval_string(
        &mut self,
        expr: &StringAst<'static>,
    ) -> Result<StringAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_string(expr),
            DynSolver::Z3(solver) => solver.eval_string(expr),
            DynSolver::Vsa(solver) => solver.eval_string(expr),
        }
    }

    fn is_true(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.is_true(expr),
            DynSolver::Z3(solver) => solver.is_true(expr),
            DynSolver::Vsa(solver) => solver.is_true(expr),
        }
    }

    fn is_false(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.is_false(expr),
            DynSolver::Z3(solver) => solver.is_false(expr),
            DynSolver::Vsa(solver) => solver.is_false(expr),
        }
    }

    fn has_true(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.is_true(expr),
            DynSolver::Z3(solver) => solver.is_true(expr),
            DynSolver::Vsa(solver) => solver.is_true(expr),
        }
    }

    fn has_false(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.is_false(expr),
            DynSolver::Z3(solver) => solver.is_false(expr),
            DynSolver::Vsa(solver) => solver.is_false(expr),
        }
    }

    fn min_unsigned(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.min_unsigned(expr),
            DynSolver::Z3(solver) => solver.min_unsigned(expr),
            DynSolver::Vsa(solver) => solver.min_unsigned(expr),
        }
    }

    fn max_unsigned(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.max_unsigned(expr),
            DynSolver::Z3(solver) => solver.max_unsigned(expr),
            DynSolver::Vsa(solver) => solver.max_unsigned(expr),
        }
    }

    fn min_signed(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.min_signed(expr),
            DynSolver::Z3(solver) => solver.min_signed(expr),
            DynSolver::Vsa(solver) => solver.min_signed(expr),
        }
    }

    fn max_signed(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.max_signed(expr),
            DynSolver::Z3(solver) => solver.max_signed(expr),
            DynSolver::Vsa(solver) => solver.max_signed(expr),
        }
    }
}
