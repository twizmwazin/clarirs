use clarirs_core::prelude::*;
use clarirs_vsa::VSASolver;
use clarirs_z3::Z3Solver;

#[derive(Clone)]
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
            DynSolver::Vsa(solver) => solver.eval_bool(expr),
        }
    }

    fn eval_bitvec(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.eval_bitvec(expr),
            DynSolver::Z3(solver) => solver.eval_bitvec(expr),
            DynSolver::Vsa(solver) => solver.eval_bitvec(expr),
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

    fn min(&mut self, expr: &BitVecAst<'static>) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.min(expr),
            DynSolver::Z3(solver) => solver.min(expr),
            DynSolver::Vsa(solver) => solver.min(expr),
        }
    }

    fn max(&mut self, expr: &BitVecAst<'static>) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::Concrete(solver) => solver.max(expr),
            DynSolver::Z3(solver) => solver.max(expr),
            DynSolver::Vsa(solver) => solver.max(expr),
        }
    }
}
