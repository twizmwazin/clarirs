use std::ops::{Deref, DerefMut};

use crate::{Z3_CONTEXT, check_z3_error};
use clarirs_core::error::ClarirsError;
use clarirs_z3_sys as z3;

#[repr(transparent)]
pub struct RcAst(z3::Ast);

impl Clone for RcAst {
    fn clone(&self) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::inc_ref(ctx, self.0) });
        RcAst(self.0)
    }
}

impl From<&RcAst> for RcAst {
    fn from(val: &RcAst) -> Self {
        val.clone()
    }
}

impl Drop for RcAst {
    fn drop(&mut self) {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::dec_ref(ctx, self.0) });
    }
}

impl TryFrom<z3::Ast> for RcAst {
    type Error = ClarirsError;

    fn try_from(ast: z3::Ast) -> Result<Self, Self::Error> {
        check_z3_error()?;
        Z3_CONTEXT.with(|&ctx| unsafe { z3::inc_ref(ctx, ast) });
        Ok(RcAst(ast))
    }
}

impl From<RcAst> for z3::Ast {
    fn from(ast: RcAst) -> Self {
        ast.0
    }
}

impl Deref for RcAst {
    type Target = z3::Ast;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for RcAst {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[repr(transparent)]
pub struct RcSolver(z3::Solver);

impl RcSolver {
    pub fn new() -> Result<Self, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let solver = RcSolver::from(z3::mk_solver(ctx));
            check_z3_error()?;
            Ok(solver)
        })
    }

    pub fn assert(&mut self, ast: &RcAst) -> Result<(), ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_assert(ctx, self.0, **ast) });
        check_z3_error()
    }

    pub fn check(&mut self) -> Result<z3::Lbool, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let result = z3::solver_check(ctx, self.0);
            check_z3_error()?;
            Ok(result)
        })
    }

    pub fn model(&mut self) -> Result<RcModel, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let model = RcModel::from(z3::solver_get_model(ctx, self.0));
            check_z3_error()?;
            Ok(model)
        })
    }
}

impl Clone for RcSolver {
    fn clone(&self) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_inc_ref(ctx, self.0) });
        RcSolver(self.0)
    }
}

impl Drop for RcSolver {
    fn drop(&mut self) {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_dec_ref(ctx, self.0) });
    }
}

impl From<z3::Solver> for RcSolver {
    fn from(solver: z3::Solver) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::solver_inc_ref(ctx, solver) });
        RcSolver(solver)
    }
}

impl From<RcSolver> for z3::Solver {
    fn from(solver: RcSolver) -> Self {
        solver.0
    }
}

impl Deref for RcSolver {
    type Target = z3::Solver;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for RcSolver {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[repr(transparent)]
pub struct RcOptimize(z3::Optimize);

impl RcOptimize {
    pub fn new() -> Result<Self, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let optimize = RcOptimize::from(z3::mk_optimize(ctx));
            check_z3_error()?;
            Ok(optimize)
        })
    }

    pub fn assert(&mut self, ast: &RcAst) -> Result<(), ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_assert(ctx, self.0, **ast) });
        check_z3_error()
    }

    pub fn assert_soft(&mut self, ast: &RcAst, weight: u32) -> Result<(), ClarirsError> {
        let weight_string = std::ffi::CString::new(weight.to_string()).map_err(|_| {
            ClarirsError::BackendError("Z3", "Failed to convert weight to CString".into())
        })?;
        Z3_CONTEXT.with(|&ctx| unsafe {
            z3::optimize_assert_soft(
                ctx,
                self.0,
                **ast,
                weight_string.as_ptr(),
                std::ptr::null_mut(),
            );
        });
        check_z3_error()
    }

    pub fn minimize(&mut self, ast: &RcAst) -> Result<(), ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_minimize(ctx, self.0, **ast) });
        check_z3_error()
    }

    pub fn maximize(&mut self, ast: &RcAst) -> Result<(), ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_maximize(ctx, self.0, **ast) });
        check_z3_error()
    }

    pub fn check(&mut self) -> Result<z3::Lbool, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let result = z3::optimize_check(ctx, self.0, 0, std::ptr::null());
            check_z3_error()?;
            Ok(result)
        })
    }

    pub fn get_model(&mut self) -> Result<RcModel, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let model = z3::optimize_get_model(ctx, self.0);
            check_z3_error()?;
            Ok(RcModel::from(model))
        })
    }
}

impl Clone for RcOptimize {
    fn clone(&self) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_inc_ref(ctx, self.0) });
        RcOptimize(self.0)
    }
}

impl Drop for RcOptimize {
    fn drop(&mut self) {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_dec_ref(ctx, self.0) });
    }
}

impl From<z3::Optimize> for RcOptimize {
    fn from(optimize: z3::Optimize) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::optimize_inc_ref(ctx, optimize) });
        RcOptimize(optimize)
    }
}

impl From<RcOptimize> for z3::Optimize {
    fn from(optimize: RcOptimize) -> Self {
        optimize.0
    }
}

impl Deref for RcOptimize {
    type Target = z3::Optimize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for RcOptimize {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[repr(transparent)]
pub struct RcModel(z3::Model);

impl RcModel {
    pub fn eval(&self, ast: &RcAst) -> Result<RcAst, ClarirsError> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let mut eval_result: z3::Ast = std::mem::zeroed();
            let eval_ret = z3::model_eval(ctx, self.0, **ast, true, &mut eval_result);
            check_z3_error()?;
            if !eval_ret {
                return Err(ClarirsError::BackendError(
                    "Z3",
                    "Model evaluation failed".into(),
                ));
            }
            RcAst::try_from(eval_result)
        })
    }
}

impl Clone for RcModel {
    fn clone(&self) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::model_inc_ref(ctx, self.0) });
        RcModel(self.0)
    }
}

impl Drop for RcModel {
    fn drop(&mut self) {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::model_dec_ref(ctx, self.0) });
    }
}

impl From<z3::Model> for RcModel {
    fn from(model: z3::Model) -> Self {
        Z3_CONTEXT.with(|&ctx| unsafe { z3::model_inc_ref(ctx, model) });
        RcModel(model)
    }
}

impl From<RcModel> for z3::Model {
    fn from(model: RcModel) -> Self {
        model.0
    }
}

impl Deref for RcModel {
    type Target = z3::Model;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for RcModel {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
