use std::{cell::OnceCell, rc::Rc};

use clarirs_core::prelude::*;

struct Z3Model<'c, 's> {
    ctx: &'c Context<'c>,
    z3_ctx: &'s z3::Context,
    model: z3::Model<'s>,
}

impl<'c, 's> HasContext<'c> for Z3Model<'c, 's> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, 's> Model<'c> for Z3Model<'c, 's> {
    fn batch_eval<I>(&self, exprs: I, max_solutions: u32) -> Result<Vec<AstRef<'c>>, ClarirsError>
    where
        I: IntoIterator<Item = AstRef<'c>>,
    {
        todo!()
    }
}

#[derive(Clone)]
struct Z3Solver<'c, 's> {
    ctx: &'c Context<'c>,
    z3_cfg: Rc<z3::Config>,
    z3_ctx: Rc<z3::Context>,
    solver: OnceCell<z3::Solver<'s>>,
}

impl<'c, 's> Z3Solver<'c, 's> {
    fn new(ctx: &'c Context<'c>) -> Self {
        let z3_cfg = Rc::new(z3::Config::new());
        let z3_ctx = Rc::new(z3::Context::new(&z3_cfg));

        Self {
            ctx,
            z3_cfg,
            z3_ctx,
            solver: OnceCell::new(),
        }
    }
}

impl<'c, 's> HasContext<'c> for Z3Solver<'c, 's> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, 's> Solver<'c, 's> for Z3Solver<'c, 's>
where
    'c: 's,
{
    type Model = Z3Model<'c, 's>;

    fn add(&'s mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
        self.solver.get_or_init(|| z3::Solver::new(&self.z3_ctx));
        self.solver.get().unwrap().assert(
            &convert_astref_to_z3(constraint, &self.z3_ctx)?
                .as_bool()
                .ok_or(ClarirsError::TypeError(
                    "You can only add bools as solver constraints.".into(),
                ))?,
        );
        Ok(())
    }

    fn model(&'s mut self) -> Result<Self::Model, ClarirsError> {
        self.solver.get_or_init(|| z3::Solver::new(&self.z3_ctx));
        Ok(Z3Model {
            ctx: self.ctx,
            z3_ctx: &self.z3_ctx,
            model: self.solver.get().unwrap().get_model().unwrap(),
        })
    }
}

fn convert_astref_to_z3<'z>(
    ast: &AstRef,
    ctx: &'z z3::Context,
) -> Result<z3::ast::Dynamic<'z>, ClarirsError> {
    todo!()
}

fn convert_z3_to_astref<'c>(
    ast: z3::ast::Dynamic,
    ctx: &'c Context<'c>,
) -> Result<AstRef<'c>, ClarirsError> {
    match ast.sort_kind() {
        z3::SortKind::Bool => {
            let ast = ast.as_bool().unwrap();
            todo!()
        }
        _ => todo!(),
    }
}
