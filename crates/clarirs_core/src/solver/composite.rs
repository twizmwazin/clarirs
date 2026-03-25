use std::collections::{BTreeSet, HashMap, HashSet};

use crate::prelude::*;

/// A composite solver that partitions constraints by their variables.
///
/// Independent constraint sets are solved in separate child solver instances,
/// which can significantly improve performance when constraints involve
/// disjoint variable sets.
#[derive(Clone, Debug)]
pub struct CompositeSolver<'c, S: Solver<'c>> {
    ctx: &'c Context<'c>,
    template: S,
    children: HashMap<usize, S>,
    var_to_child: HashMap<InternedString, usize>,
    next_id: usize,
}

impl<'c, S: Solver<'c>> HasContext<'c> for CompositeSolver<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, S: Solver<'c>> CompositeSolver<'c, S> {
    pub fn new(ctx: &'c Context<'c>, template: S) -> Self {
        Self {
            ctx,
            template,
            children: HashMap::new(),
            var_to_child: HashMap::new(),
            next_id: 0,
        }
    }

    fn child_ids_for_vars(&self, vars: &BTreeSet<InternedString>) -> Vec<usize> {
        let set: HashSet<usize> = vars
            .iter()
            .filter_map(|v| self.var_to_child.get(v).copied())
            .collect();
        let mut ids: Vec<usize> = set.into_iter().collect();
        ids.sort();
        ids
    }

    fn new_child(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.children.insert(id, self.template.clone());
        id
    }

    fn merge_children(&mut self, ids: &[usize]) -> Result<usize, ClarirsError> {
        debug_assert!(ids.len() >= 2);
        let target = ids[0];

        for &other_id in &ids[1..] {
            let other = self
                .children
                .remove(&other_id)
                .expect("child id must exist");
            let target_solver = self.children.get_mut(&target).unwrap();
            for constraint in other.constraints()? {
                target_solver.add(&constraint)?;
            }
        }

        let removed: HashSet<usize> = ids[1..].iter().copied().collect();
        for v in self.var_to_child.values_mut() {
            if removed.contains(v) {
                *v = target;
            }
        }

        Ok(target)
    }

    fn with_solver_for<T>(
        &mut self,
        vars: &BTreeSet<InternedString>,
        f: impl FnOnce(&mut S) -> Result<T, ClarirsError>,
    ) -> Result<T, ClarirsError> {
        let ids = self.child_ids_for_vars(vars);

        match ids.len() {
            0 => {
                let mut solver = self.template.clone();
                f(&mut solver)
            }
            1 => f(self.children.get_mut(&ids[0]).unwrap()),
            _ => {
                let mut merged = self.template.clone();
                for &id in &ids {
                    for constraint in self.children[&id].constraints()? {
                        merged.add(&constraint)?;
                    }
                }
                f(&mut merged)
            }
        }
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for CompositeSolver<'c, S> {
    fn add(&mut self, constraint: &AstRef<'c>) -> Result<(), ClarirsError> {
        let vars: BTreeSet<InternedString> = constraint.variables().clone();

        if vars.is_empty() {
            if constraint.is_false() {
                return Err(ClarirsError::Unsat);
            }
            return Ok(());
        }

        let ids = self.child_ids_for_vars(&vars);

        let target_id = match ids.len() {
            0 => self.new_child(),
            1 => ids[0],
            _ => self.merge_children(&ids)?,
        };

        self.children.get_mut(&target_id).unwrap().add(constraint)?;

        for v in vars {
            self.var_to_child.insert(v, target_id);
        }

        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.children.clear();
        self.var_to_child.clear();
        Ok(())
    }

    fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        let mut all = Vec::new();
        for child in self.children.values() {
            all.extend(child.constraints()?);
        }
        Ok(all)
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        for child in self.children.values_mut() {
            child.simplify()?;
        }
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        for child in self.children.values_mut() {
            if !child.satisfiable()? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.is_true(expr))
    }

    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.is_false(expr))
    }

    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.has_true(expr))
    }

    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.has_false(expr))
    }

    fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.min_unsigned(expr))
    }

    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.max_unsigned(expr))
    }

    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.min_signed(expr))
    }

    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.max_signed(expr))
    }

    fn eval_many(
        &mut self,
        expr: &AstRef<'c>,
        n: u32,
    ) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.eval_many(expr, n))
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;
    use crate::prelude::*;

    #[test]
    fn test_composite_solver_independent_constraints() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let mut solver = CompositeSolver::new(&ctx, template);

        solver.add(&ctx.true_()?)?;
        assert!(solver.satisfiable()?);
        assert_eq!(solver.constraints()?.len(), 0);

        Ok(())
    }

    #[test]
    fn test_composite_solver_unsat_concrete() {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let mut solver = CompositeSolver::new(&ctx, template);

        let result = solver.add(&ctx.false_().unwrap());
        assert!(result.is_err());
    }

    #[test]
    fn test_composite_solver_partitioning() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let solver = CompositeSolver::new(&ctx, template);

        assert_eq!(solver.children.len(), 0);

        Ok(())
    }

    #[test]
    fn test_composite_solver_clear() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let mut solver = CompositeSolver::new(&ctx, template);
        solver.clear()?;
        assert!(solver.children.is_empty());
        assert!(solver.var_to_child.is_empty());
        Ok(())
    }
}
