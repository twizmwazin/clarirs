use std::collections::{BTreeSet, HashMap, HashSet};

use crate::prelude::*;

/// A composite solver that partitions constraints by their variables.
///
/// Independent constraint sets are solved in separate child solver instances,
/// which can significantly improve performance when constraints involve
/// disjoint variable sets. This mirrors the design of claripy's
/// `CompositeFrontend`.
///
/// The solver is parameterized over `S`, the backing solver type (e.g., Z3).
/// A fresh `template` solver is cloned whenever a new child is needed.
#[derive(Clone, Debug)]
pub struct CompositeSolver<'c, S: Solver<'c>> {
    ctx: &'c Context<'c>,
    template: S,
    children: HashMap<usize, S>,
    var_to_child: HashMap<InternedString, usize>,
    next_id: usize,
    /// Set when a concretely-false constraint is added. claripy's
    /// CompositeFrontend records the unsat state instead of raising from
    /// add(); unsat is reported by satisfiable() and value queries.
    unsat: bool,
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
            unsat: false,
        }
    }

    /// Iterate over the child solvers (one per independent constraint set).
    pub fn children_mut(&mut self) -> impl Iterator<Item = &mut S> {
        self.children.values_mut()
    }

    /// Return the child IDs that own any of the given variables (deduplicated).
    fn child_ids_for_vars(&self, vars: &BTreeSet<InternedString>) -> Vec<usize> {
        let set: HashSet<usize> = vars
            .iter()
            .filter_map(|v| self.var_to_child.get(v).copied())
            .collect();
        let mut ids: Vec<usize> = set.into_iter().collect();
        ids.sort();
        ids
    }

    /// Allocate a new child by cloning the template. Returns its ID.
    fn new_child(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.children.insert(id, self.template.clone());
        id
    }

    /// Merge all children in `ids[1..]` into `ids[0]`, updating variable
    /// mappings. Returns the surviving child ID.
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

        // Repoint variable mappings from removed children to `target`.
        let removed: HashSet<usize> = ids[1..].iter().copied().collect();
        for v in self.var_to_child.values_mut() {
            if removed.contains(v) {
                *v = target;
            }
        }

        Ok(target)
    }

    /// Execute `f` on the solver that contains the relevant variables for a
    /// query. When the variables span zero or one child the existing child is
    /// used directly; when they span multiple children a temporary merged
    /// solver is created.
    fn with_solver_for<T>(
        &mut self,
        vars: &BTreeSet<InternedString>,
        f: impl FnOnce(&mut S) -> Result<T, ClarirsError>,
    ) -> Result<T, ClarirsError> {
        let ids = self.child_ids_for_vars(vars);

        match ids.len() {
            0 => {
                // Variables not constrained — use a fresh solver.
                let mut solver = self.template.clone();
                f(&mut solver)
            }
            1 => f(self.children.get_mut(&ids[0]).unwrap()),
            _ => {
                // Build a temporary merged solver for the query.
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
            // Concrete constraint — record unsat if false. claripy does not
            // raise from add(); the unsat state surfaces on later queries.
            if constraint.is_false() {
                self.unsat = true;
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

        // Map all variables in this constraint to the target child.
        for v in vars {
            self.var_to_child.insert(v, target_id);
        }

        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.children.clear();
        self.var_to_child.clear();
        self.unsat = false;
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
        if self.unsat {
            return Ok(false);
        }
        for child in self.children.values_mut() {
            if !child.satisfiable()? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn satisfiable_with_extra(&mut self, extra: &[AstRef<'c>]) -> Result<bool, ClarirsError> {
        if extra.is_empty() {
            return self.satisfiable();
        }

        let mut vars: BTreeSet<InternedString> = BTreeSet::new();
        for constraint in extra {
            if constraint.variables().is_empty() {
                if constraint.is_false() {
                    return Ok(false);
                }
                continue;
            }
            vars.extend(constraint.variables().iter().cloned());
        }

        let ids = self.child_ids_for_vars(&vars);
        match ids.len() {
            0 => {
                // The extras are independent of all current constraints.
                let mut solver = self.template.clone();
                for constraint in extra {
                    solver.add(constraint)?;
                }
                if !solver.satisfiable()? {
                    return Ok(false);
                }
                self.satisfiable()
            }
            1 => {
                // Hot path: the extras only touch one child; that child's
                // scoped check is incremental, and the other children's plain
                // checks hit their persistent solvers.
                let id = ids[0];
                for (child_id, child) in self.children.iter_mut() {
                    if *child_id != id && !child.satisfiable()? {
                        return Ok(false);
                    }
                }
                self.children
                    .get_mut(&id)
                    .expect("child id from child_ids_for_vars")
                    .satisfiable_with_extra(extra)
            }
            _ => {
                // The extras span several children: merge them temporarily.
                let mut merged = self.template.clone();
                for &id in &ids {
                    for constraint in self.children[&id].constraints()? {
                        merged.add(&constraint)?;
                    }
                }
                for constraint in extra {
                    merged.add(constraint)?;
                }
                if !merged.satisfiable()? {
                    return Ok(false);
                }
                for (child_id, child) in self.children.iter_mut() {
                    if !ids.contains(child_id) && !child.satisfiable()? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
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
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.min_unsigned(expr))
    }

    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.max_unsigned(expr))
    }

    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.min_signed(expr))
    }

    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.max_signed(expr))
    }

    fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars = expr.variables().clone();
        self.with_solver_for(&vars, |s| s.eval_n(expr, n))
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

        // Add concrete constraints (no variables) — should succeed
        solver.add(&ctx.true_()?)?;
        assert!(solver.satisfiable()?);
        assert_eq!(solver.constraints()?.len(), 0); // concrete true is dropped

        Ok(())
    }

    #[test]
    fn test_composite_solver_unsat_concrete() {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let mut solver = CompositeSolver::new(&ctx, template);

        // Adding false succeeds (claripy does not raise from add); the unsat
        // state is reported by satisfiable().
        solver.add(&ctx.false_().unwrap()).unwrap();
        assert!(!solver.satisfiable().unwrap());

        // clear() resets the unsat state.
        solver.clear().unwrap();
        assert!(solver.satisfiable().unwrap());
    }

    #[test]
    fn test_composite_solver_partitioning() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let template = ConcreteSolver::new(&ctx);
        let solver = CompositeSolver::new(&ctx, template);

        // Two independent symbolic variables should go to different children.
        // ConcreteSolver doesn't actually store constraints, but we can verify
        // the partitioning logic via the child count.
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

    mod with_eq_model_solver {
        use super::*;
        use crate::solver::test_support::EqModelSolver;

        type TestComposite<'c> = CompositeSolver<'c, EqModelSolver<'c>>;

        fn new_solver<'c>(ctx: &'c Context<'c>) -> TestComposite<'c> {
            CompositeSolver::new(ctx, EqModelSolver::new(ctx))
        }

        fn bvv8<'c>(ctx: &'c Context<'c>, v: u64) -> Result<AstRef<'c>, ClarirsError> {
            ctx.bvv(BitVec::from((v, 8)))
        }

        /// Independent constraints go to separate children; a constraint
        /// spanning both merges them permanently (mirrors
        /// test_solver_split.py's grouping expectations).
        #[test]
        fn test_partitioning_and_merging() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;

            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 1)?)?)?;
            assert_eq!(solver.children.len(), 2);
            assert_ne!(
                solver.var_to_child[x.variables().first().unwrap()],
                solver.var_to_child[y.variables().first().unwrap()]
            );

            // A second constraint on x stays in x's child.
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            assert_eq!(solver.children.len(), 2);

            // x == y touches both children: they merge into one.
            solver.add(&ctx.eq_(&x, &y)?)?;
            assert_eq!(solver.children.len(), 1);
            assert_eq!(
                solver.var_to_child[x.variables().first().unwrap()],
                solver.var_to_child[y.variables().first().unwrap()]
            );

            // The surviving child holds all four constraints.
            assert_eq!(solver.constraints()?.len(), 4);
            assert!(solver.satisfiable()?);
            Ok(())
        }

        /// Transitively connected constraints end up in a single child
        /// (mirrors test_transitively_connected_constraints_stay_together).
        #[test]
        fn test_transitive_connection_single_child() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let a = ctx.bvs("a", 8)?;
            let b = ctx.bvs("b", 8)?;
            let c = ctx.bvs("c", 8)?;

            solver.add(&ctx.eq_(&a, &b)?)?;
            solver.add(&ctx.eq_(&b, &c)?)?;
            assert_eq!(solver.children.len(), 1);

            let variables = solver.variables()?;
            let vars: Vec<&str> = variables.iter().map(|v| v.as_str()).collect();
            assert_eq!(vars, vec!["a", "b", "c"]);
            Ok(())
        }

        /// Contradictory constraints on the same variable land in the same
        /// child and make it unsat (mirrors
        /// test_contradictory_concrete_constraints).
        #[test]
        fn test_contradiction_within_child() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 2)?)?)?;
            assert_eq!(solver.children.len(), 1);
            assert!(!solver.satisfiable()?);
            Ok(())
        }

        /// A contradiction only revealed by merging two children (x == 1,
        /// y == 2, then x == y) is detected after the merge.
        #[test]
        fn test_contradiction_across_children() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 2)?)?)?;
            assert!(solver.satisfiable()?);

            solver.add(&ctx.eq_(&x, &y)?)?;
            assert_eq!(solver.children.len(), 1);
            assert!(!solver.satisfiable()?);
            Ok(())
        }

        /// Adding concrete false makes an otherwise-satisfiable solver unsat
        /// (mirrors test_false_makes_otherwise_sat_solver_unsat), and value
        /// queries then report Unsat.
        #[test]
        fn test_concrete_false_poisons_solver() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 5)?)?)?;
            assert!(solver.satisfiable()?);

            solver.add(&ctx.false_()?)?;
            assert!(!solver.satisfiable()?);

            assert!(matches!(solver.eval_n(&x, 1), Err(ClarirsError::Unsat)));
            assert!(matches!(solver.min_unsigned(&x), Err(ClarirsError::Unsat)));
            assert!(matches!(solver.max_unsigned(&x), Err(ClarirsError::Unsat)));
            assert!(matches!(solver.min_signed(&x), Err(ClarirsError::Unsat)));
            assert!(matches!(solver.max_signed(&x), Err(ClarirsError::Unsat)));

            // clear() resets everything, including the unsat flag.
            solver.clear()?;
            assert!(solver.satisfiable()?);
            assert!(solver.children.is_empty());
            Ok(())
        }

        /// Queries route to the child owning the variables; queries over
        /// unconstrained variables use a fresh template; queries spanning
        /// children use a temporary merge that does not alter the partition.
        #[test]
        fn test_query_routing() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            let seven = bvv8(&ctx, 7)?;
            let nine = bvv8(&ctx, 9)?;
            solver.add(&ctx.eq_(&x, &seven)?)?;
            solver.add(&ctx.eq_(&y, &nine)?)?;
            assert_eq!(solver.children.len(), 2);

            // Single-child routing: each variable evaluates from its own
            // child (mirrors test_group_solvers_carry_their_constraints).
            assert_eq!(solver.eval(&x)?, seven);
            assert_eq!(solver.eval(&y)?, nine);
            assert_eq!(solver.min_unsigned(&x)?, seven);
            assert_eq!(solver.max_unsigned(&x)?, seven);
            assert_eq!(solver.min_signed(&y)?, nine);
            assert_eq!(solver.max_signed(&y)?, nine);

            // Concrete expression: no child owns its (empty) variable set, so
            // a fresh template solver answers.
            assert_eq!(solver.eval(&bvv8(&ctx, 3)?)?, bvv8(&ctx, 3)?);
            assert!(solver.is_true(&ctx.true_()?)?);
            assert!(solver.is_false(&ctx.false_()?)?);

            // A query spanning both children is answered by a temporary
            // merged solver: x + y == 16 given x == 7, y == 9.
            let sum_eq = ctx.eq_(&ctx.add(&x, &y)?, &bvv8(&ctx, 16)?)?;
            assert!(solver.is_true(&sum_eq)?);
            assert!(!solver.is_false(&sum_eq)?);
            assert!(solver.has_true(&sum_eq)?);
            assert!(!solver.has_false(&sum_eq)?);
            // The merge was temporary: the partition is unchanged.
            assert_eq!(solver.children.len(), 2);
            Ok(())
        }

        #[test]
        fn test_satisfiable_with_extra_concrete_extras() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 5)?)?)?;

            // Empty extras delegate to satisfiable().
            assert!(solver.satisfiable_with_extra(&[])?);
            // A concretely-false extra short-circuits to unsat.
            assert!(!solver.satisfiable_with_extra(&[ctx.false_()?])?);
            // A concretely-true extra is ignored.
            assert!(solver.satisfiable_with_extra(&[ctx.true_()?])?);
            Ok(())
        }

        /// Extras over variables no child owns are checked in a fresh solver.
        #[test]
        fn test_satisfiable_with_extra_unconstrained_vars() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let z = ctx.bvs("z", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 5)?)?)?;

            // Consistent extras on a fresh variable: still satisfiable.
            assert!(solver.satisfiable_with_extra(&[ctx.eq_(&z, &bvv8(&ctx, 3)?)?])?);
            // Self-contradictory extras on a fresh variable: unsat.
            assert!(!solver.satisfiable_with_extra(&[
                ctx.eq_(&z, &bvv8(&ctx, 3)?)?,
                ctx.eq_(&z, &bvv8(&ctx, 4)?)?,
            ])?);
            // The check was transient: no new child was created.
            assert_eq!(solver.children.len(), 1);
            Ok(())
        }

        /// Extras touching exactly one child use that child's scoped check
        /// and still verify the remaining children.
        #[test]
        fn test_satisfiable_with_extra_single_child() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 2)?)?)?;

            // Consistent extra on x's child.
            assert!(solver.satisfiable_with_extra(&[ctx.eq_(&x, &bvv8(&ctx, 1)?)?])?);
            // Contradictory extra on x's child.
            assert!(!solver.satisfiable_with_extra(&[ctx.eq_(&x, &bvv8(&ctx, 9)?)?])?);
            // The extras were transient: the persistent set is still sat.
            assert!(solver.satisfiable()?);

            // If a *different* child is already unsat, the answer is false
            // even when the extras themselves are consistent.
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 3)?)?)?; // y child now unsat
            assert!(!solver.satisfiable_with_extra(&[ctx.eq_(&x, &bvv8(&ctx, 1)?)?])?);
            Ok(())
        }

        /// Extras spanning several children are checked in a temporary
        /// merged solver, leaving the partition intact.
        #[test]
        fn test_satisfiable_with_extra_multi_child() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 1)?)?)?;
            assert_eq!(solver.children.len(), 2);

            // x == y is consistent with x == 1, y == 1.
            assert!(solver.satisfiable_with_extra(&[ctx.eq_(&x, &y)?])?);
            // x == y + something contradictory is not.
            assert!(
                !solver
                    .satisfiable_with_extra(&[ctx.eq_(&x, &y)?, ctx.eq_(&x, &bvv8(&ctx, 2)?)?,])?
            );
            // No permanent merge happened.
            assert_eq!(solver.children.len(), 2);
            Ok(())
        }

        /// The multi-child path also verifies children uninvolved in the
        /// extras.
        #[test]
        fn test_satisfiable_with_extra_multi_child_other_unsat() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            let z = ctx.bvs("z", 8)?;
            solver.add(&ctx.eq_(&x, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&y, &bvv8(&ctx, 1)?)?)?;
            // z's child is unsat.
            solver.add(&ctx.eq_(&z, &bvv8(&ctx, 1)?)?)?;
            solver.add(&ctx.eq_(&z, &bvv8(&ctx, 2)?)?)?;
            assert_eq!(solver.children.len(), 3);

            // The extra spans x and y (both fine), but the z child is unsat.
            assert!(!solver.satisfiable_with_extra(&[ctx.eq_(&x, &y)?])?);
            Ok(())
        }

        #[test]
        fn test_constraints_aggregates_children() -> Result<(), ClarirsError> {
            let ctx = Context::new();
            let mut solver = new_solver(&ctx);

            let x = ctx.bvs("x", 8)?;
            let y = ctx.bvs("y", 8)?;
            let c1 = ctx.eq_(&x, &bvv8(&ctx, 1)?)?;
            let c2 = ctx.eq_(&y, &bvv8(&ctx, 2)?)?;
            solver.add(&c1)?;
            solver.add(&c2)?;

            let constraints = solver.constraints()?;
            assert_eq!(constraints.len(), 2);
            assert!(constraints.contains(&c1));
            assert!(constraints.contains(&c2));

            // simplify() forwards to every child without error.
            solver.simplify()?;
            assert_eq!(solver.constraints()?.len(), 2);

            // children_mut() exposes each child exactly once.
            assert_eq!(solver.children_mut().count(), 2);
            Ok(())
        }
    }
}
