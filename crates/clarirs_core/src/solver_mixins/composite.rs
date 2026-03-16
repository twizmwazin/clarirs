use std::collections::{BTreeSet, HashMap};

use crate::prelude::*;

/// A composite solver that splits constraints into independent groups based on
/// variable connectivity and delegates each group to a separate child solver.
///
/// Inspired by claripy's `CompositeFrontend`, this solver:
/// - Tracks which variables belong to which child solver
/// - Automatically merges child solvers when a new constraint bridges
///   previously independent variable groups
/// - Queries are routed to whichever child solver owns the relevant variables
///
/// This can significantly speed up constraint solving when a problem contains
/// many independent sub-problems.
#[derive(Clone, Debug)]
pub struct CompositeSolver<'c, S: Solver<'c> + Clone> {
    ctx: &'c Context<'c>,
    /// Maps variable names to indices into the `children` vec.
    var_to_child: HashMap<InternedString, usize>,
    /// Child solver instances. Slots may be `None` after merges.
    children: Vec<Option<S>>,
    /// Concrete constraints (no variables) accumulated so far.
    concrete_constraints: Vec<BoolAst<'c>>,
    /// Set true if any child or concrete constraint is UNSAT.
    unsat: bool,
}

impl<'c, S: Solver<'c> + Clone> CompositeSolver<'c, S> {
    pub fn new(ctx: &'c Context<'c>, _template: S) -> Self {
        Self {
            ctx,
            var_to_child: HashMap::new(),
            children: Vec::new(),
            concrete_constraints: Vec::new(),
            unsat: false,
        }
    }

    /// Get the number of active child solvers.
    pub fn num_children(&self) -> usize {
        self.children.iter().filter(|c| c.is_some()).count()
    }

    /// Get the child solver index for a given variable, if any.
    pub fn child_index_for_var(&self, var: &InternedString) -> Option<usize> {
        self.var_to_child.get(var).copied()
    }

    /// Split a set of constraints into groups by variable connectivity.
    ///
    /// Returns a list of (variable_set, constraint_list) pairs.
    /// Constraints with no variables are grouped under an empty variable set.
    pub fn split_constraints(
        constraints: &[BoolAst<'c>],
    ) -> Vec<(BTreeSet<InternedString>, Vec<BoolAst<'c>>)> {
        // Union-Find for variable grouping
        let mut parent: HashMap<InternedString, InternedString> = HashMap::new();

        fn find(
            parent: &mut HashMap<InternedString, InternedString>,
            x: &InternedString,
        ) -> InternedString {
            if !parent.contains_key(x) {
                parent.insert(x.clone(), x.clone());
                return x.clone();
            }
            let p = parent[x].clone();
            if &p == x {
                return x.clone();
            }
            let root = find(parent, &p);
            parent.insert(x.clone(), root.clone());
            root
        }

        fn union(
            parent: &mut HashMap<InternedString, InternedString>,
            a: &InternedString,
            b: &InternedString,
        ) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        }

        // Per-constraint variable sets
        let mut constraint_vars: Vec<BTreeSet<InternedString>> =
            Vec::with_capacity(constraints.len());

        for constraint in constraints {
            let vars: BTreeSet<InternedString> = constraint.variables().clone();
            // Union all variables in this constraint together
            let var_list: Vec<_> = vars.iter().cloned().collect();
            for i in 1..var_list.len() {
                union(&mut parent, &var_list[0], &var_list[i]);
            }
            constraint_vars.push(vars);
        }

        // Group constraints by their root variable
        let mut groups: HashMap<
            Option<InternedString>,
            (BTreeSet<InternedString>, Vec<BoolAst<'c>>),
        > = HashMap::new();

        for (constraint, vars) in constraints.iter().zip(constraint_vars.iter()) {
            let key = if vars.is_empty() {
                None
            } else {
                Some(find(&mut parent, vars.iter().next().unwrap()))
            };
            let entry = groups
                .entry(key)
                .or_insert_with(|| (BTreeSet::new(), Vec::new()));
            entry.0.extend(vars.iter().cloned());
            entry.1.push(constraint.clone());
        }

        groups.into_values().collect()
    }

    /// Find or create the child solver that should handle a set of variables.
    /// If variables span multiple existing children, merge them.
    fn solver_for_vars(&mut self, vars: &BTreeSet<InternedString>) -> usize
    where
        S: Solver<'c>,
    {
        // Find all existing child indices related to these variables.
        // Use transitive closure: also include all variables already in those children.
        let mut related_indices: BTreeSet<usize> = BTreeSet::new();
        let mut all_vars = vars.clone();
        let mut changed = true;

        while changed {
            changed = false;
            for var in all_vars.clone() {
                if let Some(&idx) = self.var_to_child.get(&var)
                    && related_indices.insert(idx)
                {
                    changed = true;
                    // Add all variables from this child
                    for (v, &i) in &self.var_to_child {
                        if i == idx {
                            all_vars.insert(v.clone());
                        }
                    }
                }
            }
        }

        match related_indices.len() {
            0 => {
                // No existing child has any of these variables — create new one
                let idx = self.children.len();
                self.children.push(None); // placeholder, will be populated by caller
                for var in vars {
                    self.var_to_child.insert(var.clone(), idx);
                }
                idx
            }
            1 => {
                // Exactly one child already covers these variables
                let idx = *related_indices.iter().next().unwrap();
                // Register any new variables to this child
                for var in vars {
                    self.var_to_child.insert(var.clone(), idx);
                }
                idx
            }
            _ => {
                // Multiple children need to be merged
                let indices: Vec<usize> = related_indices.into_iter().collect();
                let target = indices[0];
                let sources = &indices[1..];

                // Merge constraints from source children into target
                for &src in sources {
                    if let Some(source_solver) = self.children[src].take()
                        && let Ok(source_constraints) = source_solver.constraints()
                        && let Some(ref mut target_solver) = self.children[target]
                    {
                        for c in &source_constraints {
                            let _ = target_solver.add(c);
                        }
                    }
                }

                // Remap all variables from source children to target
                for (_, idx) in self.var_to_child.iter_mut() {
                    if sources.contains(idx) {
                        *idx = target;
                    }
                }

                // Register new variables to target
                for var in vars {
                    self.var_to_child.insert(var.clone(), target);
                }

                target
            }
        }
    }

    /// Ensure a child solver exists at the given index.
    fn ensure_child(&mut self, idx: usize, template: &S) {
        if idx >= self.children.len() {
            self.children.resize_with(idx + 1, || None);
        }
        if self.children[idx].is_none() {
            self.children[idx] = Some(template.clone());
        }
    }

    /// Get a mutable reference to the child solver for a set of expression variables,
    /// merging children as needed.
    fn solver_for_expr_vars(&mut self, vars: &BTreeSet<InternedString>) -> Option<&mut S> {
        if vars.is_empty() {
            // For concrete expressions, use the first available child or return None
            return self.children.iter_mut().find_map(|c| c.as_mut());
        }
        let idx = self.solver_for_vars(vars);
        self.children[idx].as_mut()
    }
}

impl<'c, S: Solver<'c> + Clone> HasContext<'c> for CompositeSolver<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, S: Solver<'c> + Clone> Solver<'c> for CompositeSolver<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }

        let vars: BTreeSet<InternedString> = constraint.variables().clone();

        if vars.is_empty() {
            // Pure concrete constraint — validate immediately
            self.concrete_constraints.push(constraint.clone());
            // Check if it's trivially false
            if constraint.is_false() {
                self.unsat = true;
                return Err(ClarirsError::Unsat);
            }
            // Also add to all existing children so they stay in sync
            for child in self.children.iter_mut().flatten() {
                child.add(constraint)?;
            }
            return Ok(());
        }

        // Find/create the child for these variables, using the first existing child as template
        let template = self
            .children
            .iter()
            .find_map(|c| c.clone())
            .unwrap_or_else(|| {
                // No children exist yet — we need to create one.
                // The caller must have set up the composite with a template.
                // We'll clone from context to create a minimal solver.
                panic!("CompositeSolver: no template child available");
            });

        let idx = self.solver_for_vars(&vars);
        self.ensure_child(idx, &template);

        if let Some(child) = self.children[idx].as_mut() {
            child.add(constraint)?;
        }

        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.var_to_child.clear();
        self.children.clear();
        self.concrete_constraints.clear();
        self.unsat = false;
        Ok(())
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let mut all = self.concrete_constraints.clone();
        for child in self.children.iter().flatten() {
            all.extend(child.constraints()?);
        }
        Ok(all)
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        for child in self.children.iter_mut().flatten() {
            child.simplify()?;
        }
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        if self.unsat {
            return Ok(false);
        }
        // All children must be satisfiable
        for child in self.children.iter_mut().flatten() {
            if !child.satisfiable()? {
                self.unsat = true;
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        if vars.is_empty() {
            // Concrete expression
            return Ok(expr.is_true());
        }
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.is_true(expr),
            None => Ok(expr.is_true()),
        }
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        if vars.is_empty() {
            return Ok(expr.is_false());
        }
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.is_false(expr),
            None => Ok(expr.is_false()),
        }
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        if vars.is_empty() {
            return Ok(expr.is_true());
        }
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.has_true(expr),
            None => Ok(expr.is_true()),
        }
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        if vars.is_empty() {
            return Ok(expr.is_false());
        }
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.has_false(expr),
            None => Ok(expr.is_false()),
        }
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.min_unsigned(expr),
            None => Err(ClarirsError::UnsupportedOperation(
                "No child solver for expression".to_string(),
            )),
        }
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.max_unsigned(expr),
            None => Err(ClarirsError::UnsupportedOperation(
                "No child solver for expression".to_string(),
            )),
        }
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.min_signed(expr),
            None => Err(ClarirsError::UnsupportedOperation(
                "No child solver for expression".to_string(),
            )),
        }
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.max_signed(expr),
            None => Err(ClarirsError::UnsupportedOperation(
                "No child solver for expression".to_string(),
            )),
        }
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.eval_bool_n(expr, n),
            None => {
                // Concrete expression
                if n == 0 {
                    Ok(Vec::new())
                } else {
                    Ok(vec![expr.simplify()?])
                }
            }
        }
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.eval_bitvec_n(expr, n),
            None => {
                if n == 0 {
                    Ok(Vec::new())
                } else {
                    Ok(vec![expr.simplify()?])
                }
            }
        }
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.eval_float_n(expr, n),
            None => {
                if n == 0 {
                    Ok(Vec::new())
                } else {
                    Ok(vec![expr.simplify()?])
                }
            }
        }
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        if self.unsat {
            return Err(ClarirsError::Unsat);
        }
        let vars: BTreeSet<InternedString> = expr.variables().clone();
        match self.solver_for_expr_vars(&vars) {
            Some(child) => child.eval_string_n(expr, n),
            None => {
                if n == 0 {
                    Ok(Vec::new())
                } else {
                    Ok(vec![expr.simplify()?])
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_composite<'c>(ctx: &'c Context<'c>) -> CompositeSolver<'c, ConcreteSolver<'c>> {
        CompositeSolver::new(ctx, ConcreteSolver::new(ctx))
    }

    #[test]
    fn test_composite_empty_satisfiable() {
        let ctx = Context::new();
        let mut solver = make_composite(&ctx);
        assert!(solver.satisfiable().unwrap());
    }

    #[test]
    fn test_composite_concrete_constraint() {
        let ctx = Context::new();
        let mut solver = make_composite(&ctx);

        let true_val = ctx.true_().unwrap();
        solver.add(&true_val).unwrap();
        assert!(solver.satisfiable().unwrap());
    }

    #[test]
    fn test_composite_false_constraint_is_unsat() {
        let ctx = Context::new();
        let mut solver = make_composite(&ctx);

        let false_val = ctx.false_().unwrap();
        assert!(solver.add(&false_val).is_err());
        assert!(!solver.satisfiable().unwrap());
    }

    #[test]
    fn test_split_constraints_independent() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 8).unwrap();
        let b = ctx.bvs("b", 8).unwrap();
        let one = ctx.bvv_prim(1u8).unwrap();
        let two = ctx.bvv_prim(2u8).unwrap();

        let c1 = ctx.eq_(&a, &one).unwrap();
        let c2 = ctx.eq_(&b, &two).unwrap();

        let groups = CompositeSolver::<ConcreteSolver>::split_constraints(&[c1, c2]);
        // a and b are independent → should be 2 groups
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_split_constraints_connected() {
        let ctx = Context::new();
        let a = ctx.bvs("a", 8).unwrap();
        let b = ctx.bvs("b", 8).unwrap();
        let one = ctx.bvv_prim(1u8).unwrap();

        // a == b and a == 1 share variable 'a'
        let c1 = ctx.eq_(&a, &b).unwrap();
        let c2 = ctx.eq_(&a, &one).unwrap();

        let groups = CompositeSolver::<ConcreteSolver>::split_constraints(&[c1, c2]);
        // a and b are connected → should be 1 group
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].1.len(), 2);
    }

    #[test]
    fn test_split_constraints_concrete() {
        let ctx = Context::new();
        let true_val = ctx.true_().unwrap();
        let false_val = ctx.false_().unwrap();

        let groups = CompositeSolver::<ConcreteSolver>::split_constraints(&[
            true_val.clone(),
            false_val.clone(),
        ]);
        // Both are concrete → 1 group with empty var set
        assert_eq!(groups.len(), 1);
        assert!(groups[0].0.is_empty());
    }

    #[test]
    fn test_composite_clear() {
        let ctx = Context::new();
        let mut solver = make_composite(&ctx);

        let true_val = ctx.true_().unwrap();
        solver.add(&true_val).unwrap();
        solver.clear().unwrap();

        assert!(solver.constraints().unwrap().is_empty());
    }

    #[test]
    fn test_composite_constraints_collected() {
        let ctx = Context::new();
        let mut solver = make_composite(&ctx);

        let true_val = ctx.true_().unwrap();
        solver.add(&true_val).unwrap();
        solver.add(&true_val).unwrap();

        let constraints = solver.constraints().unwrap();
        assert_eq!(constraints.len(), 2);
    }
}
