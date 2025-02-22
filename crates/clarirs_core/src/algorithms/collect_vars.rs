use std::collections::HashSet;

use crate::prelude::*;

use super::dfs::{walk_dfs, DfsResult};

#[allow(clippy::mutable_key_type)]
pub fn collect_vars<'c>(ast: &VarAst<'c>) -> Result<HashSet<VarAst<'c>>, ClarirsError> {
    let mut vars: HashSet<VarAst<'c>> = HashSet::new();
    let mut interesting: HashSet<String> = ast.variables();

    walk_dfs(ast, |node| {
        if interesting.is_empty() {
            // We have all the variables we need
            return DfsResult::Stop;
        }

        if !node.symbolic() {
            // Variables are always symbolic
            return DfsResult::SkipChildren;
        }

        let intersect: Vec<String> = node.variables().intersection(&interesting).cloned().collect();

        match intersect.len() {
            0 => DfsResult::SkipChildren,
            1 if node.depth() == 1 => {
                // We found a variable
                vars.insert(node.clone());
                interesting.remove(&intersect[0]);
                DfsResult::Continue
            },
            _ => DfsResult::Continue,
        }

    })?;

   Ok(vars)

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_collect_vars() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let ast = ctx.add(
            &ctx.bvs("a", 64)?,
            &ctx.mul(&ctx.bvs("b", 64)?, &ctx.bvs("c", 64)?)?,
        )?;
        let var_ast = VarAst::from(&ast);

        let vars = collect_vars(&var_ast)?;

        assert_eq!(vars.len(), 3);

        Ok(())
    }

    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_collect_vars_with_repeated_vars() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let ast = ctx.add(
            &ctx.bvs("a", 64)?,
            &ctx.mul(&ctx.bvs("a", 64)?, &ctx.bvs("c", 64)?)?,
        )?;
        let var_ast = VarAst::from(&ast);

        let vars = collect_vars(&var_ast)?;

        assert_eq!(vars.len(), 2);

        Ok(())
    }
}
