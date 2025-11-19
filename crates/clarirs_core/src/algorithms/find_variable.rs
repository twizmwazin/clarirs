use crate::prelude::*;

pub fn find_variable<'c>(ast: DynAst<'c>, name: &str) -> Option<DynAst<'c>> {
    let interned = ast.context().intern_string(name);
    if !ast.variables().contains(&interned) {
        return None;
    }

    ast.children()
        .into_iter()
        .find(|child| child.variables().contains(&interned))
        .and_then(|child| find_variable(child, name))
        .or(Some(ast))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_variable_not_present() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let result = find_variable(x.into(), "y");
        assert!(result.is_none());
        Ok(())
    }

    #[test]
    fn test_find_variable_at_root() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let result = find_variable(x.clone().into(), "x");
        assert!(result.is_some());
        assert_eq!(&result.unwrap().variables(), x.variables());
        Ok(())
    }

    #[test]
    fn test_find_variable_in_child() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let expr = ctx.add(&x, &y)?;

        let result = find_variable(expr.into(), "x");
        assert!(result.is_some());
        let found = result.unwrap();
        assert!(found.variables().contains("x"));
        Ok(())
    }

    #[test]
    fn test_find_variable_deeply_nested() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let z = ctx.bvs("z", 32)?;
        let expr = ctx.mul(&ctx.add(&x, &y)?, &z)?;

        let result = find_variable(expr.into(), "x");
        assert!(result.is_some());
        let found = result.unwrap();
        assert!(found.variables().contains("x"));
        // Should find the deepest node containing x
        assert!(!found.variables().contains("z"));

        Ok(())
    }
}
