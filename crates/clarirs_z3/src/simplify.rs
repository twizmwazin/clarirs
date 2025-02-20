use clarirs_z3_sys as z3;

/// Simplifies the given Z3 AST by wrapping `z3::simplify` and auto-incrementing
/// the ref count.
pub(crate) fn simplify(ctx: z3::Context, ast: z3::Ast) -> z3::Ast {
    unsafe {
        let simplified_ast = z3::simplify(ctx, ast);
        z3::inc_ref(ctx, ast);
        simplified_ast
    }
}
