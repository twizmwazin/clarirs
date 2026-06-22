mod astext;
mod rc;
mod solver;

pub use solver::Z3Solver;

use ::z3 as z3hl;
use clarirs_core::cache::GenericCache;
use rc::RcAst;
use z3_sys as z3;

thread_local! {
    /// Raw handle to the high-level crate's thread-local Z3 context. clarirs_z3
    /// builds and introspects ASTs through the C API (`z3-sys`) but shares the
    /// single context that the `z3` crate manages, so high-level wrappers
    /// (`Solver`, `Model`, ...) and the raw ASTs interoperate.
    static Z3_CONTEXT: z3::Z3_context = z3hl::Context::thread_local().get_z3_context();

    static Z3_AST_CACHE: GenericCache<u64, RcAst> = GenericCache::default();
}

/// The high-level thread-local context, used to wrap raw ASTs into RAII handles.
pub(crate) fn z3_context() -> z3hl::Context {
    z3hl::Context::thread_local()
}

pub(crate) fn check_z3_error() -> Result<(), clarirs_core::error::ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let error_code = z3::Z3_get_error_code(*z3_ctx);
        if error_code != z3::ErrorCode::Ok {
            let err_msg = z3::Z3_get_error_msg(*z3_ctx, error_code);
            let c_str = std::ffi::CStr::from_ptr(err_msg);
            let msg = c_str.to_string_lossy().into_owned();
            Err(clarirs_core::error::ClarirsError::BackendError("Z3", msg))
        } else {
            Ok(())
        }
    })
}
