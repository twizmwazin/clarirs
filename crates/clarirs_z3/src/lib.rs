mod astext;
mod rc;
mod solver;
pub(crate) mod z3_compat;

pub use solver::Z3Solver;

use clarirs_core::cache::GenericCache;
use z3_compat as z3;
use rc::RcAst;

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config();
        let ctx = z3::mk_context(cfg);
        z3::set_error_handler(ctx, None);
        z3::del_config(cfg);
        ctx
    };

    static Z3_AST_CACHE: GenericCache<u64, RcAst> = GenericCache::default();
}

pub(crate) fn check_z3_error() -> Result<(), clarirs_core::error::ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let error_code = z3::get_error_code(*z3_ctx);
        if error_code != z3::ErrorCode::OK {
            let err_msg = z3::get_error_msg(*z3_ctx, error_code);
            let c_str = std::ffi::CStr::from_ptr(err_msg);
            let msg = c_str.to_string_lossy().into_owned();
            Err(clarirs_core::error::ClarirsError::BackendError("Z3", msg))
        } else {
            Ok(())
        }
    })
}
