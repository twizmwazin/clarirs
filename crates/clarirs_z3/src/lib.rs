mod astext;
mod rc;
mod solver;

pub use solver::Z3Solver;

use clarirs_core::cache::GenericCache;
use rc::RcAst;

thread_local! {
    static Z3_CONTEXT: z3_sys::Z3_context = unsafe {
        let cfg = z3_sys::Z3_mk_config().expect("Z3_mk_config returned null");
        let ctx = z3_sys::Z3_mk_context(cfg).expect("Z3_mk_context returned null");
        z3_sys::Z3_set_error_handler(ctx, None);
        z3_sys::Z3_del_config(cfg);
        ctx
    };

    static Z3_AST_CACHE: GenericCache<u64, RcAst> = GenericCache::default();
}

pub(crate) fn check_z3_error() -> Result<(), clarirs_core::error::ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let error_code = z3_sys::Z3_get_error_code(*z3_ctx);
        if error_code != z3_sys::ErrorCode::OK {
            let err_msg = z3_sys::Z3_get_error_msg(*z3_ctx, error_code);
            let c_str = std::ffi::CStr::from_ptr(err_msg);
            let msg = c_str.to_string_lossy().into_owned();
            Err(clarirs_core::error::ClarirsError::BackendError("Z3", msg))
        } else {
            Ok(())
        }
    })
}
