mod astext;
mod rc;
mod solver;
mod z3;

pub use solver::Z3Solver;

use clarirs_core::cache::GenericCache;
use clarirs_core::error::ClarirsError;
use rc::RcAst;

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config().expect("Z3_mk_config returned null");
        let ctx = z3::mk_context(cfg).expect("Z3_mk_context returned null");
        z3::set_error_handler(ctx, None);
        z3::del_config(cfg);
        ctx
    };

    static Z3_AST_CACHE: GenericCache<u64, RcAst> = GenericCache::default();
}

/// Convert a nullable `z3-sys` result into a [`ClarirsError`].
///
/// Pointer-returning Z3 functions yield `None` (rather than a null pointer) when
/// Z3 hits an internal error or an invalid request. Results that become an
/// [`RcAst`] are checked via `RcAst::try_from(Option<_>)`; this helper covers the
/// few intermediate handles (sorts, symbols, solvers, …) that are not. The
/// precise cause, when Z3 set one, is surfaced by [`check_z3_error`].
pub(crate) fn require<T>(value: Option<T>) -> Result<T, ClarirsError> {
    value.ok_or_else(|| ClarirsError::BackendError("Z3", "Z3 returned a null pointer".into()))
}

pub(crate) fn check_z3_error() -> Result<(), clarirs_core::error::ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let error_code = z3::get_error_code(*z3_ctx);
        if error_code != z3::ErrorCode::Ok {
            let err_msg = z3::get_error_msg(*z3_ctx, error_code);
            let c_str = std::ffi::CStr::from_ptr(err_msg);
            let msg = c_str.to_string_lossy().into_owned();
            Err(clarirs_core::error::ClarirsError::BackendError("Z3", msg))
        } else {
            Ok(())
        }
    })
}
