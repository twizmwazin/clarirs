mod astext;
mod rc;
mod solver;

pub use solver::Z3Solver;

use clarirs_z3_sys as z3;

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config();
        let ctx = z3::mk_context(cfg);
        z3::del_config(cfg);
        ctx
    }
}

pub(crate) fn get_z3_error_msg() -> String {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let error_code = z3::get_error_code(*z3_ctx);
        let err_msg = z3::get_error_msg(*z3_ctx, error_code);
        let c_str = std::ffi::CStr::from_ptr(err_msg);
        c_str.to_string_lossy().into_owned()
    })
}
