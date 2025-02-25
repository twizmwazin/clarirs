mod astext;
mod rc;
mod solver;

use clarirs_z3_sys as z3;

/// Error handler that panics on Z3 errors
unsafe extern "C" fn panic_on_error(_: z3::Context, e: z3::ErrorCode) {
    panic!("Z3 error: {:?}", e);
}

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config();
        let ctx = z3::mk_context_rc(cfg);
        z3::set_error_handler(ctx, Some(panic_on_error));
        z3::del_config(cfg);
        ctx
    }
}

pub use solver::Z3Solver;
