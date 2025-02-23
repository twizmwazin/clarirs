mod astext;
mod rc;
mod solver;

use clarirs_z3_sys as z3;

thread_local! {
    static Z3_CONTEXT: z3::Context = unsafe {
        let cfg = z3::mk_config();
        let ctx = z3::mk_context(cfg);
        z3::del_config(cfg);
        ctx
    }
}

pub use solver::Z3Solver;
