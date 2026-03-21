mod astext;
mod solver;

pub use solver::Z3Solver;

use clarirs_core::cache::GenericCache;
use z3::ast::Dynamic;

thread_local! {
    static Z3_AST_CACHE: GenericCache<u64, Dynamic> = GenericCache::default();
}
