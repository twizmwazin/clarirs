pub mod canonicalize;
pub mod collect_vars;
pub mod dfs;
pub mod excavate_ite;
pub mod find_variable;
pub mod join;
pub mod post_order;
pub mod replace;
pub mod simplify;

pub use canonicalize::{canonicalize, structurally_match};
pub use excavate_ite::ExcavateIte;
pub use join::Join;
pub use post_order::walk_post_order;
pub use replace::Replace;
pub use simplify::Simplify;
