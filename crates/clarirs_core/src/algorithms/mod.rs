pub mod canonicalize;
pub mod collect_vars;
pub mod dfs;
pub mod excavate_ite;
pub mod find_variable;
pub mod join;
pub mod post_order;
pub mod pre_order;
pub mod reconstruct;
pub mod replace;
pub mod replace_dict;
pub mod simplify;

pub use canonicalize::{canonicalize, structurally_match};
pub use excavate_ite::ExcavateIte;
pub use join::Join;
pub use post_order::walk_post_order;
pub use pre_order::walk_pre_order;
pub use replace::Replace;
pub use replace_dict::{
    replace_dict, replace_dict_bitvec, replace_dict_bool, replace_dict_float, replace_dict_string,
};
pub use simplify::Simplify;
