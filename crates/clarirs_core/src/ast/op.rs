use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

pub trait Op<'c>: Debug + Hash + Serialize {
    fn child_iter(&self) -> IntoIter<VarAst<'c>>;

    fn children(&self) -> Vec<VarAst<'c>> {
        self.child_iter().collect()
    }

    fn is_true(&self) -> bool {
        false
    }

    fn is_false(&self) -> bool {
        false
    }

    fn variables(&self) -> HashSet<String>;

    fn symbolic(&self) -> bool {
        !self.variables().is_empty()
    }

    fn concrete(&self) -> bool {
        self.variables().is_empty()
    }

    fn get_annotations(&self) -> Vec<Annotation>;
}
