mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use crate::prelude::*;

macro_rules! simplify {
    ($($var:ident),*) => {
        $(let $var = $var.simplify()?;)*
    };
}

pub(crate) use simplify;

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError>;
}
