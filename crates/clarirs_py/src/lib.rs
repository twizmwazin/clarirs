//! The `claripy` Python extension module.
//!
//! Most of the bindings now live in `clarirs_core::python` (behind that crate's
//! `python` feature), which lets the AST conversion traits be implemented
//! directly on the core types. This crate is a thin shell that adds the pieces
//! which depend on `clarirs_z3` / `clarirs-vsa` — solvers and VSA queries —
//! since those crates depend on `clarirs_core` and so cannot live inside it.

#![allow(non_snake_case)]

mod dynsolver;
mod solver;
mod vsa;

/// Re-exports so the solver/VSA modules can keep using `crate::prelude` and
/// `crate::ast`, exactly as they did when they lived alongside the rest.
pub mod prelude {
    pub use clarirs_core::add_pyfunctions;
    pub use clarirs_core::python::prelude::*;
}

pub use clarirs_core::python::ast;

use clarirs_vsa::cardinality::Cardinality;
use clarirs_vsa::reduce::Reduce;
use clarirs_vsa::strided_interval::ComparisonResult;

use prelude::*;

/// Install the VSA-backed cardinality hooks that the core `BV`/`Bool`
/// `cardinality` getters dispatch through. See [`clarirs_core::python::vsa_hooks`].
fn install_vsa_hooks() {
    let _ = clarirs_core::python::vsa_hooks::BV_CARDINALITY.set(|ast| ast.cardinality());
    let _ = clarirs_core::python::vsa_hooks::BOOL_CARDINALITY.set(|ast| {
        Ok(match ast.reduce()?.into_bool()? {
            ComparisonResult::True | ComparisonResult::False => 1,
            ComparisonResult::Maybe => 2,
        })
    });
}

#[pymodule]
pub fn claripy(py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    install_vsa_hooks();

    // Everything that does not depend on solvers or VSA.
    clarirs_core::python::register(py, m)?;

    // Solver and VSA bindings, which depend on clarirs_z3 / clarirs-vsa.
    clarirs_core::python::import_submodule(py, m, "claripy", "solver", solver::import)?;
    clarirs_core::python::import_submodule(py, m, "claripy", "vsa", vsa::import)?;

    m.add_class::<solver::PySolver>()?;
    m.add_class::<solver::PyConcreteSolver>()?;
    m.add_class::<solver::PyVSASolver>()?;
    m.add_class::<solver::PyZ3Solver>()?;
    m.add_class::<solver::PyHybridSolver>()?;
    m.add_class::<solver::PyReplacementSolver>()?;
    m.add_class::<solver::PyCompositeSolver>()?;

    Ok(())
}
