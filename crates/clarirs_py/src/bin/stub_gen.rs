//! Generates the Python type stub (`.pyi`) files for the `claripy` extension
//! module from the `gen_stub_*` annotations in the crate.
//!
//! Run with `cargo run --bin stub_gen` (or `maturin develop` followed by the
//! same). Output paths are derived from `[tool.maturin]` in the workspace
//! `pyproject.toml`.

fn main() -> pyo3_stub_gen::Result<()> {
    let stub = claripy::stub_info()?;
    stub.generate()?;
    Ok(())
}
