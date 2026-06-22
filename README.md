Clarirs
===

Clarirs is a rust implementation of claripy, an expression and constrint solving
library built for angr. Clarirs aims to be mostly compatible with claripy as
used in angr, but does not aim to be perfect drop in replacement or support all
features of claripy. Additionally, there is hope that the additional performance
of this rust implementation will allow for more complex solving and
simplification strategies to be implemented that increase overall performance,
serving as a platform for future research.

Clarirs is currently in the early stages of development and is not yet ready for
use in production. The API is subject to change and the library is not yet
feature complete. If you are interested in contributing to the project, issues,
pull requests, and feedback are all welcome. Feel free to reach out to the
maintainers with any questions or concerns via GitHub, the angr Discord, or
email.

## Requirements and Installation

Clairs requires the latest stable version of rust to build. To build the library
and run the tests, use cargo:

```bash
cargo build
cargo test
```

To build and test the python bindings, Python 3.10 or later is required. A venv
is reccomended. To build and install the python bindings, install with pip:

```bash
pip install .
```

For a python development install, it may be more efficient to use maturin to
build the python bindings:

```bash
maturin develop
```

See the [maturin user guide](https://www.maturin.rs) for more information on
using maturin.

### Linking against Z3

By default, clarirs builds Z3 from the bundled source tree (a git submodule) and
links it statically. This is fully self-contained: the resulting library and
wheels have no external Z3 dependency, but building takes longer and the wheels
are large.

As an opt-in alternative, clarirs can instead load Z3 at runtime from a shared
library — most usefully the one shipped in the
[`z3-solver`](https://pypi.org/project/z3-solver/) wheel. This avoids compiling
Z3, produces a much smaller wheel, and lets clarirs share a single Z3 with the
rest of an angr/claripy environment. Nothing is linked against Z3 at build time;
the library is discovered and `dlopen`ed at runtime.

To build the Python bindings in this mode, disable the default `static-link`
feature and enable `dynamic-link`. The Z3 headers are needed at build time to
generate the bindings; they are taken from the installed `z3-solver` package
automatically (or from `CLARIRS_Z3_INCLUDE_DIR` if set):

```bash
pip install z3-solver
maturin build --no-default-features --features dynamic-link
# or, for a development install:
maturin develop --no-default-features --features dynamic-link
```

At runtime the Z3 library is located in the following order:

1. `CLARIRS_Z3_LIBRARY` — full path to the Z3 shared library.
2. `CLARIRS_Z3_LIB_DIR` — directory containing the Z3 shared library.
3. The `lib/` directory of the installed `z3-solver` Python package.
4. The platform's default library search path (e.g. a system-wide `libz3`).

The same feature flags work for the Rust crates directly, for example:

```bash
cargo test -p clarirs_z3 --no-default-features --features dynamic-link
```

## Related works
Clarirs was not designed in a vacuum. The following projects have been
influential in the design and implementation of clarirs. If you use clarirs in
an academic work, please consider citing the following works:

- [claripy](https://github.com/angr/claripy): The original implementation of
    claripy in python.
- [angr](https://github.com/angr/angr): The symbolic execution engine and
    program analysis framework that claripy was originally developed for, and that
    clarirs aims to be used with.
- [z3](https://github.com/Z3Prover/z3): The SMT solver that claripy and clarirs
    use to solve constraints.
- [claricpp](https://github.com/angr/claripy/tree/ast-cpp): A C++ implementation
    of claripy that was developed as part of the angr project.

## License
Clarirs is free software licensed under the BSD 2-Clause License. See the
LICENSE file for more information.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in clarirs by you, shall be licensed under the BSD 2-Clause
License, without any additional terms or conditions.
