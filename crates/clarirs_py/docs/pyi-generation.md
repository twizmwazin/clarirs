# Exploration: generating `.pyi` type stubs for `claripy`

This document records an investigation into automatically generating Python type
stubs (`.pyi`) for the `clarirs_py` extension module (imported as `claripy`),
and a working proof-of-concept that proves the approach.

There are two candidate tools: PyO3's own built-in (experimental) introspection,
and the third-party `pyo3-stub-gen`. The *Two approaches* section compares them;
the short version is that PyO3's built-in generator cannot introspect clarirs's
function-style `#[pymodule]`, so the POC uses `pyo3-stub-gen`.

## TL;DR

- **It works.** [`pyo3-stub-gen`](https://github.com/Jij-Inc/pyo3-stub-gen)
  `0.23` supports `pyo3 >=0.27, <0.30`, so it is compatible with the `pyo3 0.29`
  that this crate already uses.
- A proof-of-concept wired up for the whole `claripy.vsa` submodule plus the AST
  class hierarchy compiles and emits correct stubs (see *Proof-of-concept*).
- Two clarirs-specific wrinkles need handling for a full rollout:
  1. clarirs's many submodules require pyo3-stub-gen's **mixed** Python/Rust
     layout (a `python-source` directory); the pure-Rust single-file layout it
     builds with today cannot represent submodules.
  2. `num_bigint::BigInt`/`BigUint` (used by `BVV`, `eval`, `min`, `max`, …)
     have **no** built-in `PyStubType`, so each such item needs a one-line
     `#[gen_stub(override_return_type(...))]` (or argument override).
- Everything else — submodule placement, cross-module type references, default
  arguments, class inheritance, docstrings — is produced automatically.

## Two approaches

### PyO3's built-in (experimental) introspection

PyO3 0.29 ships an `experimental-inspect` feature (`pyo3/experimental-inspect`,
present in our pinned version). With it enabled, the `#[pyclass]`/`#[pyfunction]`
macros embed JSON introspection fragments in the compiled `.so`, and
`pyo3-introspection` — driven by `maturin generate-stubs`,
`maturin build --generate-stubs`, or `maturin develop --generate-stubs` —
extracts them into `.pyi`. Its big attraction is **no per-item annotations at
all**.

**Why it does not fit clarirs today.** The PyO3 guide states introspection
*"only works with Python modules declared with an inline Rust module"* and that
*"content within `#[pymodule]` functions cannot be introspected; such modules
are marked incomplete."* clarirs's `#[pymodule] fn claripy(..)` is the
function-style form and builds everything imperatively at runtime —
`m.add_class`, the `add_pyfunctions!` macro, and `import_submodule` +
`py_run!("sys.modules[..] = ..")` for every submodule and compat shim. The
built-in generator cannot see into that; adopting it would require rewriting the
whole module to the declarative `#[pymodule] mod claripy { #[pymodule_export] ..}`
form, and some of clarirs's tricks (runtime `sys.modules` aliasing for
`claripy.fp`/`claripy.errors`, dynamic annotation re-exports) do not translate
cleanly. Submodule support in the built-in path is also still immature.

### pyo3-stub-gen (used by this POC)

Because you tag items explicitly and state their `module = "..."` yourself,
`pyo3-stub-gen` tolerates clarirs's imperative module construction — which is why
the POC below works without touching the module wiring. The trade-off is ~125
annotations and a couple of manual type overrides.

| | PyO3 built-in (`experimental-inspect`) | pyo3-stub-gen |
| --- | --- | --- |
| Per-item annotations | none | ~125 `gen_stub_*` tags |
| Works with clarirs's function-style `#[pymodule]` | **no** — needs declarative `mod` rewrite | **yes** (verified) |
| Submodules | immature/underspecified | works (mixed layout) |
| `BigInt` / custom `Coerce*` types | manual `INPUT_TYPE`/`OUTPUT_TYPE` impls | per-item `override_type` |
| Maturity | experimental | mature, finer control |

**Recommendation:** use `pyo3-stub-gen` now (it matches the current
architecture); revisit PyO3's built-in generator if/when the module is ever
migrated to declarative inline modules or the built-in path matures.

## How pyo3-stub-gen works

It is a compile-time + run-once tool, not a runtime reflector:

1. Annotate each exported item with a `gen_stub_*` macro placed **above** the
   PyO3 macro:
   - `#[gen_stub_pyclass]` above `#[pyclass]`
   - `#[gen_stub_pymethods]` above `#[pymethods]`
   - `#[gen_stub_pyfunction]` above `#[pyfunction]`

   These expand to `inventory::submit!` calls that register type info into a
   global registry at static-init time.
2. A gatherer function (`pub fn stub_info() -> Result<StubInfo>`) collects the
   registry.
3. A small binary (`src/bin/stub_gen.rs`) calls `stub_info()?.generate()?` to
   write the `.pyi` files. Run with `cargo run --bin stub_gen`.

Because the bin links the crate, `[lib]` must include `rlib` alongside the
`cdylib` that maturin builds.

## Proof-of-concept in this branch

The POC is intentionally scoped to one full submodule (`claripy.vsa`, 11
functions) plus the four AST classes its signatures reference (`Base`, `Bits`,
`Bool`, `BV`). It is enough to exercise every interesting code path.

Changes:

- `crates/clarirs_py/Cargo.toml` — add `pyo3-stub-gen` (default features off, to
  avoid pulling a `numpy`/`pyo3` version that conflicts with our pinned `pyo3`),
  and `crate-type = ["cdylib", "rlib"]`.
- `src/vsa.rs` — `#[gen_stub_pyfunction(module = "claripy.vsa")]` on all 11
  functions; the four `BigInt`/`BigUint`-returning ones also carry
  `#[gen_stub(override_return_type(type_repr = "int" | "list[int]"))]`.
- `src/ast/{base,bits,bool,bv}.rs` — `#[gen_stub_pyclass]` on the four classes
  (methods intentionally not annotated in the POC).
- `src/lib.rs` — the `stub_info()` gatherer.
- `src/bin/stub_gen.rs` — the generator binary.

### Generated output (verified)

`cargo run --bin stub_gen` produces a `claripy/` stub package. Highlights:

`stubs/claripy/vsa/__init__.pyi` (note the cross-module imports, the resolved
`BigInt` overrides, default arguments, and preserved docstrings):

```python
import builtins
from claripy.ast import base
from claripy.ast import bool
from claripy.ast import bv

def cardinality(expr: bv.BV) -> int: ...
def eval(expr: bv.BV, n: builtins.int) -> list[int]: ...
def has_false(expr: bool.Bool) -> builtins.bool: ...
def identical(a: base.Base, b: base.Base) -> builtins.bool: ...
def max(expr: bv.BV, signed: builtins.bool = ...) -> int: ...
def reduce(expr: base.Base) -> base.Base: ...
```

`stubs/claripy/ast/bv/__init__.pyi` (inheritance is captured from `extends=`):

```python
from claripy.ast import bits
class BV(bits.Bits): ...
```

The tool also generates the package `__init__.pyi` files with the right
submodule re-exports, e.g. `stubs/claripy/__init__.pyi` re-exports `ast` and
`vsa`.

### Reproducing

```bash
cargo run --bin stub_gen
# stubs land in crates/clarirs_py/stubs/ (gitignored)
```

The POC gatherer writes into a dedicated `stubs/` directory using
`StubInfo::from_project_root(.., is_mixed_layout = true, ..)`. This deliberately
keeps stub generation **independent of maturin's build configuration** so the
POC cannot perturb the real extension build. A production setup would instead
drive layout from `pyproject.toml` (see below).

> Note: in this environment `z3-sys` downloads a prebuilt Z3 via its
> `gh-release` feature using a `rustls` HTTP client that does not trust the
> sandbox's TLS-terminating proxy CA, so the download fails. That is unrelated
> to pyo3-stub-gen; pre-seeding the Z3 archive into the build cache lets the
> crate link and the generator run.

## What a full rollout needs

### 1. Switch to mixed layout

clarirs exposes `claripy.ast.base`, `claripy.ast.bv`, `claripy.vsa`,
`claripy.solver`, `claripy.annotation`, … pyo3-stub-gen refuses to emit
submodules in pure-Rust layout:

> Pure Rust layout does not support multiple modules or submodules … Please use
> mixed Python/Rust layout (add `python-source` to `[tool.maturin]`).

So production integration means adding `python-source` (e.g. `python/`) to
`[tool.maturin]`, which makes `python/claripy/` the package root that maturin
populates with the compiled module. This is a real structural change to the
package layout and **must be validated against `maturin build`/`develop`**
before adopting — it is the single biggest decision in this work. (`module-name
= "claripy"` is also added to `pyproject.toml`; it is a no-op for the current
build since it already matches the `[lib] name`, but it pins the name the stub
tool keys off.)

### 2. Annotate every exported item

Approximate surface in `crates/clarirs_py/src`:

| Macro | Count (approx) |
| --- | --- |
| `#[gen_stub_pyclass]` over `#[pyclass]` | ~22 |
| `#[gen_stub_pymethods]` over `#[pymethods]` | ~21 |
| `#[gen_stub_pyfunction]` over `#[pyfunction]` | ~82 |

Mostly mechanical. Two things need care:

- **Explicit `module = "..."`.** clarirs registers functions into submodules at
  runtime via `add_pyfunctions!`/`import_submodule`, which the macros cannot
  see. Each `#[gen_stub_pyfunction]` needs an explicit `module = "claripy.…"`
  matching the runtime placement (as done for `vsa`). Classes already declare
  `module = "…"` in their `#[pyclass]` attribute, which the tool reads for free.
- **`BigInt`/`BigUint` overrides.** No built-in `PyStubType`. Either add a
  per-item `#[gen_stub(override_return_type(type_repr = "int"))]` /
  `#[gen_stub(override_type(type_repr = "int"))]`, or implement `PyStubType` for
  these types once in a local newtype/helper to avoid repetition. Other custom
  coercion types (`CoerceBV`, `CoerceBool`, …) used in argument position will
  likewise need overrides or `PyStubType` impls.

### 3. Decide how the tool is built and shipped

In the POC, `pyo3-stub-gen` is an ordinary dependency, so its (small) code is
linked into the production `.so`. Cleaner options for a full rollout:

- Gate the dependency and the `gen_stub_*` annotations behind a `stub-gen`
  feature so release builds don't carry it, or
- Accept the dependency (this is what most pyo3-stub-gen projects do — the
  inventory data is small).

### 4. Wire generation into CI / build

Run `cargo run --bin stub_gen` in CI and fail if the committed stubs drift, and
add a `py.typed` marker so the stubs are honored by type checkers. `stubtest`
can validate stubs against the runtime module (with the caveat that it does not
fully support PyO3 nested submodules).

## Recommendation

Adopting `pyo3-stub-gen` is feasible and the per-item work is largely
mechanical. The gating decision is the **mixed-layout migration** (item 1): it
touches packaging, not just the Rust source. Suggested order:

1. Prototype the `python-source` mixed layout and confirm `maturin build`,
   `import claripy`, and the existing pytest suite still pass.
2. Add a reusable `PyStubType` story for `BigInt`/`BigUint` and the `Coerce*`
   types.
3. Annotate module-by-module (`vsa` is already done here), regenerating and
   eyeballing stubs as you go.
4. Add `py.typed` + a CI drift check.

## References

- pyo3-stub-gen: <https://github.com/Jij-Inc/pyo3-stub-gen>
- crates.io (compat `pyo3 >=0.27, <0.30`):
  <https://crates.io/crates/pyo3-stub-gen>
- PyO3 user guide, type-stub generation:
  <https://pyo3.rs/v0.29.0/type-stub>
