use std::env;
use std::path::PathBuf;
use std::process::Command;

use bindgen::callbacks::{EnumVariantValue, ItemInfo, ItemKind, ParseCallbacks};

#[derive(Debug, Default)]
struct RenameTypes;

impl ParseCallbacks for RenameTypes {
    fn item_name(&self, item_info: ItemInfo) -> Option<String> {
        item_info
            .name
            // Strip Z3_ prefix from item names
            .strip_prefix("Z3_")
            .map(|s| {
                match item_info.kind {
                    // Leave function names as is
                    ItemKind::Function => s.to_string(),
                    // Convert snake_case to PascalCase
                    ItemKind::Type => s
                        .split('_')
                        .filter(|s| !s.is_empty())
                        .map(|s| {
                            let lowered = s.to_lowercase();
                            let mut chars = lowered.chars();
                            match chars.next() {
                                None => String::new(),
                                Some(first) => {
                                    first.to_uppercase().collect::<String>() + chars.as_str()
                                }
                            }
                        })
                        .collect::<String>(),
                    _ => s.to_string(),
                }
            })
    }

    fn enum_variant_name(
        &self,
        enum_name: Option<&str>,
        original_variant_name: &str,
        _variant_value: EnumVariantValue,
    ) -> Option<String> {
        // Remove Z3_ prefix from enum variants
        original_variant_name
            .strip_prefix("Z3_")
            // Convert snake_case to PascalCase
            .map(|s| {
                s.split('_')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        let lowered = s.to_lowercase();
                        let mut chars = lowered.chars();
                        match chars.next() {
                            None => String::new(),
                            Some(first) => {
                                first.to_uppercase().collect::<String>() + chars.as_str()
                            }
                        }
                    })
                    .collect::<String>()
            })
            // Special case various enums
            .map(|name| {
                match enum_name.unwrap_or("") {
                    "Z3_lbool" => name.strip_prefix("L"),
                    "Z3_symbol_kind" => name.strip_suffix("Symbol"),
                    "Z3_parameter_kind" => name.strip_prefix("Parameter"),
                    "Z3_sort_kind" => name.strip_suffix("Sort"),
                    "Z3_ast_kind" => name.strip_suffix("Ast"),
                    "Z3_decl_kind" => name.strip_prefix("Op"),
                    "Z3_param_kind" => name.strip_prefix("Pk"),
                    "Z3_ast_print_mode" => name.strip_prefix("Print"),
                    "Z3_goal_prec" => name.strip_prefix("Goal"),
                    _ => Some(name.as_str()),
                }
                .map(String::from)
                .unwrap_or(name)
            })
    }
}

/// Returns true if the crate is being built in "dynamic" mode, where Z3 is
/// loaded at runtime as a shared library rather than compiled from source and
/// statically linked.
///
/// `static-link` always takes precedence when both features are enabled (for
/// example under `cargo build --all-features`) so that the default, fully
/// self-contained build is never accidentally disabled.
fn dynamic_link() -> bool {
    feature_enabled("DYNAMIC_LINK") && !feature_enabled("STATIC_LINK")
}

fn feature_enabled(name: &str) -> bool {
    env::var_os(format!("CARGO_FEATURE_{name}")).is_some()
}

/// Common bindgen configuration shared by the static and dynamic builds so that
/// the generated types and names are identical in both modes.
fn bindgen_builder(include_dir: &str) -> bindgen::Builder {
    bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg(format!("-I{include_dir}"))
        .generate_comments(true)
        .allowlist_item("Z3_.*")
        .rustified_enum(".*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .parse_callbacks(Box::new(RenameTypes))
}

fn build_z3_from_source() -> (String, String) {
    let mut config = cmake::Config::new("z3");

    // Get the build profile (debug or release)
    let profile = env::var("PROFILE").unwrap_or_else(|_| "debug".to_string());

    // Configure CMake build options for static linking and optimization
    config
        .define("BUILD_SHARED_LIBS", "OFF")
        .define("Z3_BUILD_LIBZ3_SHARED", "OFF")
        .define("Z3_BUILD_EXECUTABLE", "OFF")
        .define("Z3_BUILD_TEST_EXECUTABLES", "OFF")
        .define("Z3_BUILD_PYTHON_BINDINGS", "OFF")
        .define("Z3_BUILD_DOTNET_BINDINGS", "OFF")
        .define("Z3_BUILD_JAVA_BINDINGS", "OFF")
        .define("Z3_BUILD_DOCUMENTATION", "OFF");

    if profile == "debug" && (cfg!(target_os = "macos") || cfg!(target_os = "linux")) {
        // Optimize for speed in debug builds
        config
            .define("CMAKE_BUILD_TYPE", "Debug")
            .define("CMAKE_CXX_FLAGS_DEBUG", "-O3 -DNDEBUG -g0");
    } else {
        config.define("CMAKE_BUILD_TYPE", "Release");
    }

    if cfg!(target_os = "windows") {
        config.cxxflag("-DWIN32");
        config.cxxflag("-D_WINDOWS");
        config.define("CMAKE_MSVC_RUNTIME_LIBRARY", "MultiThreadedDLL");
    }

    // Build Z3 and get output directory
    let dst = config.build();
    let lib_dir = dst.join("lib");
    let include_dir = dst.join("include");

    (
        lib_dir.display().to_string(),
        include_dir.display().to_string(),
    )
}

/// Build Z3 from the bundled source tree and statically link it. This is the
/// default behaviour and produces a fully self-contained artifact.
fn build_static() {
    let (lib_dir, include_dir) = build_z3_from_source();

    // Configure static linking
    println!("cargo:rustc-link-search=native={lib_dir}");
    if cfg!(target_os = "windows") && env::var("CC").is_ok_and(|cc| cc.contains("msvc")) {
        println!("cargo:rustc-link-lib=static=libz3");
    } else {
        println!("cargo:rustc-link-lib=static=z3");
    }

    // Add system dependencies for static linking
    #[cfg(target_os = "linux")]
    {
        println!("cargo:rustc-link-lib=dylib=stdc++");
        println!("cargo:rustc-link-lib=dylib=m");
        println!("cargo:rustc-link-lib=dylib=pthread");
    }

    #[cfg(target_os = "macos")]
    {
        println!("cargo:rustc-link-lib=dylib=c++");
        println!("cargo:rustc-link-lib=dylib=m");
        // Add framework path for macOS system libraries
        println!("cargo:rustc-link-search=framework=/System/Library/Frameworks");
    }

    // Track dependencies for rebuilds
    println!("cargo:rerun-if-changed=z3/CMakeLists.txt");
    println!("cargo:rerun-if-changed=z3/src");
    println!("cargo:rerun-if-env-changed=PROFILE");

    // Generate bindings using bindgen
    let bindings = bindgen_builder(&include_dir)
        .generate()
        .expect("Unable to generate bindings");

    write_bindings(bindings.to_string());
}

/// Generate bindings that load Z3 at runtime from a shared library, without
/// linking against it at build time. The headers are only needed to generate
/// the bindings; no Z3 code is compiled or linked.
fn build_dynamic() {
    println!("cargo:rerun-if-env-changed=CLARIRS_Z3_INCLUDE_DIR");
    println!("cargo:rerun-if-env-changed=PYO3_PYTHON");

    let include_dir = detect_include_dir().unwrap_or_else(|| {
        panic!(
            "clarirs-z3-sys: building with the `dynamic-link` feature requires the Z3 \
             headers to generate bindings, but they could not be located.\n\
             Install the `z3-solver` Python package (which ships the headers), or set \
             CLARIRS_Z3_INCLUDE_DIR to a directory containing `z3.h`."
        )
    });

    let bindings = bindgen_builder(&include_dir)
        // Generate a `Z3Lib` struct whose fields are function pointers resolved
        // at runtime via `libloading`, plus methods that call through them.
        .dynamic_library_name("Z3Lib")
        // Do not require every symbol to be present at load time: this keeps the
        // loader tolerant of Z3 builds that omit rarely-used symbols.
        .dynamic_link_require_all(false)
        .generate()
        .expect("Unable to generate Z3 dynamic bindings");

    let generated = bindings.to_string();
    let shims = generate_dynamic_shims(&generated);

    let mut output = String::with_capacity(generated.len() + shims.len() + LOADER_SUPPORT.len());
    output.push_str(&generated);
    output.push('\n');
    output.push_str(LOADER_SUPPORT);
    output.push('\n');
    output.push_str(&shims);
    output.push('\n');

    write_bindings(output);
}

fn write_bindings(contents: String) {
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    std::fs::write(out_path.join("bindings.rs"), contents).expect("Couldn't write bindings!");
}

/// Locate a directory containing the Z3 headers for dynamic builds.
///
/// Resolution order:
/// 1. The `CLARIRS_Z3_INCLUDE_DIR` environment variable.
/// 2. The `include` directory of an installed `z3-solver` Python wheel,
///    discovered by querying a Python interpreter.
fn detect_include_dir() -> Option<String> {
    if let Some(dir) = env::var_os("CLARIRS_Z3_INCLUDE_DIR") {
        let dir = dir.to_string_lossy().into_owned();
        if PathBuf::from(&dir).join("z3.h").exists() {
            return Some(dir);
        }
        panic!("CLARIRS_Z3_INCLUDE_DIR is set to {dir:?} but it does not contain z3.h");
    }

    let interpreters = [
        env::var("PYO3_PYTHON").ok(),
        Some("python3".to_string()),
        Some("python".to_string()),
    ];

    for interpreter in interpreters.into_iter().flatten() {
        let output = Command::new(&interpreter)
            .args([
                "-c",
                "import os, z3; print(os.path.join(os.path.dirname(z3.__file__), 'include'))",
            ])
            .output();

        if let Ok(output) = output {
            if output.status.success() {
                let dir = String::from_utf8_lossy(&output.stdout).trim().to_string();
                if !dir.is_empty() && PathBuf::from(&dir).join("z3.h").exists() {
                    return Some(dir);
                }
            }
        }
    }

    None
}

/// Parse the bindgen-generated dynamic bindings and emit free-function shims
/// that forward to a process-global, lazily-loaded `Z3Lib` instance. This keeps
/// every call site (`z3::mk_config(...)`) identical between the static and
/// dynamic builds.
fn generate_dynamic_shims(generated: &str) -> String {
    use quote::quote;

    let file = syn::parse_file(generated).expect("Unable to parse generated Z3 bindings");

    let mut shims = Vec::new();

    for item in &file.items {
        let syn::Item::Impl(item_impl) = item else {
            continue;
        };

        let is_z3lib = matches!(
            &*item_impl.self_ty,
            syn::Type::Path(type_path)
                if type_path
                    .path
                    .segments
                    .last()
                    .is_some_and(|seg| seg.ident == "Z3Lib")
        );
        if !is_z3lib {
            continue;
        }

        for impl_item in &item_impl.items {
            let syn::ImplItem::Fn(method) = impl_item else {
                continue;
            };

            let mut inputs = method.sig.inputs.iter();

            // Only the Z3 API methods take `&self`; the loader constructors
            // (`new`, `from_library`) do not, so skipping receiver-less methods
            // cleanly excludes them.
            match inputs.next() {
                Some(syn::FnArg::Receiver(_)) => {}
                _ => continue,
            }

            let name = &method.sig.ident;
            let output = &method.sig.output;

            let mut params = Vec::new();
            let mut args = Vec::new();
            let mut usable = true;

            for input in inputs {
                let syn::FnArg::Typed(pat_type) = input else {
                    usable = false;
                    break;
                };
                let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                    usable = false;
                    break;
                };
                let ident = &pat_ident.ident;
                let ty = &pat_type.ty;
                params.push(quote!(#ident: #ty));
                args.push(quote!(#ident));
            }

            if !usable {
                continue;
            }

            shims.push(quote! {
                #[inline]
                #[allow(dead_code, clippy::missing_safety_doc, clippy::too_many_arguments)]
                pub unsafe fn #name(#(#params),*) #output {
                    unsafe { z3lib().#name(#(#args),*) }
                }
            });
        }
    }

    quote!(#(#shims)*).to_string()
}

/// Runtime support appended to the dynamic bindings: a process-global handle to
/// the loaded Z3 library, an explicit `load` entry point, and a lazy resolver
/// driven by environment variables.
const LOADER_SUPPORT: &str = r#"
use ::std::ffi::OsStr;
use ::std::sync::OnceLock;

static Z3LIB: OnceLock<Z3Lib> = OnceLock::new();

/// Explicitly load the Z3 shared library from `path`.
///
/// This should be called before any Z3 function is used. If it is not called,
/// the library is loaded lazily on first use using the `CLARIRS_Z3_LIBRARY` or
/// `CLARIRS_Z3_LIB_DIR` environment variables, falling back to the platform's
/// default library search path.
///
/// Calling this more than once is a no-op after the first successful load.
pub fn load<P: AsRef<OsStr>>(path: P) -> Result<(), ::libloading::Error> {
    if Z3LIB.get().is_some() {
        return Ok(());
    }
    let lib = unsafe { Z3Lib::new(path.as_ref())? };
    let _ = Z3LIB.set(lib);
    Ok(())
}

/// Returns `true` if the Z3 shared library has already been loaded.
pub fn is_loaded() -> bool {
    Z3LIB.get().is_some()
}

fn default_library_name() -> &'static str {
    #[cfg(target_os = "windows")]
    {
        "libz3.dll"
    }
    #[cfg(target_os = "macos")]
    {
        "libz3.dylib"
    }
    #[cfg(not(any(target_os = "windows", target_os = "macos")))]
    {
        "libz3.so"
    }
}

fn resolve_library_path() -> ::std::ffi::OsString {
    if let Some(path) = ::std::env::var_os("CLARIRS_Z3_LIBRARY") {
        return path;
    }
    if let Some(dir) = ::std::env::var_os("CLARIRS_Z3_LIB_DIR") {
        return ::std::path::Path::new(&dir)
            .join(default_library_name())
            .into_os_string();
    }
    default_library_name().into()
}

#[inline]
fn z3lib() -> &'static Z3Lib {
    Z3LIB.get_or_init(|| {
        let path = resolve_library_path();
        unsafe { Z3Lib::new(&path) }.unwrap_or_else(|err| {
            panic!(
                "clarirs: failed to load the Z3 shared library ({:?}): {}.\n\
                 Install the `z3-solver` package, or set CLARIRS_Z3_LIBRARY to the \
                 path of the Z3 shared library (or CLARIRS_Z3_LIB_DIR to its directory).",
                path, err
            )
        })
    })
}
"#;

fn main() {
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DYNAMIC_LINK");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_STATIC_LINK");

    if dynamic_link() {
        build_dynamic();
    } else {
        build_static();
    }
}
