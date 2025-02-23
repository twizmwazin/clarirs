use std::env;
use std::path::PathBuf;

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
                    ItemKind::Var => s
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

    if profile == "debug" && cfg!(target_os = "macos") || cfg!(target_os = "linux") {
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

fn main() {
    let (lib_dir, include_dir) = build_z3_from_source();

    // Configure static linking
    println!("cargo:rustc-link-search=native={}", lib_dir);
    if cfg!(target_os = "windows") {
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
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=z3/CMakeLists.txt");
    println!("cargo:rerun-if-changed=z3/src");
    println!("cargo:rerun-if-env-changed=PROFILE");

    // Generate bindings using bindgen
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg(format!("-I{}", include_dir))
        .generate_comments(true)
        .allowlist_item("Z3_.*")
        .rustified_enum(".*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .parse_callbacks(Box::new(RenameTypes))
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let bindings_path = out_path.join("bindings.rs");
    bindings
        .write_to_file(&bindings_path)
        .expect("Couldn't write bindings!");
}
