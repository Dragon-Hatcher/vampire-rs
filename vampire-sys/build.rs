use std::{env, path::PathBuf};

fn main() {
    let vampire_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("vampire-lib");

    let dst = cmake::Config::new(vampire_path)
        .define("CMAKE_BUILD_TYPE", "Release")
        .build_target("vampire_lib")
        .build();

    println!("cargo:rustc-link-search=native={}/build", dst.display());
    println!("cargo:rustc-link-lib=static=vampire_lib");

    // Link C++ standard library
    let target = env::var("TARGET").unwrap();
    if target.contains("apple") {
        println!("cargo:rustc-link-lib=c++");
    } else if target.contains("linux") {
        println!("cargo:rustc-link-lib=stdc++");
    }
}
