use std::path::PathBuf;

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

    // println!("cargo:warning={:?}", vampire_path);
}
