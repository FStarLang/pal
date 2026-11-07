use std::process::Command;
use zngur::Zngur;

fn compiler_output(compiler: &cc::Tool, argument: &str) -> String {
    let output = compiler
        .to_command()
        .arg(argument)
        .output()
        .expect("Cannot query the C++ compiler");
    assert!(
        output.status.success(),
        "C++ compiler {argument} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = String::from_utf8(output.stdout)
        .expect("C++ compiler output is not UTF-8")
        .trim()
        .to_owned();
    assert!(
        !result.is_empty(),
        "C++ compiler {argument} returned no output"
    );
    result
}

fn llvm_config_flags(args: &[&str]) -> Vec<String> {
    (Command::new("llvm-config-20").args(args.iter()).output())
        .or(Command::new("llvm-config").args(args.iter()).output())
        .expect("Cannot find llvm-config")
        .stdout
        .split(|c| c.is_ascii_whitespace())
        .filter(|flag| flag.len() > 0)
        .map(|flag| str::from_utf8(flag).unwrap().into())
        .collect()
}

fn split_off<'a>(prefix: &str, s: &'a str) -> Option<&'a str> {
    if s.starts_with(prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}

fn take_until(s: &str, c: char) -> &str {
    s.find(c).map(|i| &s[..i]).unwrap_or(s)
}

fn main() {
    build_rs::output::rerun_if_changed("cpp/iface.zng");
    build_rs::output::rerun_if_changed("cpp/impl.cpp");

    let crate_dir = build_rs::input::cargo_manifest_dir();
    let out_dir = build_rs::input::out_dir();

    Zngur::from_zng_file(crate_dir.join("cpp/iface.zng"))
        .with_cpp_file(out_dir.join("generated.cpp"))
        .with_h_file(crate_dir.join("cpp/generated.h"))
        .with_rs_file(out_dir.join("generated.rs"))
        .with_zng_header_in_place()
        .generate();

    let mut build = cc::Build::new();

    let llvm_version = llvm_config_flags(&["--version"])
        .first()
        .and_then(|v| str::parse::<u32>(take_until(v, '.')).ok())
        .expect("Cannot parse `llvm-config --version` output");
    if llvm_version < 20 {
        panic!(
            "\nPAL requires clang >= 20, but found version {:}\n",
            llvm_version
        )
    }

    // zngur warnings...
    build
        .flag("-Wno-undefined-inline")
        .flag("-Wno-uninitialized-const-reference")
        .flag("-Wno-unused-parameter");

    build
        .cpp(true)
        .compiler("clang++")
        .include(crate_dir.join("cpp"));

    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("windows") {
        build_rs::output::rerun_if_env_changed("PATH");
        let compiler = build.get_compiler();
        let version = compiler_output(&compiler, "-dumpversion");
        assert_eq!(
            version
                .split('.')
                .next()
                .and_then(|v| v.parse::<u32>().ok()),
            Some(llvm_version),
            "The C++ compiler and llvm-config must use the same LLVM major version"
        );
        let resource_dir = compiler_output(&compiler, "-print-resource-dir").replace('\\', "/");
        assert!(
            std::path::Path::new(&resource_dir)
                .join("include/stdbool.h")
                .is_file(),
            "Missing Clang builtin headers in {resource_dir}"
        );
        build.define(
            "PAL_CLANG_RESOURCE_DIR",
            Some(format!("{resource_dir:?}").as_str()),
        );
    }

    build
        .clone()
        .file(out_dir.join("generated.cpp"))
        .flag("-Wno-unused-function")
        .compile("zngur_generated");

    for flag in llvm_config_flags(&["--cxxflags"]) {
        build.flag(flag);
    }
    build.file("cpp/impl.cpp").compile("impls");

    for flag in llvm_config_flags(&["--ldflags", "--libs"]) {
        if let Some(lib) = split_off("-l", &flag) {
            build_rs::output::rustc_link_lib(lib);
        } else if let Some(lib_path) = split_off("-L", &flag) {
            build_rs::output::rustc_link_search(lib_path);
        }
    }
    build_rs::output::rustc_link_lib("clang-cpp");
}
