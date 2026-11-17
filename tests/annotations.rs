use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};
use tempfile::TempDir;

fn run(root: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_pal_annotations"))
        .current_dir(root)
        .args(args)
        .output()
        .unwrap()
}

fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn cli_preflights_check_is_readonly_and_apply_is_idempotent() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let a = "int a(int x) _requires(x >= 0) { return x; }\n";
    let b = "int b(int y) _requires(y >= 0) { return y; }\n";
    fs::write(root.join("a.c"), a).unwrap();
    fs::write(root.join("b.h"), b).unwrap();
    success(run(root, &["--extract", "a.c", "b.h"]));
    let stripped_a = fs::read(root.join("a.c")).unwrap();
    let stripped_b = fs::read(root.join("b.h")).unwrap();
    let overlay = fs::read(root.join("out.annotations")).unwrap();
    assert!(
        success(run(root, &["--apply", "out.annotations", "--check"]))
            .contains("2 files would change")
    );
    assert_eq!(fs::read(root.join("a.c")).unwrap(), stripped_a);
    assert_eq!(fs::read(root.join("b.h")).unwrap(), stripped_b);
    assert!(!run(root, &["--extract", "a.c"]).status.success());
    assert_eq!(fs::read(root.join("out.annotations")).unwrap(), overlay);

    fs::write(root.join("b.h"), "int b(int z) { return z; }\n").unwrap();
    assert!(!run(root, &["--apply", "out.annotations"]).status.success());
    assert_eq!(fs::read(root.join("a.c")).unwrap(), stripped_a);
    fs::write(root.join("b.h"), stripped_b).unwrap();
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), a);
    assert_eq!(fs::read_to_string(root.join("b.h")).unwrap(), b);
    assert!(success(run(root, &["--apply", "out.annotations"])).contains("0 files changed"));
}

#[test]
fn invalid_overlays_and_missing_inputs_never_modify_sources() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let source = "int f(void) _ensures(return == 0) { return 0; }\n";
    fs::write(root.join("a.c"), source).unwrap();
    assert!(
        !run(root, &["--extract", "a.c", "missing.h"])
            .status
            .success()
    );
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
    assert!(!root.join("out.annotations").exists());
    success(run(root, &["--extract", "a.c"]));
    let original = fs::read_to_string(root.join("out.annotations")).unwrap();
    let stripped = fs::read(root.join("a.c")).unwrap();
    for invalid in [
        original.replace("format_version = 1", "format_version = 999"),
        original.replace("path = \"a.c\"", "path = \"../a.c\""),
        original.replace("offset = ", "offset = -"),
    ] {
        fs::write(root.join("invalid.annotations"), invalid).unwrap();
        assert!(
            !run(root, &["--apply", "invalid.annotations"])
                .status
                .success()
        );
        assert_eq!(fs::read(root.join("a.c")).unwrap(), stripped);
    }
}

#[test]
fn source_root_is_independent_of_overlay_location() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    fs::create_dir(root.join("sources")).unwrap();
    let source = "int f(int x) _ensures(return == x) { return x; }\n";
    fs::write(root.join("sources/a.c"), source).unwrap();
    success(run(root, &["--extract", "--root", "sources", "a.c"]));
    success(run(
        root,
        &["--apply", "out.annotations", "--root", "sources"],
    ));
    assert_eq!(
        fs::read_to_string(root.join("sources/a.c")).unwrap(),
        source
    );
}

#[test]
fn wrapper_discovery_follows_supplied_headers_without_leaking_between_sources() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    fs::write(
        root.join("proofs.h"),
        "#define STEP(x) _ghost_stmt(proof $(x))\n",
    )
    .unwrap();
    let a = "#include \"proofs.h\"\nvoid a(int x) { STEP(x); }\n";
    let b = "void STEP(int);\nvoid b(int x) { STEP(x); }\n";
    fs::write(root.join("a.c"), a).unwrap();
    fs::write(root.join("b.c"), b).unwrap();
    success(run(root, &["--extract", "a.c", "b.c", "proofs.h"]));
    assert!(
        !fs::read_to_string(root.join("a.c"))
            .unwrap()
            .contains("STEP(x);")
    );
    assert_eq!(fs::read_to_string(root.join("b.c")).unwrap(), b);
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), a);
    assert_eq!(fs::read_to_string(root.join("b.c")).unwrap(), b);
}

#[test]
fn stripped_control_flow_and_comma_expressions_compile() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let source = "\
#define _step(x) _ghost_stmt(assert pure ($(x) >= 0))\n\
_include_pulse(Helpers, let proof = ())\n\
void f(_plain int *p) _requires(*p >= 0) {\n\
    if (*p) _assert(*p); else _step(*p);\n\
    for (_step(*p), *p = 0; *p < 3; _assert(*p >= 0), (*p)++)\n\
        _invariant(*p <= 3) {}\n\
    do _ghost_stmt(proof ()); while (*p);\n\
}\n";
    fs::write(root.join("a.c"), source).unwrap();
    success(run(root, &["--extract", "a.c"]));
    let output = Command::new("clang")
        .current_dir(root)
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-fsyntax-only",
            "a.c",
        ])
        .output()
        .unwrap();
    success(output);
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
}

#[cfg(unix)]
#[test]
fn aliases_keep_symlinks_and_file_modes_and_reject_external_targets() {
    use std::os::unix::fs::{PermissionsExt, symlink};
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    fs::create_dir(root.join("sources")).unwrap();
    let source = "void f(_plain int *p) {}\n";
    let target = root.join("sources/a.c");
    fs::write(&target, source).unwrap();
    fs::set_permissions(&target, fs::Permissions::from_mode(0o640)).unwrap();
    symlink("sources/a.c", root.join("alias.c")).unwrap();
    assert!(
        success(run(root, &["--extract", "alias.c", "sources/a.c"])).contains("1 distinct files")
    );
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(&target).unwrap(), source);
    assert_eq!(
        fs::metadata(&target).unwrap().permissions().mode() & 0o777,
        0o640
    );
    assert_eq!(
        fs::read_link(root.join("alias.c")).unwrap(),
        Path::new("sources/a.c")
    );
    let outside = TempDir::new().unwrap();
    fs::write(outside.path().join("b.h"), source).unwrap();
    symlink(outside.path().join("b.h"), root.join("external.h")).unwrap();
    assert!(
        !run(
            root,
            &["--extract", "external.h", "-o", "external.annotations"]
        )
        .status
        .success()
    );
    assert_eq!(
        fs::read_to_string(outside.path().join("b.h")).unwrap(),
        source
    );
}

#[test]
fn every_tracked_c_and_header_roundtrips_via_cli() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let listing = Command::new("git")
        .current_dir(repository)
        .args(["ls-files", "-z", "--", "*.c", "*.h"])
        .output()
        .unwrap();
    assert!(listing.status.success());
    let paths: Vec<PathBuf> = listing
        .stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| PathBuf::from(std::str::from_utf8(path).unwrap()))
        .collect();
    assert!(!paths.is_empty());
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let mut originals = BTreeMap::new();
    let mut links: BTreeMap<PathBuf, PathBuf> = BTreeMap::new();
    for relative in &paths {
        let source = repository.join(relative);
        let target = root.join(relative);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        if source.symlink_metadata().unwrap().is_symlink() {
            #[cfg(unix)]
            {
                let link = fs::read_link(&source).unwrap();
                std::os::unix::fs::symlink(&link, &target).unwrap();
                links.insert(relative.clone(), link);
            }
            #[cfg(not(unix))]
            fs::copy(&source, &target).unwrap();
        } else {
            fs::copy(&source, &target).unwrap();
        }
        originals.insert(relative.clone(), fs::read(&source).unwrap());
    }
    let output = Command::new(env!("CARGO_BIN_EXE_pal_annotations"))
        .current_dir(root)
        .arg("--extract")
        .args(&paths)
        .output()
        .unwrap();
    let report = success(output);
    println!("{report}");
    let overlay: toml::Value = fs::read_to_string(root.join("out.annotations"))
        .unwrap()
        .parse()
        .unwrap();
    let files = overlay["files"].as_array().unwrap();
    let count: usize = files
        .iter()
        .map(|file| file["annotations"].as_array().unwrap().len())
        .sum();
    assert!(count > 5_000, "only extracted {count} annotations");

    // A second extraction must find no remaining annotation invocations.
    let output = Command::new(env!("CARGO_BIN_EXE_pal_annotations"))
        .current_dir(root)
        .args(["--extract", "-o", "empty.annotations"])
        .args(&paths)
        .output()
        .unwrap();
    assert!(success(output).contains("Extracted 0 annotations"));
    success(run(root, &["--apply", "out.annotations", "--check"]));
    success(run(root, &["--apply", "out.annotations"]));
    for (relative, original) in originals {
        assert_eq!(
            fs::read(root.join(&relative)).unwrap(),
            original,
            "{}",
            relative.display()
        );
    }
    for (relative, link) in links {
        assert_eq!(fs::read_link(root.join(relative)).unwrap(), link);
    }
    assert!(success(run(root, &["--apply", "out.annotations"])).contains("0 files changed"));
}
