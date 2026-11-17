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
fn proofs_only_keeps_specs_and_roundtrips_implementation_annotations() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let source = "\
_include_pulse(Vocabulary)\n\
_type(Permission, Pulse.perm)\n\
_include_pulse(Helpers, let proof () : Lemma True = ())\n\
int f(_plain int *p) _requires(*p >= 0) _ensures(return >= 0) {\n\
    _ghost_stmt(start ());\n\
    while (*p > 0) _invariant(*p >= 0) { (*p)--; }\n\
    end: _ensures(_live(p))\n\
    return *p;\n\
}\n";
    fs::write(root.join("a.c"), source).unwrap();
    success(run(root, &["--extract", "--proofs-only", "a.c"]));
    let stripped = fs::read_to_string(root.join("a.c")).unwrap();
    assert!(stripped.contains("_include_pulse(Vocabulary)"));
    assert!(stripped.contains("_type(Permission, Pulse.perm)"));
    assert!(stripped.contains("_include_pulse(Helpers, let proof () : Lemma True = ())"));
    assert!(stripped.contains("f(_plain int *p) _requires(*p >= 0) _ensures(return >= 0)"));
    for proof in ["_ghost_stmt", "_invariant", "_ensures(_live"] {
        assert!(!stripped.contains(proof), "{stripped}");
    }
    success(run(root, &["--apply", "out.annotations", "--check"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), stripped);
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
}

#[test]
fn proofs_only_resolves_supplied_angle_headers_without_erasing_sal() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    fs::create_dir(root.join("include")).unwrap();
    let header = "\
#define STEP(x) _ghost_stmt(proof $(x))\n\
#define SPEC(x) _inline_pulse(owned $(x))\n\
#define JOIN(x) _ensures(_live(x))\n\
#define BRANCH _ghost_stmt(branch ())\n\
#define G _ghost_stmt(short ())\n\
#undef _Out_\n\
#define _Out_ _out\n";
    let source = "#include <proof.h>\nvoid f(_Out_ int *p) _requires(SPEC(p)) { STEP(p); end: JOIN(p) if (p) { BRANCH; } *p = 1; G; }\n";
    fs::write(root.join("include/proof.h"), header).unwrap();
    fs::write(root.join("a.c"), source).unwrap();
    success(run(
        root,
        &[
            "--extract",
            "--proofs-only",
            "-I",
            "include",
            "a.c",
            "include/proof.h",
        ],
    ));
    let stripped = fs::read_to_string(root.join("a.c")).unwrap();
    assert!(stripped.contains("_Out_ int *p"));
    assert!(stripped.contains("_requires(SPEC(p))"));
    assert!(!stripped.contains("STEP(p)"));
    assert!(!stripped.contains("JOIN(p)"));
    assert!(!stripped.contains("BRANCH;"));
    assert!(!stripped.contains("G;"));
    assert!(
        fs::read_to_string(root.join("include/proof.h"))
            .unwrap()
            .contains("#define _Out_ _out")
    );
    success(run(root, &["--apply", "out.annotations", "--check"]));
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
    assert_eq!(
        fs::read_to_string(root.join("include/proof.h")).unwrap(),
        header
    );
}

#[test]
fn proofs_only_retains_redefined_wrappers_and_their_aliases() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    let source = "\
#undef RUNTIME_ASSERT\n\
#define RUNTIME_ASSERT(x) _assert(x)\n\
#define OTHER_ASSERT(x) RUNTIME_ASSERT(x)\n\
void f(int x) { OTHER_ASSERT(x); RUNTIME_ASSERT(x); _ghost_stmt(proof ()); }\n";
    fs::write(root.join("a.c"), source).unwrap();
    success(run(root, &["--extract", "--proofs-only", "a.c"]));
    let stripped = fs::read_to_string(root.join("a.c")).unwrap();
    assert!(stripped.contains("OTHER_ASSERT(x); RUNTIME_ASSERT(x);"));
    success(run(root, &["--apply", "out.annotations"]));
    assert_eq!(fs::read_to_string(root.join("a.c")).unwrap(), source);
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
fn proof_only_validation_preflights_every_file_for_check_and_apply() {
    let directory = TempDir::new().unwrap();
    let root = directory.path();
    fs::write(root.join("a.c"), "void a(void) { _ghost_stmt(a ()); }\n").unwrap();
    fs::write(root.join("b.c"), "void b(void) { _ghost_stmt(b ()); }\n").unwrap();
    success(run(root, &["--extract", "a.c", "b.c"]));
    let originals: Vec<_> = ["a.c", "b.c"]
        .map(|name| fs::read(root.join(name)).unwrap())
        .into();
    let original: toml::Value =
        toml::from_str(&fs::read_to_string(root.join("out.annotations")).unwrap()).unwrap();
    for payload in [
        "_ghost_stmt(b ()); injected();",
        "_ghost_stmt(b ());\n#define INJECTED 1\n",
    ] {
        let mut overlay = original.clone();
        overlay["files"][1]["annotations"][0]["text"] = payload.into();
        fs::write(
            root.join("bad.annotations"),
            toml::to_string(&overlay).unwrap(),
        )
        .unwrap();
        for args in [
            vec!["--apply", "bad.annotations", "--check"],
            vec!["--apply", "bad.annotations"],
        ] {
            let result = run(root, &args);
            assert!(!result.status.success());
            assert!(String::from_utf8_lossy(&result.stderr).contains("b.c:"));
            assert!(String::from_utf8_lossy(&result.stderr).contains("source preservation"));
            for (name, original) in ["a.c", "b.c"].iter().zip(&originals) {
                assert_eq!(fs::read(root.join(name)).unwrap(), *original);
            }
        }
    }
}

#[test]
fn overlay_cannot_classify_runtime_or_unrelated_names_as_proof_wrappers() {
    for prefix in ["void STEP(int);\n", "#define STEP(x) runtime(x)\n", ""] {
        let directory = TempDir::new().unwrap();
        let root = directory.path();
        fs::write(
            root.join("a.c"),
            "#define STEP(x) _ghost_stmt(proof $(x))\nvoid a(int x) { STEP(x); }\n",
        )
        .unwrap();
        fs::write(
            root.join("b.c"),
            format!("{prefix}void b(int x) {{ _ghost_stmt(proof $(x)); }}\n"),
        )
        .unwrap();
        success(run(root, &["--extract", "a.c", "b.c"]));
        let original_a = fs::read(root.join("a.c")).unwrap();
        let original_b = fs::read(root.join("b.c")).unwrap();
        let mut overlay: toml::Value =
            toml::from_str(&fs::read_to_string(root.join("out.annotations")).unwrap()).unwrap();
        // STEP is genuinely proof-only in a.c, but b.c neither includes it nor
        // defines the same proof-only wrapper. The metadata must not grant it.
        let advertised = overlay["files"][0]["macros"].clone();
        overlay["files"][1]
            .as_table_mut()
            .unwrap()
            .insert("macros".into(), advertised);
        overlay["files"][1]["annotations"][0]["text"] = "STEP(x);".into();
        fs::write(
            root.join("bad.annotations"),
            toml::to_string(&overlay).unwrap(),
        )
        .unwrap();
        for args in [
            vec!["--apply", "bad.annotations", "--check"],
            vec!["--apply", "bad.annotations"],
        ] {
            let result = run(root, &args);
            assert!(!result.status.success());
            let error = String::from_utf8_lossy(&result.stderr);
            assert!(
                error.contains("source preservation")
                    || error.contains("source contains annotations"),
                "{error}"
            );
            assert_eq!(fs::read(root.join("a.c")).unwrap(), original_a);
            assert_eq!(fs::read(root.join("b.c")).unwrap(), original_b);
        }
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
