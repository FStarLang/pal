use super::*;

fn apply_source(file: &FileOverlay, source: &str, macros: &[Macro]) -> Result<String> {
    let updated = render_source(file, source, macros)?;
    preservation::validate_application(file, source, &updated, macros)?;
    Ok(updated)
}

fn extract(source: &str) -> (FileOverlay, String, Vec<Macro>) {
    let macros = discover_macros(&[source]).unwrap();
    let (overlay, stripped) = extract_source("sample.c".into(), source, &macros).unwrap();
    assert_eq!(apply_source(&overlay, &stripped, &macros).unwrap(), source);
    assert_eq!(apply_source(&overlay, source, &macros).unwrap(), source);
    (overlay, stripped, macros)
}

#[test]
fn application_rejects_runtime_text_and_forged_replacements() {
    let source = "void f(void) {\n    _ghost_stmt(proof ());\n}\n";
    for payload in [
        "_ghost_stmt(proof ()); work();",
        "_ghost_stmt(proof ());\n#define CHANGED 1\n",
        "_ghost_stmt(proof ()); // hide following code",
        "work();",
    ] {
        let (mut file, stripped, macros) = extract(source);
        file.annotations[0].text = payload.into();
        for current in [stripped.clone(), format!("int unrelated;\n{stripped}")] {
            assert!(
                apply_source(&file, &current, &macros)
                    .unwrap_err()
                    .contains("source preservation")
            );
        }
    }
    let (mut file, stripped, macros) = extract(source);
    file.annotations[0].replacement = "void".into();
    file.annotations[0].site.replacement_tokens = vec!["void".into()];
    assert!(
        apply_source(&file, &stripped, &macros)
            .unwrap_err()
            .contains("scaffolding")
    );
    file.annotations[0].replacement.clear();
    assert!(
        apply_source(&file, &stripped, &macros)
            .unwrap_err()
            .contains("scaffolding")
    );
}

#[test]
fn application_checks_payload_recognition_at_the_actual_site() {
    let source = "void f(void) _requires(1) { /* comment */ }\n";
    let (mut file, stripped, macros) = extract(source);
    file.annotations[0].offset = stripped.find("comment").unwrap();
    assert!(
        apply_source(&file, &stripped, &macros)
            .unwrap_err()
            .contains("source context")
    );
}

#[test]
fn application_preserves_macro_form_and_directive_boundaries() {
    let source = "#define F(x) _plain x\n";
    let (mut file, stripped, macros) = extract(source);
    file.annotations[0].offset = stripped.find("F(").unwrap() + 1;
    file.annotations[0].text = " _plain ".into();
    assert!(
        apply_source(&file, &stripped, &macros)
            .unwrap_err()
            .contains("function-like")
    );

    let (mut file, stripped, macros) = extract(source);
    file.annotations[0].text = "_plain\n".into();
    assert!(
        apply_source(&file, &stripped, &macros)
            .unwrap_err()
            .contains("runtime/preprocessor token")
    );
}

#[test]
fn application_does_not_consume_user_comments_in_placeholders() {
    let source = "void f(int x) { if (x) _assert(x); }\n";
    let (file, stripped, macros) = extract(source);
    let edited = stripped.replace("((void)0)", "((/* keep me */void)0)");
    assert!(
        apply_source(&file, &edited, &macros)
            .unwrap_err()
            .contains("remove non-annotation text")
    );
}

#[test]
fn application_preserves_the_current_source_with_edited_proofs() {
    let source = "int f(int x) _requires(x > 0) { return x; }\n";
    let (mut file, stripped, macros) = extract(source);
    file.annotations[0].text = "_requires(x >= 0)".into();
    let edited = format!("int added(void) {{ return 42; }}\n{stripped}");
    let applied = apply_source(&file, &edited, &macros).unwrap();
    assert_eq!(
        applied,
        format!(
            "int added(void) {{ return 42; }}\n{}",
            source.replace("x > 0", "x >= 0")
        )
    );
    assert_eq!(apply_source(&file, &applied, &macros).unwrap(), applied);
}

#[test]
fn expressions_comments_literals_and_inactive_branches_roundtrip() {
    let source = r#"#include "pal.h"
// _requires(not_an_annotation)
const char *s = "_ghost_stmt(not_an_annotation)";
#if DISABLED
void inactive(void) _ensures(1) { _ghost_stmt(assert pure (True)); }
#endif
void f(_plain int *p) _requires(*p >= 0) {
    if (*p) _assert(*p == '('); else _ghost_stmt(assert pure ('i == 'i));
    for (_ghost_stmt(step), *p = 0; *p < 3; _assert(*p >= 0), (*p)++)
        _invariant(*p <= 3) {}
    _assert(')' != ' ' && '\\' != '\'' && '(' == '(');
}
"#;
    let (_, stripped, _) = extract(source);
    assert!(stripped.contains("if (*p) ((void)0); else ((void)0);"));
    assert!(stripped.contains("for (((void)0), *p = 0;"));
    assert!(stripped.contains("// _requires(not_an_annotation)"));
    assert!(stripped.contains("\"_ghost_stmt(not_an_annotation)\""));
    assert!(!stripped.contains("_ensures(1)"));
}

#[test]
fn wrappers_and_mixed_macro_bodies_roundtrip() {
    let source = "\
#define _owned _refine(this != 0)\n\
#define _owned2 _owned\n\
#define _step(x) _ghost_stmt(use $(x))\n\
#define RUN(x) do { _assert(x); work(x); } while (0)\n\
_owned2 int *global;\n\
void f(void) { _step(global); RUN(global); }\n";
    let (overlay, stripped, macros) = extract(source);
    assert_eq!(macros.len(), 3);
    assert!(stripped.contains("#define _owned \n"));
    assert!(stripped.contains("#define _step(x) ((void)0)"));
    assert!(stripped.contains("do { ((void)0); work(x); } while (0)"));
    assert!(stripped.contains(" int *global;"));
    assert!(overlay.annotations.iter().any(|a| a.text == "_owned2"));
    assert!(!stripped.contains("_step(global)"));
}

#[test]
fn runtime_macro_variants_are_not_erased_as_annotation_aliases() {
    let source = "\
#ifdef VERIFY\n\
#define STEP(x) _ghost_stmt(use $(x))\n\
#else\n\
#define STEP(x) runtime(x)\n\
#endif\n\
void f(int x) { STEP(x); }\n";
    let (_, stripped, macros) = extract(source);
    assert!(macros.is_empty());
    assert!(stripped.contains("#define STEP(x) ((void)0)"));
    assert!(stripped.contains("#define STEP(x) runtime(x)"));
    assert!(stripped.contains("STEP(x);"));
}

#[test]
fn undefined_or_runtime_symbol_wrappers_are_rejected() {
    let undefined =
        "#define STEP(x) _ghost_stmt(proof $(x))\n#undef STEP\nvoid f(void) { STEP(1); }\n";
    assert!(
        discover_macros(&[undefined])
            .unwrap_err()
            .contains("undefined")
    );
    let conditional = "\
#ifdef VERIFY\n\
#define STEP(x) _ghost_stmt(proof $(x))\n\
#else\n\
void STEP(int);\n\
#endif\n\
void f(void) { STEP(1); }\n";
    assert!(
        discover_macros(&[conditional])
            .unwrap_err()
            .contains("also a C declaration")
    );
    let local = "\
#ifdef VERIFY\n\
#define OWNED _plain\n\
#endif\n\
void f(void) {\n\
#ifndef VERIFY\n\
int x = 0, OWNED = 1;\n\
#endif\n\
}\n";
    assert!(
        discover_macros(&[local])
            .unwrap_err()
            .contains("also a C declaration")
    );
}

#[test]
fn pal_definitions_and_runtime_assert_are_preserved() {
    let source = "\
#define _requires(p) __attribute__((annotate(\"pal-requires\", p)))\n\
#define _inline_pulse(p) _inline_pulse(__capture_args(p))\n\
#define _container_of(p, t, f) ((t *)((char *)(p) - offsetof(t, f)))\n\
void f(void) { _assert(\"runtime\", \"file\", 12); }\n";
    let (overlay, stripped, _) = extract(source);
    assert!(overlay.annotations.is_empty());
    assert_eq!(stripped, source);
}

#[test]
fn nested_snippets_line_splices_and_crlf_roundtrip() {
    let source = "void f(int x)\r\n _requires(\\\r\n _inline_pulse(pure ($(x) >= 0)))\r\n{\r\n _ghost_stmt(let s = \"(()\" in assert (pure (s == s)));\r\n}\r\n";
    let (overlay, stripped, _) = extract(source);
    assert_eq!(overlay.annotations.len(), 2);
    assert!(!stripped.contains("_inline_pulse"));
    assert!(stripped.contains("\r\n"));
}

#[test]
fn standalone_proof_lines_disappear_but_controlled_bodies_remain() {
    let source = "void f(int x)
    _requires(x >= 0)
{
    _ghost_stmt(before ());
    _assert(x >= 0);
    x++;
    if (x) _ghost_stmt(yes ()); else _assert(x == 0);
    while (x) _ghost_stmt(step ());
    for (_ghost_stmt(start ()); x; _ghost_stmt(next ())) {}
    _ghost_stmt(after ()); // keep this comment
}
"
    .replace('\n', "\r\n");
    let (_, stripped, _) = extract(&source);
    assert!(stripped.starts_with("void f(int x)\r\n{\r\n    x++;\r\n"));
    assert!(stripped.contains("if (x) ((void)0); else ((void)0);"));
    assert!(stripped.contains("while (x) ((void)0);"));
    assert!(stripped.contains("for (((void)0); x; ((void)0)) {}"));
    assert!(stripped.contains("// keep this comment"));
}

#[test]
fn older_overlays_keep_their_noop_roundtrip() {
    let source = "void f(void)\n    _requires(1)\n{\n    _ghost_stmt(step ());\n}\n";
    let (overlay, stripped) = extract_source_mode("old.c".into(), source, &[], false).unwrap();
    let serialized = toml::to_string(&overlay)
        .unwrap()
        .replace("compact_statements = false\n", "");
    let overlay: FileOverlay = toml::from_str(&serialized).unwrap();
    assert!(stripped.contains("((void)0);"));
    assert_eq!(apply_source(&overlay, &stripped, &[]).unwrap(), source);
    assert_eq!(apply_source(&overlay, source, &[]).unwrap(), source);
}

#[test]
fn compact_proofs_preserve_preprocessor_controlled_and_labeled_bodies() {
    let source = "void f(int x) {
    if (x)
#ifdef ENABLED
        _assert(x > 0);
#else
        _ghost_stmt(step ());
#endif
    x++;
    label: _ghost_stmt(labeled ());
    do _ghost_stmt(body ()); while (x);
}
";
    let (_, stripped, _) = extract(source);
    assert!(stripped.contains("#ifdef ENABLED\n        ((void)0);\n#else\n        ((void)0);"));
    assert!(stripped.contains("label: ((void)0);"));
    assert!(stripped.contains("do ((void)0); while (x);"));
}

#[test]
fn consecutive_compact_proofs_relocate_and_reapply_after_indentation_changes() {
    let source = "void f(int x) {
    _ghost_stmt(first ());
    _ghost_stmt(second ());
    x++;
    _ghost_stmt(last ());
}
";
    let (overlay, stripped, macros) = extract(source);
    let edited = stripped.replace("    x++;", "\tx++;") + "\nint unrelated;\n";
    let restored = apply_source(&overlay, &edited, &macros).unwrap();
    let first = restored.find("_ghost_stmt(first ())").unwrap();
    let second = restored.find("_ghost_stmt(second ())").unwrap();
    assert!(first < second && second < restored.find("x++;").unwrap());
    assert!(restored.ends_with("\nint unrelated;\n"));
    assert_eq!(
        apply_source(&overlay, &restored, &macros).unwrap(),
        restored
    );
}

#[test]
fn toml_preserves_pulse_quotes_and_multiline_payloads() {
    let source = r#"void f(void) {
_ghost_stmt(
    let quote = "'''\n\"\"\"" in
    (* a Pulse comment *)
    assert pure (quote == quote));
}
"#;
    let (file, stripped, macros) = extract(source);
    let overlay = Overlay {
        format_version: 1,
        include_dirs: Vec::new(),
        files: vec![file],
    };
    let serialized = toml::to_string_pretty(&overlay).unwrap();
    let parsed: Overlay = toml::from_str(&serialized).unwrap();
    assert_eq!(
        apply_source(&parsed.files[0], &stripped, &macros).unwrap(),
        source
    );
}

#[test]
fn named_owners_survive_unrelated_functions_and_formatting() {
    let source = "int f(int x) _requires(x > 0) { return x; }\nint g(void) { return 1; }\n";
    let (overlay, stripped, macros) = extract(source);
    assert_eq!(overlay.annotations[0].owner.name, "f");
    let changed = format!("int added;\n{}", stripped.replace("return 1", "return 2"));
    let restored = apply_source(&overlay, &changed, &macros).unwrap();
    assert_eq!(
        restored,
        format!("int added;\n{}", source.replace("return 1", "return 2"))
    );
    let formatted = changed.replace("int f(int x) ", "int f ( int x )\n");
    let reapplied = apply_source(&overlay, &formatted, &macros).unwrap();
    assert!(reapplied.contains("_requires(x > 0)"));
    assert_eq!(
        apply_source(&overlay, &reapplied, &macros).unwrap(),
        reapplied
    );
}

#[test]
fn identical_loop_headers_use_required_surrounding_context() {
    let source = "\
void f(int i, int n) {\n\
    while (i < n) _invariant(i >= 0) { i++; }\n\
    i = 0;\n\
    while (i < n) _invariant(i <= n) { i++; }\n\
}\n";
    let (overlay, stripped, macros) = extract(source);
    let changed = format!("int unrelated;\n{stripped}");
    let restored = apply_source(&overlay, &changed, &macros).unwrap();
    assert_eq!(restored, format!("int unrelated;\n{source}"));
    let changed = changed.replace("i = 0;", "i = 1;");
    assert!(
        apply_source(&overlay, &changed, &macros)
            .unwrap_err()
            .contains("required token context")
    );
}

#[test]
fn ambiguous_owners_and_changed_local_context_conflict() {
    let source = "int f(int x) _requires(x > 0) { return x; }\n";
    let (overlay, stripped, macros) = extract(source);
    let duplicate = format!("{stripped}\n{stripped}");
    assert!(
        apply_source(&overlay, &duplicate, &macros)
            .unwrap_err()
            .contains("found 2")
    );
    let renamed = stripped.replace("int x", "int y");
    assert!(apply_source(&overlay, &renamed, &macros).is_err());
    let wrong_annotation = source.replace("x > 0", "x < 0");
    assert!(
        apply_source(&overlay, &wrong_annotation, &macros)
            .unwrap_err()
            .contains("differ")
    );
}

#[test]
fn conditional_owners_are_distinct() {
    let source = "\
#ifdef A\n\
int f(int x) _ensures(return == x) { return x; }\n\
#else\n\
int f(int x) _ensures(return == 0) { return 0; }\n\
#endif\n";
    let (overlay, stripped, macros) = extract(source);
    assert_ne!(overlay.annotations[0].owner, overlay.annotations[1].owner);
    let changed = format!("/* new */\n{stripped}");
    assert_eq!(
        apply_source(&overlay, &changed, &macros).unwrap(),
        format!("/* new */\n{source}")
    );
}

#[test]
fn formatted_macro_bodies_and_top_level_helpers_stay_on_the_correct_line() {
    let source = "\
#define OWNED _refine(this != 0)\n\
OWNED int *p;\n\
#ifdef A\n\
_include_pulse(Helpers, let proof = ())\n\
#endif\n";
    let (overlay, stripped, macros) = extract(source);
    assert_eq!(overlay.annotations[0].owner.name, "OWNED");
    let formatted = stripped
        .replace("#define OWNED ", "#define OWNED    ")
        .replace("#endif", "  #endif");
    let restored = apply_source(&overlay, &formatted, &macros).unwrap();
    assert!(restored.contains("#define OWNED _refine(this != 0)"));
    assert!(restored.contains("_include_pulse(Helpers, let proof = ())\n#endif"));
    assert_eq!(
        apply_source(&overlay, &restored, &macros).unwrap(),
        restored
    );
    let (_, cleaned) = extract_source("sample.c".into(), &restored, &macros).unwrap();
    assert!(cleaned.contains("#define OWNED"));
}

#[test]
fn malformed_annotation_and_standalone_inline_pulse_fail() {
    assert!(extract_source("x.c".into(), "int f(void) _requires(1;", &[]).is_err());
    assert!(extract_source("x.c".into(), "int x = _inline_pulse(foo);", &[]).is_err());
}
