use super::*;

fn extract(source: &str) -> (FileOverlay, String, Vec<Macro>) {
    let macros = discover_macros(&[source]).unwrap();
    let (overlay, stripped) = extract_source("sample.c".into(), source, &macros).unwrap();
    assert_eq!(apply_source(&overlay, &stripped, &macros).unwrap(), source);
    assert_eq!(apply_source(&overlay, source, &macros).unwrap(), source);
    (overlay, stripped, macros)
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
