use super::{
    Annotation, Edit, FileOverlay, Macro, Result, anchors, definition, edit_source,
    extract_source_mode, lex, removals,
};

pub(super) fn validate_replacement(annotation: &Annotation) -> Result<()> {
    if !matches!(annotation.replacement.as_str(), "" | "((void)0)")
        || lex::texts(&lex(&annotation.replacement)?.tokens) != annotation.site.replacement_tokens
    {
        return Err(format!(
            "{}: source preservation: replacement is not annotation scaffolding",
            annotation.id
        ));
    }
    Ok(())
}

pub(super) fn validate_removed_text(annotation: &Annotation, removed: &str) -> Result<()> {
    // Relocation may change a placeholder's spacing, but must not delete user
    // comments or any other bytes along with it.
    let compact: String = removed
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    if compact != annotation.replacement {
        return Err(format!(
            "{}: source preservation: replacing this site would remove non-annotation text",
            annotation.id
        ));
    }
    Ok(())
}

fn validate_payload(file: &FileOverlay, annotation: &Annotation, macros: &[Macro]) -> Result<()> {
    validate_replacement(annotation)?;
    let parsed = removals(&annotation.text, macros)?;
    let invalid = || {
        format!(
            "{}: source preservation: payload must contain exactly one proof annotation",
            annotation.id
        )
    };
    let [removal] = parsed.as_slice() else {
        return Err(invalid());
    };
    let edit = &removal.edit;
    if !annotation.text[..edit.start].trim().is_empty() {
        return Err(invalid());
    }
    let suffix = annotation.text[edit.end..].trim();
    let replacement = if file.compact_statements && removal.kind == "expression" && suffix == ";" {
        ""
    } else if suffix.is_empty() {
        &edit.text
    } else {
        return Err(invalid());
    };
    if annotation.replacement != replacement {
        return Err(format!(
            "{}: source preservation: replacement does not match the annotation's erasure",
            annotation.id
        ));
    }
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
struct RuntimeSource {
    tokens: Vec<(String, Option<usize>)>,
    definitions: Vec<(String, bool)>,
}

fn runtime_source(source: &str, macros: &[Macro]) -> Result<RuntimeSource> {
    // Use a fixed erasure policy, independent of the sidecar's compact mode.
    let edits: Vec<_> = removals(source, macros)?
        .into_iter()
        .map(|r| r.edit)
        .collect();
    let erased = edit_source(source, &edits)?;
    let lexed = lex(&erased)?;
    let statements = anchors::standalone_statements(&erased)?;
    let mut scaffolding = Vec::new();
    for (start, end) in statements {
        let first = lexed.tokens.partition_point(|token| token.end <= start);
        let last = lexed.tokens.partition_point(|token| token.start < end);
        if lex::texts(&lexed.tokens[first..last]) == ["(", "(", "void", ")", "0", ")", ";"] {
            scaffolding.push(Edit {
                start,
                end,
                text: String::new(),
            });
        }
    }
    let erased = edit_source(&erased, &scaffolding)?;
    let lexed = lex(&erased)?;
    let mut definitions = Vec::new();
    for directive in &lexed.directives {
        if let Some(def) = definition(&erased, &lexed.tokens, directive.tokens.clone())? {
            // F(x) and F (x) have identical tokens but define different macros.
            definitions.push((def.name.into(), def.arguments));
        }
    }
    Ok(RuntimeSource {
        tokens: lexed
            .tokens
            .into_iter()
            .map(|t| (t.text, t.directive))
            .collect(),
        definitions,
    })
}

pub(super) fn validate_application(
    file: &FileOverlay,
    original: &str,
    updated: &str,
    macros: &[Macro],
) -> Result<()> {
    for advertised in &file.macros {
        if !macros.contains(advertised) {
            return Err(format!(
                "source preservation: wrapper {} is not a verified annotation-only macro in the source/include context",
                advertised.name
            ));
        }
    }
    for annotation in &file.annotations {
        validate_payload(file, annotation, macros)?;
    }
    if file.annotations.is_empty() {
        return Ok(());
    }
    // A payload must also be recognized in situ, not swallowed by an existing
    // comment/string or joined to surrounding source tokens.
    let (observed, _) =
        extract_source_mode(file.path.clone(), updated, macros, file.compact_statements)?;
    let mut expected: Vec<_> = file.annotations.iter().map(|a| a.text.trim()).collect();
    let mut actual: Vec<_> = observed.annotations.iter().map(|a| a.text.trim()).collect();
    expected.sort();
    actual.sort();
    if expected != actual {
        return Err("source preservation: applied annotations do not match the payloads in their source context".into());
    }
    let before = runtime_source(original, macros)?;
    let after = runtime_source(updated, macros)?;
    if before.definitions != after.definitions {
        return Err("source preservation: application changes a preprocessor macro's name or function-like form".into());
    }
    let mismatch = before
        .tokens
        .iter()
        .zip(&after.tokens)
        .position(|(a, b)| a != b);
    if let Some(index) = mismatch.or_else(|| {
        (before.tokens.len() != after.tokens.len())
            .then_some(before.tokens.len().min(after.tokens.len()))
    }) {
        return Err(format!(
            "source preservation: runtime/preprocessor token {index} differs: before {:?}, after {:?}",
            before.tokens.get(index),
            after.tokens.get(index)
        ));
    }
    Ok(())
}
