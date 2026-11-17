mod anchors;
mod files;
mod lex;
mod preservation;
#[cfg(test)]
mod tests;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

pub use files::{apply_files, extract_files};
use lex::{Lexed, Token, close_paren, lex};

type Result<T> = std::result::Result<T, String>;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Overlay {
    format_version: u32,
    files: Vec<FileOverlay>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FileOverlay {
    path: String,
    original_sha256: String,
    stripped_sha256: String,
    #[serde(default)]
    compact_statements: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    macros: Vec<Macro>,
    annotations: Vec<Annotation>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Annotation {
    id: String,
    offset: usize,
    text: String,
    replacement: String,
    owner: Owner,
    site: Site,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Owner {
    kind: String,
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    context: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Site {
    kind: String,
    before: Vec<String>,
    after: Vec<String>,
    replacement_tokens: Vec<String>,
    at_start: bool,
    at_end: bool,
    gap_before: String,
    gap_after: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Macro {
    name: String,
    arguments: bool,
    kind: MacroKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum MacroKind {
    Attribute,
    Expression,
    TopLevel,
}

impl MacroKind {
    fn replacement(self) -> &'static str {
        match self {
            Self::Expression => "((void)0)",
            _ => "",
        }
    }

    fn site(self) -> &'static str {
        match self {
            Self::Attribute => "declaration",
            Self::Expression => "expression",
            Self::TopLevel => "top-level",
        }
    }
}

fn builtins() -> BTreeMap<String, Macro> {
    let mut macros = BTreeMap::new();
    for (names, arguments, kind) in [
        (
            "_requires _ensures _refine _refines _refine_always _refine_uninit \
             _refine_value _invariant _do_while_first _do_while_cond _ghost_arg \
             _cursor_from _decreases _preserves _preserves_value",
            true,
            MacroKind::Attribute,
        ),
        (
            "_plain _core_ref _nullable _mutable _consumes _out _array _arrayptr \
             _cursor _pure _total _pal_ignore _pal_admit _pal_overread \
             _pulse_opaque_to_smt _rec _pulse_eager_unfold_predicate _pointer_view \
             _overlay _owning _memset_zero _allocated",
            false,
            MacroKind::Attribute,
        ),
        ("_assert _ghost_stmt", true, MacroKind::Expression),
        (
            "_include_pulse _let _let_rec _letimpure _type",
            true,
            MacroKind::TopLevel,
        ),
    ] {
        for name in names.split_whitespace() {
            macros.insert(
                name.into(),
                Macro {
                    name: name.into(),
                    arguments,
                    kind,
                },
            );
        }
    }
    macros
}

fn hash(source: &str) -> String {
    format!("{:x}", Sha256::digest(source.as_bytes()))
}

struct Definition<'a> {
    name: &'a str,
    arguments: bool,
    body: std::ops::Range<usize>,
}

fn definition<'a>(
    source: &str,
    tokens: &'a [Token],
    range: std::ops::Range<usize>,
) -> Result<Option<Definition<'a>>> {
    if range.len() < 3 || tokens[range.start + 1].text != "define" {
        return Ok(None);
    }
    let name = &tokens[range.start + 2];
    let mut start = range.start + 3;
    let arguments = start < range.end
        && tokens[start].text == "("
        && source[name.end..tokens[start].start]
            .replace("\\\r\n", "")
            .replace("\\\n", "")
            .is_empty();
    if arguments {
        start = close_paren(tokens, start)? + 1;
    }
    Ok(Some(Definition {
        name: &name.text,
        arguments,
        body: start..range.end,
    }))
}

fn invocation_end(tokens: &[Token], i: usize, annotation: &Macro) -> Result<Option<usize>> {
    if !annotation.arguments {
        return Ok(Some(i + 1));
    }
    if tokens.get(i + 1).map(|token| token.text.as_str()) != Some("(") {
        return Ok(None);
    }
    let close = close_paren(tokens, i + 1)?;
    if annotation.name == "_assert" {
        let mut depth = 0;
        let mut commas = 0;
        for token in &tokens[i + 2..close] {
            match token.text.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
                "," if depth == 0 => commas += 1,
                _ => {}
            }
        }
        if commas == 2 {
            return Ok(None);
        }
        if commas != 0 {
            return Err(format!(
                "unsupported _assert arity at byte {}",
                tokens[i].start
            ));
        }
    }
    Ok(Some(close + 1))
}

fn discover_macros(sources: &[&str]) -> Result<Vec<Macro>> {
    let base = builtins();
    let mut macros = base.clone();
    let mut undefined = std::collections::BTreeSet::new();
    loop {
        let previous = macros.clone();
        let mut definitions: BTreeMap<String, Vec<(bool, Vec<Token>)>> = BTreeMap::new();
        for source in sources {
            let lexed = lex(source)?;
            for directive in &lexed.directives {
                let tokens = &lexed.tokens[directive.tokens.clone()];
                if tokens.get(1).map(|token| token.text.as_str()) == Some("undef")
                    && let Some(name) = tokens.get(2)
                {
                    undefined.insert(name.text.clone());
                }
                let Some(def) = definition(source, &lexed.tokens, directive.tokens.clone())? else {
                    continue;
                };
                if base.contains_key(def.name) || def.name == "_inline_pulse" {
                    continue;
                }
                definitions
                    .entry(def.name.into())
                    .or_default()
                    .push((def.arguments, lexed.tokens[def.body].to_vec()));
            }
        }
        macros = base.clone();
        for (name, definitions) in definitions {
            let arguments = definitions[0].0;
            let mut pure = true;
            let mut found = false;
            let mut kind = MacroKind::Attribute;
            for (has_arguments, body) in definitions {
                if has_arguments != arguments {
                    pure = false;
                }
                let mut i = 0;
                while i < body.len() {
                    let Some(annotation) = previous.get(&body[i].text) else {
                        break;
                    };
                    let Some(end) = invocation_end(&body, i, annotation)? else {
                        break;
                    };
                    if annotation.kind != MacroKind::Attribute {
                        kind = annotation.kind;
                    }
                    found = true;
                    i = end;
                }
                if i != body.len() {
                    pure = false;
                }
            }
            // A wrapper with a runtime definition in any branch must remain a
            // runtime macro. Its individual annotation invocations are still
            // extracted from the replacement body.
            if pure && found {
                macros.insert(
                    name.clone(),
                    Macro {
                        name,
                        arguments,
                        kind,
                    },
                );
            }
        }
        if macros == previous {
            break;
        }
    }
    let aliases: Vec<_> = macros
        .into_values()
        .filter(|annotation| !base.contains_key(&annotation.name))
        .collect();
    for alias in &aliases {
        if undefined.contains(&alias.name) {
            return Err(format!(
                "annotation wrapper {} is undefined in its include context; cannot safely classify its uses",
                alias.name
            ));
        }
    }
    if !aliases.is_empty() {
        for source in sources {
            let edits: Vec<_> = removals(source, &[])?.into_iter().map(|r| r.edit).collect();
            let clean = edit_source(source, &edits)?;
            for name in anchors::declared_names(&clean)? {
                if aliases.iter().any(|alias| alias.name == name) {
                    return Err(format!(
                        "annotation wrapper {} is also a C declaration; cannot safely classify its uses",
                        name
                    ));
                }
            }
        }
    }
    Ok(aliases)
}

#[derive(Debug)]
struct Edit {
    start: usize,
    end: usize,
    text: String,
}

struct Removal {
    edit: Edit,
    kind: &'static str,
}

fn removals(source: &str, macros: &[Macro]) -> Result<Vec<Removal>> {
    let mut known = builtins();
    for annotation in macros {
        if known
            .insert(annotation.name.clone(), annotation.clone())
            .is_some()
        {
            return Err(format!("duplicate or reserved macro: {}", annotation.name));
        }
    }
    let Lexed { tokens, directives } = lex(source)?;
    let base = builtins();
    let mut edits = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];
        let mut in_macro = false;
        if let Some(n) = token.directive {
            let directive = &directives[n];
            let Some(def) = definition(source, &tokens, directive.tokens.clone())? else {
                i = directive.tokens.end;
                continue;
            };
            if base.contains_key(def.name) || def.name == "_inline_pulse" {
                i = directive.tokens.end;
                continue;
            }
            if i < def.body.start {
                i = def.body.start;
                continue;
            }
            in_macro = true;
        }
        let Some(annotation) = known.get(&token.text) else {
            if token.text == "_inline_pulse" {
                return Err(format!(
                    "_inline_pulse outside a removable annotation at byte {}",
                    token.start
                ));
            }
            i += 1;
            continue;
        };
        let Some(end) = invocation_end(&tokens, i, annotation)? else {
            i += 1;
            continue;
        };
        if token.directive != tokens[end - 1].directive {
            return Err(format!(
                "annotation crosses a preprocessor directive at byte {}",
                token.start
            ));
        }
        edits.push(Removal {
            edit: Edit {
                start: token.start,
                end: tokens[end - 1].end,
                text: annotation.kind.replacement().into(),
            },
            kind: if in_macro {
                "macro-body"
            } else {
                annotation.kind.site()
            },
        });
        i = end;
    }
    Ok(edits)
}

fn edit_source(source: &str, edits: &[Edit]) -> Result<String> {
    let mut result = String::new();
    let mut cursor = 0;
    for edit in edits {
        if edit.start < cursor
            || edit.start > edit.end
            || !source.is_char_boundary(edit.start)
            || !source.is_char_boundary(edit.end)
        {
            return Err("overlapping or invalid annotation edits".into());
        }
        result.push_str(&source[cursor..edit.start]);
        result.push_str(&edit.text);
        cursor = edit.end;
    }
    result.push_str(&source[cursor..]);
    Ok(result)
}

fn extract_source(path: String, source: &str, macros: &[Macro]) -> Result<(FileOverlay, String)> {
    extract_source_mode(path, source, macros, true)
}

fn compact_statements(source: &str, removals: &mut [Removal]) -> Result<()> {
    let mut skeleton = String::new();
    let mut cursor = 0;
    let mut positions = Vec::new();
    for removal in removals.iter() {
        skeleton.push_str(&source[cursor..removal.edit.start]);
        positions.push(skeleton.len());
        skeleton.push_str(&removal.edit.text);
        cursor = removal.edit.end;
    }
    skeleton.push_str(&source[cursor..]);
    let statements = anchors::standalone_statements(&skeleton)?;
    for (removal, position) in removals.iter_mut().zip(positions) {
        let edit = &mut removal.edit;
        if removal.kind == "expression" {
            let Some(&end) = statements.get(&position) else {
                continue;
            };
            let tail = &skeleton[position + edit.text.len()..end];
            if tail.trim() != ";" || source.get(edit.end..edit.end + tail.len()) != Some(tail) {
                continue;
            }
            edit.end += tail.len();
            edit.text.clear();
            removal.kind = "statement";
        } else if removal.kind != "declaration" {
            continue;
        }
        // Remove a whole proof-only line, including its indentation, but never
        // consume an adjacent comment or the body of an unbraced control flow.
        let line_start = source[..edit.start].rfind('\n').map_or(0, |i| i + 1);
        let line_end = source[edit.end..]
            .find('\n')
            .map_or(source.len(), |i| edit.end + i + 1);
        if source[line_start..edit.start].trim().is_empty()
            && source[edit.end..line_end].trim().is_empty()
        {
            edit.start = line_start;
            edit.end = line_end;
        }
    }
    Ok(())
}

fn extract_source_mode(
    path: String,
    source: &str,
    macros: &[Macro],
    compact: bool,
) -> Result<(FileOverlay, String)> {
    let mut removals = removals(source, macros)?;
    if compact {
        compact_statements(source, &mut removals)?;
    }
    let mut stripped = String::new();
    let mut cursor = 0;
    let mut offsets = Vec::new();
    for removal in &removals {
        stripped.push_str(&source[cursor..removal.edit.start]);
        offsets.push(stripped.len());
        stripped.push_str(&removal.edit.text);
        cursor = removal.edit.end;
    }
    stripped.push_str(&source[cursor..]);
    let tokens = lex(&stripped)?.tokens;
    let scopes = anchors::scopes(&stripped, &tokens)?;
    let mut annotations = Vec::new();
    for (index, (removal, offset)) in removals.iter().zip(offsets).enumerate() {
        let edit = &removal.edit;
        let (owner, mut site) =
            anchors::locate(&tokens, &scopes, offset, &edit.text, removal.kind)?;
        let token_index = tokens.partition_point(|token| token.end <= offset);
        let left = token_index.checked_sub(1).map_or(0, |i| tokens[i].end);
        let right = tokens
            .get(token_index + site.replacement_tokens.len())
            .map_or(stripped.len(), |token| token.start);
        site.gap_before = stripped[left..offset].into();
        site.gap_after = stripped[offset + edit.text.len()..right].into();
        annotations.push(Annotation {
            id: format!("{}-{}", owner.name, index + 1),
            offset,
            text: source[edit.start..edit.end].into(),
            replacement: edit.text.clone(),
            owner,
            site,
        });
    }
    Ok((
        FileOverlay {
            path,
            original_sha256: hash(source),
            stripped_sha256: hash(&stripped),
            compact_statements: compact,
            macros: macros.to_vec(),
            annotations,
        },
        stripped,
    ))
}

fn restore_clean(file: &FileOverlay, source: &str) -> Result<String> {
    let exact = hash(source) == file.stripped_sha256;
    let tokens = lex(source)?.tokens;
    let scopes = anchors::scopes(source, &tokens)?;
    let mut edits = Vec::new();
    for annotation in &file.annotations {
        preservation::validate_replacement(annotation)?;
        let (start, end, text) = if exact {
            let end = annotation
                .offset
                .checked_add(annotation.replacement.len())
                .ok_or("annotation offset overflow")?;
            if source.get(annotation.offset..end) != Some(&annotation.replacement) {
                return Err(format!(
                    "{}: invalid exact-match replacement",
                    annotation.id
                ));
            }
            (annotation.offset, end, annotation.text.clone())
        } else {
            let owners: Vec<_> = scopes
                .iter()
                .filter(|scope| scope.owner == annotation.owner)
                .collect();
            if owners.len() != 1 {
                return Err(format!(
                    "{}: expected one owner {:?} {}, found {}",
                    annotation.id,
                    annotation.owner.kind,
                    annotation.owner.name,
                    owners.len()
                ));
            }
            let candidates = anchors::candidates(&tokens, owners[0], &annotation.site);
            if candidates.len() != 1 {
                return Err(format!(
                    "{}: expected one attachment site in {}, found {}; required token context changed or is ambiguous",
                    annotation.id,
                    annotation.owner.name,
                    candidates.len()
                ));
            }
            let i = candidates[0];
            if annotation.site.replacement_tokens.is_empty() {
                let left = i.checked_sub(1).map_or(0, |i| tokens[i].end);
                let right = tokens.get(i).map_or(source.len(), |token| token.start);
                let old_gap = format!(
                    "{}{}",
                    annotation.site.gap_before, annotation.site.gap_after
                );
                if source[left..right] == old_gap {
                    let start = left + annotation.site.gap_before.len();
                    (start, start, annotation.text.clone())
                } else if annotation.site.kind == "macro-body" {
                    (left, left, format!(" {}", annotation.text))
                } else if annotation.site.kind == "top-level" {
                    (right, right, format!("\n{}\n", annotation.text))
                } else {
                    // Whitespace may have changed. Insert at the right token,
                    // adding separators so declaration tokens cannot merge.
                    (right, right, format!(" {} ", annotation.text))
                }
            } else {
                let start = tokens[i].start;
                let end = tokens[i + annotation.site.replacement_tokens.len() - 1].end;
                (start, end, annotation.text.clone())
            }
        };
        preservation::validate_removed_text(annotation, &source[start..end])?;
        edits.push(Edit { start, end, text });
    }
    edits.sort_by_key(|edit| edit.start);
    edit_source(source, &edits)
}

fn render_source(file: &FileOverlay, source: &str, macros: &[Macro]) -> Result<String> {
    if file.annotations.is_empty() {
        return Ok(source.into());
    }
    let existing = removals(source, macros)?;
    if !existing.is_empty() {
        let (current, clean) =
            extract_source_mode(file.path.clone(), source, macros, file.compact_statements)?;
        let restored = restore_clean(file, &clean)?;
        let mut expected_payloads: Vec<_> =
            file.annotations.iter().map(|a| a.text.trim()).collect();
        let mut actual_payloads: Vec<_> =
            current.annotations.iter().map(|a| a.text.trim()).collect();
        expected_payloads.sort();
        actual_payloads.sort();
        let expected = lex(&restored)?.tokens;
        let actual = lex(source)?.tokens;
        if expected_payloads == actual_payloads
            && expected.len() == actual.len()
            && expected
                .iter()
                .zip(&actual)
                .all(|(a, b)| a.text == b.text && a.directive == b.directive)
        {
            return Ok(source.into());
        }
        return Err("source contains annotations that differ from this overlay; refusing to duplicate or overwrite them".into());
    }
    restore_clean(file, source)
}
