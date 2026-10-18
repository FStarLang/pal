//! Current-candidate PAL metadata and owned, public-path verifier diagnostics.

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

use lsp_types::{Diagnostic, DiagnosticSeverity, NumberOrString, Position, Range};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::Value;

use super::{
    navigation::SemanticIndex,
    workspace::{self, Failure, Result, Snapshot},
};

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(transparent)]
pub struct Diagnostics(BTreeMap<String, Vec<Diagnostic>>);

impl Diagnostics {
    pub fn new() -> Self {
        Self::default()
    }
}

impl std::ops::Deref for Diagnostics {
    type Target = BTreeMap<String, Vec<Diagnostic>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Diagnostics {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug)]
pub struct TranslationMetadata {
    pub diagnostics: Diagnostics,
    /// Generated basenames, including interface aliases, owned by this candidate's C declarations.
    pub owners: BTreeMap<String, (PathBuf, Range)>,
    /// Validated implementation basenames mapped to their source C declaration names.
    pub declarations: BTreeMap<String, String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SourceRangeInfo {
    source_files: Vec<SourceInfo>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceInfo {
    uri: String,
    modules: Vec<ModuleInfo>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ModuleInfo {
    fst_file: String,
    decl_name: String,
    source_range: Range,
    mappings: Vec<PositionMapping>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PositionMapping {
    source: Position,
    pulse: Position,
}

/// Read fresh metadata even when the generated proof problem will hit the artifact cache.
pub fn translation(
    snapshot: &Snapshot,
    index: &SemanticIndex,
    status_uri: &str,
) -> Result<TranslationMetadata> {
    let redactor = Redactor::new(snapshot);
    let raw: Diagnostics = read_metadata(&snapshot.out().join("diagnostics.json"), &redactor)?;
    let info: SourceRangeInfo =
        read_metadata(&snapshot.out().join("source_range_info.json"), &redactor)?;
    let mut diagnostics = Diagnostics::new();
    for (name, entries) in raw.0 {
        let path = source_path(snapshot, &name)?;
        let target_uri = path
            .as_ref()
            .map(|path| workspace::uri(path))
            .unwrap_or_else(|| status_uri.to_owned());
        let target = diagnostics.entry(target_uri).or_insert_with(Vec::new);
        for mut diagnostic in entries {
            if !matches!(
                diagnostic.severity,
                Some(DiagnosticSeverity::ERROR | DiagnosticSeverity::WARNING)
            ) {
                return Err(metadata_failure(
                    "PAL diagnostic has a missing or invalid severity",
                ));
            }
            if let Some(path) = &path {
                diagnostic.range = normalize(snapshot, index, path, diagnostic.range)?;
            } else {
                diagnostic.data = Some(
                    serde_json::json!({"file_name":basename(&name),"byte_range":diagnostic.range,"details":diagnostic.data.take()}),
                );
                diagnostic.range = Range::default();
                diagnostic.source.get_or_insert_with(|| "PAL".to_owned());
            }
            if let Some(related) = &mut diagnostic.related_information {
                for item in related {
                    if let Some(path) = source_path(snapshot, item.location.uri.as_str())? {
                        item.location.range =
                            normalize(snapshot, index, &path, item.location.range)?;
                        item.location.uri = workspace::uri(&path)
                            .parse()
                            .map_err(|_| metadata_failure("invalid public diagnostic URI"))?;
                    } else {
                        item.message =
                            format!("{}: {}", basename(item.location.uri.as_str()), item.message);
                        item.location.uri = status_uri
                            .parse()
                            .map_err(|_| metadata_failure("invalid job status URI"))?;
                        item.location.range = Range::default();
                    }
                    item.message = redactor.text(&item.message);
                }
            }
            diagnostic.message = redactor.text(&diagnostic.message);
            if let Some(source) = &mut diagnostic.source {
                *source = redactor.text(source);
            }
            if let Some(NumberOrString::String(code)) = &mut diagnostic.code {
                *code = redactor.text(code);
            }
            if let Some(description) = &mut diagnostic.code_description {
                description.href = redactor
                    .text(description.href.as_str())
                    .parse()
                    .map_err(|_| metadata_failure("invalid diagnostic code-description URI"))?;
            }
            if let Some(data) = &mut diagnostic.data {
                redactor.value(data);
            }
            target.push(diagnostic);
        }
    }
    let mut owners = BTreeMap::new();
    let mut declarations = BTreeMap::new();
    for source in info.source_files {
        let path = source_path(snapshot, &source.uri)?;
        let file = path.as_ref().map(|path| &snapshot.files[path]);
        for module in source.modules {
            if module.fst_file.contains(['/', '\\'])
                || !module.fst_file.ends_with(".fst")
                || module.fst_file == ".fst"
                || module.decl_name.is_empty()
                || !snapshot.out().join(&module.fst_file).is_file()
            {
                return Err(metadata_failure(
                    "source-range metadata names an invalid or missing generated module",
                ));
            }
            let (Some(path), Some(file)) = (&path, file) else {
                continue;
            };
            let broad = normalize(snapshot, index, path, module.source_range)?;
            for mapping in module.mappings {
                file.byte_position(mapping.source.line, mapping.source.character)
                    .map_err(|_| {
                        metadata_failure(
                            "source-range metadata contains an invalid source position",
                        )
                    })?;
                // Pulse positions are already generated-text coordinates, not C ownership evidence.
                let _ = mapping.pulse;
            }
            let range = index
                .declaration_range(path, &module.decl_name)
                .unwrap_or(broad);
            let owner = (path.clone(), range);
            let declaration = redactor.text(&module.decl_name);
            if declarations
                .get(&module.fst_file)
                .is_some_and(|previous| previous != &declaration)
            {
                return Err(metadata_failure(
                    "source-range metadata assigns a module to conflicting declarations",
                ));
            }
            declarations.insert(module.fst_file.clone(), declaration);
            let interface = format!("{}i", module.fst_file);
            for name in [module.fst_file, interface] {
                if let Some(previous) = owners.insert(name, owner.clone()) {
                    if previous != owner {
                        return Err(metadata_failure(
                            "source-range metadata assigns a module to conflicting declarations",
                        ));
                    }
                }
            }
        }
    }
    Ok(TranslationMetadata {
        diagnostics,
        owners,
        declarations,
    })
}

fn read_metadata<T: DeserializeOwned>(path: &Path, redactor: &Redactor) -> Result<T> {
    let path_text = path.to_string_lossy();
    let name = basename(&path_text);
    let bytes = fs::read(path).map_err(|error| {
        metadata_failure(redactor.text(&format!("cannot read {name}: {error}")))
    })?;
    serde_json::from_slice(&bytes)
        .map_err(|error| metadata_failure(redactor.text(&format!("invalid {name}: {error}"))))
}

fn metadata_failure(message: impl Into<String>) -> Failure {
    Failure::new("translation_failed", message)
}

fn normalize(
    snapshot: &Snapshot,
    index: &SemanticIndex,
    path: &Path,
    range: Range,
) -> Result<Range> {
    index
        .normalize_range(snapshot, path, range)
        .map_err(|_| metadata_failure("PAL metadata contains an invalid source range"))
}

fn source_path(snapshot: &Snapshot, name: &str) -> Result<Option<PathBuf>> {
    if name.contains("://") && !name.starts_with("file://") {
        return Err(metadata_failure(
            "PAL metadata contains an invalid source URI",
        ));
    }
    let raw = name.strip_prefix("file://").unwrap_or(name);
    // PAL currently emits raw paths after file://; prefer exact spellings before URI decoding.
    let decoded = decode_path(raw);
    for spelling in std::iter::once(raw).chain(decoded.as_deref()) {
        if let Some(path) = snapshot
            .original(Path::new(spelling))
            .filter(|path| snapshot.files.contains_key(path))
        {
            return Ok(Some(path));
        }
    }
    let logical = decoded.as_deref().unwrap_or(raw).trim_start_matches('/');
    if logical.starts_with('<') && logical.ends_with('>') {
        return Ok(None);
    }
    let path = snapshot.root.join(raw);
    let path = fs::canonicalize(&path)
        .or_else(|_| fs::canonicalize(snapshot.root.join(decoded.as_deref().unwrap_or(raw))))
        .map_err(|_| metadata_failure("PAL metadata refers to an unavailable source file"))?;
    if path.starts_with(&snapshot.root)
        || path.starts_with(snapshot.storage.path())
        || !path.is_file()
    {
        return Err(metadata_failure(
            "PAL metadata refers to an uncaptured project source file",
        ));
    }
    // System declarations may emit proof nodes, but have no public project location.
    Ok(None)
}

fn decode_path(text: &str) -> Option<String> {
    let mut bytes = Vec::with_capacity(text.len());
    let mut remaining = text.as_bytes();
    while let Some((&byte, rest)) = remaining.split_first() {
        if byte == b'%' {
            let hi = char::from(*rest.first()?).to_digit(16)?;
            let lo = char::from(*rest.get(1)?).to_digit(16)?;
            bytes.push(u8::try_from(hi * 16 + lo).ok()?);
            remaining = &rest[2..];
        } else {
            bytes.push(byte);
            remaining = rest;
        }
    }
    let decoded = String::from_utf8(bytes).ok()?;
    #[cfg(windows)]
    let decoded = if decoded.as_bytes().get(2) == Some(&b':') && decoded.starts_with('/') {
        decoded[1..].to_owned()
    } else {
        decoded
    };
    Some(decoded)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Issue {
    msg: Vec<String>,
    level: IssueLevel,
    range: Option<IssueRange>,
    number: Option<i32>,
    ctx: Vec<String>,
}

#[derive(Deserialize)]
enum IssueLevel {
    Error,
    NotImplemented,
    Warning,
    Info,
}

impl IssueLevel {
    fn severity(&self) -> DiagnosticSeverity {
        match self {
            Self::Error | Self::NotImplemented => DiagnosticSeverity::ERROR,
            Self::Warning => DiagnosticSeverity::WARNING,
            Self::Info => DiagnosticSeverity::INFORMATION,
        }
    }
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct IssueRange {
    #[serde(rename = "def")]
    definition: IssueSpan,
    #[serde(rename = "use")]
    usage: IssueSpan,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct IssueSpan {
    file_name: String,
    start_pos: IssuePosition,
    end_pos: IssuePosition,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct IssuePosition {
    line: u32,
    col: u32,
}

/// Parse F*'s per-stderr-line JSON issues; failed process output remains inspectable too.
pub fn fstar(
    snapshot: &Snapshot,
    metadata: &TranslationMetadata,
    stdout: &[u8],
    stderr: &[u8],
    status_uri: &str,
    success: bool,
) -> Diagnostics {
    let redactor = Redactor::new(snapshot);
    let mut diagnostics = Diagnostics::new();
    let mut unparsed = String::new();
    for line in String::from_utf8_lossy(stderr)
        .lines()
        .filter(|line| !line.trim().is_empty())
    {
        match serde_json::from_str::<Issue>(line) {
            Ok(mut issue) => {
                let owner = issue.range.as_ref().and_then(|range| {
                    [&range.usage, &range.definition]
                        .into_iter()
                        .find_map(|span| metadata.owners.get(basename(&span.file_name)))
                });
                if let Some(range) = &mut issue.range {
                    range.definition.file_name = basename(&range.definition.file_name).to_owned();
                    range.usage.file_name = basename(&range.usage.file_name).to_owned();
                }
                for context in &mut issue.ctx {
                    *context = redactor.text(context);
                }
                let (uri, range) = owner.map_or_else(
                    || (status_uri.to_owned(), Range::default()),
                    |(path, range)| (workspace::uri(path), *range),
                );
                let diagnostic = Diagnostic {
                    range,
                    severity: Some(issue.level.severity()),
                    code: issue.number.map(NumberOrString::Number),
                    source: Some("F*".to_owned()),
                    message: redactor.text(&issue.msg.join("\n")),
                    data: Some(serde_json::json!({ "range": issue.range, "ctx": issue.ctx })),
                    ..Diagnostic::default()
                };
                diagnostics.entry(uri).or_default().push(diagnostic);
            }
            Err(error) => {
                // Debug traces are not errors. An issue-shaped but malformed record is never success.
                let malformed = serde_json::from_str::<Value>(line)
                    .ok()
                    .is_some_and(|value| {
                        value.get("msg").is_some() || value.get("level").is_some()
                    });
                if malformed {
                    job_error(
                        &mut diagnostics,
                        status_uri,
                        redactor.text(&format!(
                            "F* emitted a malformed JSON issue ({error}): {line}"
                        )),
                    );
                } else if !success {
                    if !unparsed.is_empty() {
                        unparsed.push('\n');
                    }
                    unparsed.push_str(line);
                }
            }
        }
    }
    if !success {
        if !unparsed.is_empty() {
            job_error(
                &mut diagnostics,
                status_uri,
                format!("F* stderr:\n{}", redactor.text(&unparsed)),
            );
        }
        let stdout = String::from_utf8_lossy(stdout);
        if !stdout.trim().is_empty() {
            job_error(
                &mut diagnostics,
                status_uri,
                format!("F* stdout:\n{}", redactor.text(&stdout)),
            );
        }
        if !has_errors(&diagnostics) {
            job_error(
                &mut diagnostics,
                status_uri,
                "F* exited unsuccessfully without an error diagnostic".to_owned(),
            );
        }
    }
    diagnostics
}

fn job_error(diagnostics: &mut Diagnostics, status_uri: &str, message: String) {
    diagnostics
        .entry(status_uri.to_owned())
        .or_default()
        .push(Diagnostic {
            range: Range::default(),
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("F*".to_owned()),
            message,
            ..Diagnostic::default()
        });
}

pub fn has_errors(diagnostics: &Diagnostics) -> bool {
    diagnostics
        .values()
        .flatten()
        .any(|diagnostic| diagnostic.severity == Some(DiagnosticSeverity::ERROR))
}

pub fn merge(target: &mut Diagnostics, incoming: Diagnostics) {
    for (uri, entries) in incoming.0 {
        target.entry(uri).or_default().extend(entries);
    }
}

fn basename(path: &str) -> &str {
    path.rsplit(['/', '\\']).next().unwrap_or(path)
}

struct Redactor {
    replacements: Vec<(String, String)>,
}

impl Redactor {
    fn new(snapshot: &Snapshot) -> Self {
        let mut replacements = Vec::new();
        for (private, public) in [
            (snapshot.out(), String::new()),
            (snapshot.checked(), String::new()),
            (
                snapshot.mirror(),
                snapshot.root.to_string_lossy().into_owned(),
            ),
            (
                snapshot.storage.path().to_path_buf(),
                "<candidate>".to_owned(),
            ),
        ] {
            let raw = private.to_string_lossy().into_owned();
            let encoded = workspace::uri(&private);
            let public_uri = if private == snapshot.mirror() {
                workspace::uri(&snapshot.root)
            } else {
                public.clone()
            };
            for (from, to) in [(raw, public), (encoded, public_uri)] {
                if to.is_empty() {
                    replacements.push((format!("{from}/"), String::new()));
                    #[cfg(windows)]
                    replacements.push((format!("{from}\\"), String::new()));
                }
                replacements.push((from, to));
            }
        }
        replacements.sort_by_key(|(from, _)| std::cmp::Reverse(from.len()));
        Self { replacements }
    }

    fn text(&self, text: &str) -> String {
        let mut text = text.to_owned();
        for (from, to) in &self.replacements {
            if text.contains(from) {
                text = text.replace(from, to);
            }
        }
        text
    }

    fn value(&self, value: &mut Value) {
        match value {
            Value::String(text) => *text = self.text(text),
            Value::Array(items) => {
                for item in items {
                    self.value(item);
                }
            }
            Value::Object(fields) => {
                let old = std::mem::take(fields);
                for (key, mut value) in old {
                    self.value(&mut value);
                    fields.insert(self.text(&key), value);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::workspace::SourceFile;
    use super::*;
    use std::sync::Arc;

    #[test]
    fn metadata_uses_current_utf16_sources_and_fstar_owns_coarse_declarations() {
        let storage = Arc::new(tempfile::tempdir().unwrap());
        let project = tempfile::tempdir().unwrap();
        let root = project.path().to_path_buf();
        let path = root.join("unit.c");
        let code: Arc<str> = Arc::from("/* 𝄞 */ int answer(void) { return 0; }\n");
        let snapshot = Snapshot {
            storage,
            root,
            sources: vec![],
            files: BTreeMap::from([(
                path.clone(),
                SourceFile {
                    code: code.clone(),
                    disk: None,
                },
            )]),
            aliases: BTreeMap::new(),
            roots: vec![],
            includes: vec![],
            defines: vec![],
        };
        fs::create_dir(snapshot.out()).unwrap();
        fs::create_dir(snapshot.mirror()).unwrap();
        let private = snapshot.private(&path);
        fs::write(&private, &*code).unwrap();
        fs::write(
            snapshot.out().join("Func_answer.fst"),
            "module Func_answer\n",
        )
        .unwrap();
        let start = u32::try_from(code.find("answer").unwrap()).unwrap();
        let raw_range = Range::new(Position::new(0, start), Position::new(0, start + 5));
        fs::write(
            snapshot.out().join("diagnostics.json"),
            serde_json::to_vec(&BTreeMap::from([
                (
                    format!("file://{}", private.display()),
                    vec![Diagnostic {
                        range: raw_range,
                        severity: Some(DiagnosticSeverity::WARNING),
                        message: format!("warning at {}", private.display()),
                        ..Diagnostic::default()
                    }],
                ),
                (
                    "file:///<command line>".to_owned(),
                    vec![Diagnostic {
                        range: raw_range,
                        severity: Some(DiagnosticSeverity::WARNING),
                        message: "command-line macro warning".to_owned(),
                        ..Diagnostic::default()
                    }],
                ),
            ]))
            .unwrap(),
        )
        .unwrap();
        fs::write(snapshot.out().join("source_range_info.json"), serde_json::to_vec(&serde_json::json!({
            "sourceFiles": [{ "uri": format!("file://{}", private.display()), "modules": [{
                "fstFile": "Func_answer.fst", "declName": "answer", "sourceRange": raw_range,
                "mappings": [{ "source": raw_range.start, "pulse": { "line": 0, "character": 0 } }]
            }]}]
        })).unwrap()).unwrap();
        let metadata = translation(&snapshot, &SemanticIndex::default(), "pal://status").unwrap();
        let uri = workspace::uri(&path);
        let range = metadata.diagnostics[&uri][0].range;
        assert_eq!(range.start.character, start - 2);
        assert_eq!(range.end.character - range.start.character, 6);
        assert!(metadata.owners.contains_key("Func_answer.fsti"));
        assert_eq!(
            metadata.diagnostics["pal://status"][0].range,
            Range::default()
        );
        assert!(!has_errors(&metadata.diagnostics));
        let issue = serde_json::json!({
            "msg": ["proof failed", format!("at {}", snapshot.out().join("Func_answer.fsti").display())],
            "level": "Error", "number": 19, "ctx": ["checking answer"],
            "range": { "def": { "file_name": "Func_answer.fsti", "start_pos": { "line": 4, "col": 0 },
                "end_pos": { "line": 4, "col": 1 } }, "use": { "file_name": "Func_answer.fsti",
                "start_pos": { "line": 4, "col": 0 }, "end_pos": { "line": 4, "col": 1 } } }
        });
        let result = fstar(
            &snapshot,
            &metadata,
            b"",
            issue.to_string().as_bytes(),
            "pal://status",
            false,
        );
        assert!(has_errors(&result));
        assert_eq!(result[&uri][0].range, range);
        assert_eq!(result[&uri][0].code, Some(NumberOrString::Number(19)));
        assert!(
            !serde_json::to_string(&result)
                .unwrap()
                .contains(&snapshot.storage.path().to_string_lossy().to_string())
        );
        let result = fstar(
            &snapshot,
            &metadata,
            b"",
            b"solver crashed",
            "pal://status",
            false,
        );
        assert!(result["pal://status"][0].message.contains("solver crashed"));
        assert!(
            fstar(
                &snapshot,
                &metadata,
                b"debug",
                b"debug",
                "pal://status",
                true
            )
            .is_empty()
        );
        fs::remove_file(snapshot.out().join("source_range_info.json")).unwrap();
        assert_eq!(
            translation(&snapshot, &SemanticIndex::default(), "pal://status")
                .unwrap_err()
                .code,
            "translation_failed"
        );
    }
}
