//! Immutable candidate inputs shared by semantic indexing and PAL translation.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use lsp_types::{Position, Range};
use rmcp::schemars::{self, JsonSchema};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct FailureCode(String);

impl std::ops::Deref for FailureCode {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl PartialEq<&str> for FailureCode {
    fn eq(&self, other: &&str) -> bool {
        self.0 == *other
    }
}

impl fmt::Display for FailureCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Failure {
    pub code: FailureCode,
    pub message: String,
}

impl Failure {
    pub fn new(code: &str, message: impl Into<String>) -> Self {
        Self {
            code: FailureCode(code.to_owned()),
            message: message.into(),
        }
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for Failure {}

pub type Result<T> = std::result::Result<T, Failure>;

#[derive(Clone, Debug, Deserialize, JsonSchema)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum Change {
    Reference { path: String },
    Replace { path: String, code: String },
    Append { path: String, code: String },
}

impl Change {
    pub fn path(&self) -> &str {
        match self {
            Self::Reference { path } | Self::Replace { path, .. } | Self::Append { path, .. } => {
                path
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct ManagedSource {
    pub path: PathBuf,
    pub identity: PathBuf,
    pub code: Arc<str>,
    pub reference: bool,
    /// All explicitly submitted root-relative spellings, including earlier revisions.
    pub aliases: Vec<PathBuf>,
}

#[derive(Clone, Debug)]
pub struct Toolchain {
    pub clang: PathBuf,
    pub resource_dir: PathBuf,
}

impl Toolchain {
    pub fn discover() -> Result<Self> {
        let mut errors = Vec::new();
        let mut bindir = None;
        for executable in ["llvm-config-20", "llvm-config"] {
            match command_text(executable.as_ref(), &["--bindir"]) {
                Ok(directory) if !directory.is_empty() => {
                    bindir = Some(PathBuf::from(directory));
                    break;
                }
                Ok(_) => errors.push(format!("{executable} --bindir returned an empty path")),
                Err(error) => errors.push(error.message),
            }
        }
        let bindir =
            bindir.ok_or_else(|| Failure::new("toolchain_unavailable", errors.join("; ")))?;
        let clang =
            fs::canonicalize(bindir.join(if cfg!(windows) { "clang.exe" } else { "clang" }))
                .map_err(|error| {
                    Failure::new(
                        "toolchain_unavailable",
                        format!("cannot locate clang: {error}"),
                    )
                })?;
        path_text(&clang)?;
        let compiler_version = command_text(&clang, &["--version"])?;
        let compiler_major = version_major(&compiler_version)?;
        let resource_dir = fs::canonicalize(command_text(&clang, &["--print-resource-dir"])?)
            .map_err(|error| {
                Failure::new(
                    "toolchain_unavailable",
                    format!("cannot locate clang resources: {error}"),
                )
            })?;
        if !resource_dir.is_dir() {
            return Err(Failure::new(
                "toolchain_unavailable",
                "clang resource directory is not a directory",
            ));
        }
        path_text(&resource_dir)?;
        let _clang = clang_rs::Clang::new().map_err(|error| Failure::new(
            "toolchain_unavailable",
            format!("cannot load libclang: {error}; set LIBCLANG_PATH to the LLVM {compiler_major} library directory"),
        ))?;
        let library_version = clang_rs::get_version();
        let library_major = version_major(&library_version)?;
        if compiler_major < 20 || library_major < 20 || compiler_major != library_major {
            return Err(Failure::new(
                "toolchain_mismatch",
                format!(
                    "PAL requires matching clang/libclang major versions >=20; selected clang is {compiler_major}, libclang is {library_major}; set LIBCLANG_PATH to the selected LLVM library directory"
                ),
            ));
        }
        Ok(Self {
            clang,
            resource_dir,
        })
    }
}

fn command_text(executable: &Path, arguments: &[&str]) -> Result<String> {
    let output = Command::new(executable)
        .args(arguments)
        .output()
        .map_err(|error| {
            Failure::new(
                "toolchain_unavailable",
                format!("cannot run {}: {error}", executable.display()),
            )
        })?;
    if !output.status.success() {
        return Err(Failure::new(
            "toolchain_unavailable",
            format!(
                "{} {} failed: {}",
                executable.display(),
                arguments.join(" "),
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    String::from_utf8(output.stdout)
        .map(|text| text.trim().to_owned())
        .map_err(|error| {
            Failure::new(
                "toolchain_unavailable",
                format!(
                    "{} returned non-UTF-8 output: {error}",
                    executable.display()
                ),
            )
        })
}

fn version_major(version: &str) -> Result<u32> {
    version
        .split_once("version ")
        .map(|(_, tail)| tail)
        .and_then(|tail| tail.split('.').next())
        .and_then(|major| major.trim().parse().ok())
        .ok_or_else(|| {
            Failure::new(
                "toolchain_unavailable",
                format!("unrecognized clang version: {version}"),
            )
        })
}

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub code: Arc<str>,
    pub disk: Option<Arc<str>>,
}

impl SourceFile {
    /// Clang offsets are byte offsets; public positions count UTF-16 code units.
    pub fn position(&self, offset: usize) -> Position {
        let mut offset = offset.min(self.code.len());
        while !self.code.is_char_boundary(offset) {
            offset -= 1;
        }
        let mut line = 0u32;
        let mut start = 0;
        let mut end = self.code.len();
        while let Some((newline, next)) = self.line_break(start) {
            if next > offset {
                end = newline;
                break;
            }
            line = line.saturating_add(1);
            start = next;
        }
        let character = self.code[start..offset.min(end)].encode_utf16().count();
        Position::new(line, u32::try_from(character).unwrap_or(u32::MAX))
    }

    pub fn offset(&self, position: Position) -> Result<usize> {
        let (start, end) = self.line_bounds(position.line)?;
        let mut column = 0u32;
        for (byte, scalar) in self.code[start..end].char_indices() {
            if column == position.character {
                return Ok(start + byte);
            }
            column = column
                .checked_add(if scalar.len_utf16() == 2 { 2 } else { 1 })
                .ok_or_else(|| {
                    Failure::new(
                        "invalid_position",
                        "source line exceeds the LSP position limit",
                    )
                })?;
            if column > position.character {
                return Err(Failure::new(
                    "invalid_position",
                    "position splits a UTF-16 surrogate pair",
                ));
            }
        }
        if column == position.character {
            Ok(end)
        } else {
            Err(Failure::new(
                "invalid_position",
                "character is past the end of the source line",
            ))
        }
    }

    pub fn byte_position(&self, line: u32, column: u32) -> Result<usize> {
        let (start, end) = self.line_bounds(line)?;
        let offset = start
            .checked_add(column as usize)
            .filter(|offset| *offset <= end)
            .ok_or_else(|| {
                Failure::new(
                    "invalid_position",
                    "byte column is past the end of the source line",
                )
            })?;
        if !self.code.is_char_boundary(offset) {
            return Err(Failure::new(
                "invalid_position",
                "byte column splits a UTF-8 character",
            ));
        }
        Ok(offset)
    }

    pub fn range(&self, start: usize, end: usize) -> Range {
        Range::new(self.position(start), self.position(end))
    }

    fn line_bounds(&self, line: u32) -> Result<(usize, usize)> {
        let mut start = 0;
        for _ in 0..line {
            start = self
                .line_break(start)
                .map(|(_, next)| next)
                .ok_or_else(|| {
                    Failure::new("invalid_position", "line is past the end of the source")
                })?;
        }
        let end = self
            .line_break(start)
            .map_or(self.code.len(), |(newline, _)| newline);
        Ok((start, end))
    }

    fn line_break(&self, start: usize) -> Option<(usize, usize)> {
        let bytes = self.code.as_bytes();
        let newline = start
            + bytes[start..]
                .iter()
                .position(|byte| *byte == b'\r' || *byte == b'\n')?;
        let next = newline
            + if bytes[newline] == b'\r' && bytes.get(newline + 1) == Some(&b'\n') {
                2
            } else {
                1
            };
        Some((newline, next))
    }
}

#[derive(Debug)]
pub struct Snapshot {
    pub storage: Arc<tempfile::TempDir>,
    pub root: PathBuf,
    pub sources: Vec<ManagedSource>,
    pub files: BTreeMap<PathBuf, SourceFile>,
    pub aliases: BTreeMap<PathBuf, PathBuf>,
    pub roots: Vec<PathBuf>,
    pub includes: Vec<PathBuf>,
    pub defines: Vec<String>,
}

/// Validate the operation shape before reserving a job, without reading source bytes.
/// Resolution errors are deliberately deferred to candidate preparation.
pub fn validate_changes(root: &Path, sources: &[ManagedSource], changes: &[Change]) -> Result<()> {
    let mut targets = BTreeSet::new();
    let mut roots: BTreeSet<PathBuf> = sources
        .iter()
        .filter(|source| is_c(&source.path))
        .map(|source| source.identity.clone())
        .collect();
    for change in changes {
        let relative = input_path(change.path())?;
        let absolute = root.join(&relative);
        let known = sources.iter().find(|source| {
            source.path == relative
                || source.aliases.contains(&relative)
                || source.identity == absolute
        });
        let identity = known
            .map(|source| source.identity.clone())
            .or_else(|| fs::canonicalize(&absolute).ok())
            .or_else(|| resolve_inside(root, &absolute, false).ok())
            .unwrap_or(absolute);
        if !targets.insert(identity.clone()) {
            return Err(Failure::new(
                "conflicting_changes",
                format!("multiple changes target {}", relative.display()),
            ));
        }
        if matches!(change, Change::Append { .. })
            && known.is_none()
            && !sources.iter().any(|source| source.identity == identity)
        {
            return Err(Failure::new(
                "missing_file",
                format!(
                    "append requires an existing managed source: {}",
                    relative.display()
                ),
            ));
        }
        roots.remove(&identity);
        if is_c(&relative) {
            roots.insert(identity);
        }
    }
    if roots.is_empty() {
        return Err(Failure::new(
            "no_translation_units",
            "a session must contain at least one .c source",
        ));
    }
    Ok(())
}

pub fn prepare(
    root: PathBuf,
    mut sources: Vec<ManagedSource>,
    changes: Vec<Change>,
    includes: Vec<PathBuf>,
    defines: Vec<String>,
) -> Result<Snapshot> {
    validate_changes(&root, &sources, &changes)?;
    let root = fs::canonicalize(&root).map_err(|error| io_failure("invalid_path", &root, error))?;
    if !root.is_dir() {
        return Err(Failure::new(
            "invalid_path",
            "workspace root is not a directory",
        ));
    }
    path_text(&root)?;
    let mut changed_identities = BTreeSet::new();
    for change in changes {
        let relative = input_path(change.path())?;
        let absolute = root.join(&relative);
        let identity =
            resolve_inside(&root, &absolute, matches!(change, Change::Reference { .. }))?;
        if !changed_identities.insert(identity.clone()) {
            return Err(Failure::new(
                "conflicting_changes",
                format!("changes alias the same file: {}", relative.display()),
            ));
        }
        let existing = sources.iter().position(|source| {
            source.path == relative
                || source.aliases.contains(&relative)
                || source.identity == identity
        });
        let (code, reference) = match change {
            Change::Reference { .. } => (Arc::from(""), true),
            Change::Replace { code, .. } => (Arc::from(code), false),
            Change::Append { code, .. } => {
                let index = existing.ok_or_else(|| {
                    Failure::new("missing_file", "append requires an existing managed source")
                })?;
                let mut combined = String::with_capacity(sources[index].code.len() + code.len());
                combined.push_str(&sources[index].code);
                combined.push_str(&code);
                (Arc::from(combined), false)
            }
        };
        if let Some(index) = existing {
            let new_root = !is_c(&sources[index].path) && is_c(&relative);
            let source = &mut sources[index];
            if !source.aliases.contains(&relative) {
                source.aliases.push(relative.clone());
            }
            source.path = relative;
            source.identity = identity;
            source.code = code;
            source.reference = reference;
            if new_root {
                let source = sources.remove(index);
                sources.push(source);
            }
        } else {
            sources.push(ManagedSource {
                path: relative.clone(),
                identity,
                code,
                reference,
                aliases: vec![relative],
            });
        }
    }
    let mut identities = BTreeSet::new();
    for source in &mut sources {
        source.identity = resolve_inside(&root, &root.join(&source.path), source.reference)?;
        if !identities.insert(source.identity.clone()) {
            return Err(Failure::new(
                "conflicting_changes",
                format!(
                    "managed paths alias the same file: {}",
                    source.path.display()
                ),
            ));
        }
        if source.reference {
            source.code = read_source(&source.identity)?;
        }
        if !source.aliases.contains(&source.path) {
            source.aliases.push(source.path.clone());
        }
        for alias in &source.aliases {
            let resolved = resolve_inside(&root, &root.join(alias), false)?;
            if resolved != source.identity {
                return Err(Failure::new(
                    "inputs_changed",
                    format!("managed alias changed identity: {}", alias.display()),
                ));
            }
        }
    }
    if !sources.iter().any(|source| is_c(&source.path)) {
        return Err(Failure::new(
            "no_translation_units",
            "a session must contain at least one .c source",
        ));
    }
    let includes = includes
        .into_iter()
        .map(|path| {
            let path = if path.is_absolute() {
                path
            } else {
                root.join(path)
            };
            path_text(&path)?;
            Ok(path)
        })
        .collect::<Result<Vec<_>>>()?;
    if defines.iter().any(|define| define.contains('\0')) {
        return Err(Failure::new(
            "invalid_path",
            "preprocessor definitions cannot contain NUL",
        ));
    }
    let temporary_parent = fs::canonicalize(std::env::temp_dir()).map_err(|error| {
        Failure::new(
            "snapshot_failed",
            format!("cannot resolve temporary directory: {error}"),
        )
    })?;
    let storage = Arc::new(tempfile::tempdir_in(temporary_parent).map_err(|error| {
        Failure::new(
            "snapshot_failed",
            format!("cannot create candidate directory: {error}"),
        )
    })?);
    let mut snapshot = Snapshot {
        storage,
        root,
        sources,
        files: BTreeMap::new(),
        aliases: BTreeMap::new(),
        roots: Vec::new(),
        includes,
        defines,
    };
    for directory in [snapshot.mirror(), snapshot.out(), snapshot.checked()] {
        fs::create_dir_all(&directory)
            .map_err(|error| io_failure("snapshot_failed", &directory, error))?;
    }
    snapshot.mirror_symlinks()?;
    for index in 0..snapshot.sources.len() {
        let source = &snapshot.sources[index];
        let identity = source.identity.clone();
        let code = Arc::clone(&source.code);
        let disk = source.reference.then(|| Arc::clone(&code));
        let path = source.path.clone();
        let aliases = source.aliases.clone();
        snapshot
            .files
            .insert(identity.clone(), SourceFile { code, disk });
        snapshot.add_alias(&identity, &identity)?;
        for alias in aliases {
            snapshot.add_alias(&snapshot.root.join(alias), &identity)?;
        }
        snapshot.materialize(&identity)?;
        if is_c(&path) {
            snapshot.roots.push(snapshot.mirror().join(path));
        }
    }
    snapshot.write_overlay()?;
    snapshot.recheck_inputs()?;
    Ok(snapshot)
}

impl Snapshot {
    pub fn mirror(&self) -> PathBuf {
        self.storage.path().join("mirror")
    }
    pub fn out(&self) -> PathBuf {
        self.storage.path().join("out")
    }
    pub fn checked(&self) -> PathBuf {
        self.storage.path().join("checked")
    }
    pub fn overlay(&self) -> PathBuf {
        self.storage.path().join("overlay.json")
    }
    fn fallback_overlay(&self) -> PathBuf {
        self.storage.path().join("fallback.json")
    }

    /// Also resolves unseen included project headers before their first capture.
    pub fn original(&self, path: &Path) -> Option<PathBuf> {
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.root.join(path)
        };
        if let Some(identity) = self.aliases.get(&path) {
            return Some(identity.clone());
        }
        let original = if let Ok(relative) = path.strip_prefix(self.mirror()) {
            self.root.join(relative)
        } else {
            path
        };
        if let Some(identity) = self.aliases.get(&original) {
            return Some(identity.clone());
        }
        let identity = fs::canonicalize(&original).ok().or_else(|| {
            original
                .starts_with(&self.root)
                .then(|| resolve_inside(&self.root, &original, false).ok())
                .flatten()
        })?;
        identity.starts_with(&self.root).then_some(identity)
    }

    pub fn private(&self, original: &Path) -> PathBuf {
        let identity = self
            .original(original)
            .unwrap_or_else(|| original.to_path_buf());
        match identity.strip_prefix(&self.root) {
            Ok(relative) => self.mirror().join(relative),
            Err(_) => identity,
        }
    }

    pub fn capture(&mut self, observed: &Path, code: Arc<str>) -> Result<()> {
        let Some(identity) = self.original(observed) else {
            return Ok(());
        };
        if let Some(file) = self.files.get(&identity) {
            if file.code != code {
                return Err(Failure::new(
                    "inputs_changed",
                    format!(
                        "loaded contents changed between translation units: {}",
                        identity.display()
                    ),
                ));
            }
        } else {
            let disk = read_source(&identity)
                .map_err(|error| Failure::new("inputs_changed", error.message))?;
            if disk != code {
                return Err(Failure::new(
                    "inputs_changed",
                    format!(
                        "included file changed while being captured: {}",
                        identity.display()
                    ),
                ));
            }
            self.files.insert(
                identity.clone(),
                SourceFile {
                    disk: Some(Arc::clone(&code)),
                    code,
                },
            );
        }
        self.add_alias(&identity, &identity)?;
        let observed = if observed.is_absolute() {
            observed.to_path_buf()
        } else {
            self.root.join(observed)
        };
        self.add_alias(&observed, &identity)?;
        self.materialize(&identity)
    }

    pub fn write_overlay(&self) -> Result<()> {
        let mirror = self.mirror();
        // Keep unseen nested includes relative to their original directories. The lower
        // overlay prefers frozen mirror files and falls back only for not-yet-captured paths.
        write_json(
            &self.fallback_overlay(),
            &json!({
                "version": 0,
                "use-external-names": false,
                "redirecting-with": "fallback",
                "roots": [{ "type": "directory-remap", "name": mirror, "external-contents": self.root }],
            }),
        )?;
        let mut tree = OverlayDirectory::default();
        for (alias, identity) in &self.aliases {
            if alias.starts_with(&mirror) {
                continue;
            }
            tree.insert(alias, self.private(identity))?;
        }
        let overlay = json!({
            "version": 0,
            "case-sensitive": cfg!(not(windows)),
            "use-external-names": false,
            "roots": tree.roots(),
        });
        write_json(&self.overlay(), &overlay)
    }

    pub fn recheck_inputs(&self) -> Result<()> {
        for (identity, file) in &self.files {
            if let Some(expected) = &file.disk {
                let actual = read_source(identity)
                    .map_err(|error| Failure::new("inputs_changed", error.message))?;
                if &actual != expected {
                    return Err(Failure::new(
                        "inputs_changed",
                        format!("captured input changed: {}", identity.display()),
                    ));
                }
            }
        }
        let mirror = self.mirror();
        for (alias, identity) in &self.aliases {
            if alias.starts_with(&mirror)
                || self
                    .files
                    .get(identity)
                    .is_none_or(|file| file.disk.is_none())
            {
                continue;
            }
            let current = fs::canonicalize(alias).map_err(|error| {
                Failure::new(
                    "inputs_changed",
                    format!("captured alias changed: {}: {error}", alias.display()),
                )
            })?;
            if &current != identity {
                return Err(Failure::new(
                    "inputs_changed",
                    format!("captured alias changed identity: {}", alias.display()),
                ));
            }
        }
        Ok(())
    }

    /// Only project flags: PAL adds its mandatory compiler flags itself.
    pub fn project_args(&self, private_c: &Path) -> Vec<String> {
        let original = self
            .sources
            .iter()
            .find(|source| self.mirror().join(&source.path) == private_c)
            .map(|source| self.root.join(&source.path))
            .or_else(|| self.original(private_c))
            .unwrap_or_else(|| self.root.clone());
        let mut arguments = vec![
            "-iquote".into(),
            original
                .parent()
                .unwrap_or(&self.root)
                .to_string_lossy()
                .into_owned(),
        ];
        arguments.extend(
            self.includes
                .iter()
                .map(|include| format!("-I{}", include.display())),
        );
        arguments.extend(self.defines.iter().map(|define| format!("-D{define}")));
        arguments.extend([
            "-ivfsoverlay".into(),
            self.fallback_overlay().to_string_lossy().into_owned(),
            "-ivfsoverlay".into(),
            self.overlay().to_string_lossy().into_owned(),
            format!(
                "-ffile-prefix-map={}={}",
                self.mirror().display(),
                self.root.display()
            ),
        ]);
        arguments
    }

    pub fn parser_args(&self, private_c: &Path, toolchain: &Toolchain) -> Vec<String> {
        let mut arguments = vec![
            "-DC2PULSE".into(),
            "-fno-builtin".into(),
            "-D_FORTIFY_SOURCE=0".into(),
            "-resource-dir".into(),
            toolchain.resource_dir.to_string_lossy().into_owned(),
            "-Wno-unused-but-set-variable".into(),
            "-Wno-unused-variable".into(),
        ];
        arguments.extend(self.project_args(private_c));
        arguments.push(format!("-working-directory={}", self.root.display()));
        arguments
    }

    pub fn write_database(&self, toolchain: &Toolchain) -> Result<()> {
        let commands: Vec<Value> = self
            .roots
            .iter()
            .map(|source| {
                let mut arguments = vec![toolchain.clang.to_string_lossy().into_owned()];
                arguments.extend(self.project_args(source));
                arguments.push(source.to_string_lossy().into_owned());
                json!({ "directory": self.root, "file": source, "arguments": arguments })
            })
            .collect();
        write_json(
            &self.storage.path().join("compile_commands.json"),
            &commands,
        )
    }

    fn add_alias(&mut self, alias: &Path, identity: &Path) -> Result<()> {
        let alias = alias.to_path_buf();
        path_text(&alias)?;
        if let Some(previous) = self.aliases.get(&alias) {
            if previous != identity {
                return Err(Failure::new(
                    "conflicting_changes",
                    format!("alias names different captured files: {}", alias.display()),
                ));
            }
        } else {
            self.aliases.insert(alias.clone(), identity.to_path_buf());
        }
        if let Ok(relative) = alias.strip_prefix(self.mirror()) {
            return self.add_alias(&self.root.join(relative), identity);
        }
        if let Ok(relative) = alias.strip_prefix(&self.root) {
            let private = self.mirror().join(relative);
            if let Some(previous) = self.aliases.insert(private.clone(), identity.to_path_buf())
                && previous != identity
            {
                return Err(Failure::new(
                    "conflicting_changes",
                    format!(
                        "private alias names different captured files: {}",
                        private.display()
                    ),
                ));
            }
        }
        Ok(())
    }

    fn mirror_symlinks(&self) -> Result<()> {
        // ponytail: scan project symlinks per candidate; add an indexed watcher only if traversal becomes measurable.
        let mut directories = vec![self.root.clone()];
        while let Some(directory) = directories.pop() {
            // Unreadable unrelated directories cannot supply compiler inputs either.
            let Ok(entries) = fs::read_dir(&directory) else {
                continue;
            };
            for entry in entries.flatten() {
                if entry.path().starts_with(self.storage.path()) {
                    continue;
                }
                let Ok(kind) = entry.file_type() else {
                    continue;
                };
                if kind.is_dir() {
                    directories.push(entry.path());
                    continue;
                }
                if !kind.is_symlink() {
                    continue;
                }
                let Ok(target) = fs::canonicalize(entry.path()) else {
                    continue;
                };
                let Ok(relative_target) = target.strip_prefix(&self.root) else {
                    continue;
                };
                let target_private = self.mirror().join(relative_target);
                let alias = self
                    .mirror()
                    .join(entry.path().strip_prefix(&self.root).map_err(|_| {
                        Failure::new("snapshot_failed", "symlink lookup left the workspace")
                    })?);
                if let Some(parent) = alias.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|error| io_failure("snapshot_failed", parent, error))?;
                }
                if target.is_dir() {
                    fs::create_dir_all(&target_private)
                        .map_err(|error| io_failure("snapshot_failed", &target_private, error))?;
                } else if let Some(parent) = target_private.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|error| io_failure("snapshot_failed", parent, error))?;
                }
                #[cfg(unix)]
                let linked = std::os::unix::fs::symlink(&target_private, &alias);
                #[cfg(windows)]
                let linked = if target.is_dir() {
                    std::os::windows::fs::symlink_dir(&target_private, &alias)
                } else {
                    std::os::windows::fs::symlink_file(&target_private, &alias)
                };
                linked.map_err(|error| io_failure("snapshot_failed", &alias, error))?;
            }
        }
        Ok(())
    }

    fn materialize(&self, identity: &Path) -> Result<()> {
        let file = self
            .files
            .get(identity)
            .ok_or_else(|| Failure::new("snapshot_failed", "missing captured source buffer"))?;
        let canonical = self.private(identity);
        if !canonical.exists() {
            write_source(&canonical, &file.code)?;
        }
        let mirror = self.mirror();
        for (alias, target) in &self.aliases {
            if target != identity || !alias.starts_with(&mirror) || alias == &canonical {
                continue;
            }
            if alias
                .components()
                .any(|component| component == Component::ParentDir)
            {
                continue;
            }
            if let Some(parent) = alias.parent() {
                fs::create_dir_all(parent)
                    .map_err(|error| io_failure("snapshot_failed", parent, error))?;
            }
            if !alias.exists() && fs::hard_link(&canonical, alias).is_err() {
                fs::copy(&canonical, alias)
                    .map_err(|error| io_failure("snapshot_failed", alias, error))?;
            }
        }
        Ok(())
    }
}

fn input_path(path: &str) -> Result<PathBuf> {
    if path.is_empty()
        || path.contains('\0')
        || path
            .split('/')
            .next()
            .is_some_and(|part| part.contains(':'))
    {
        return Err(Failure::new(
            "invalid_path",
            "expected a workspace-relative .c or .h filesystem path",
        ));
    }
    let path = Path::new(path);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::Prefix(_) | Component::RootDir
            )
        })
    {
        return Err(Failure::new(
            "invalid_path",
            "absolute paths and '..' components are not allowed",
        ));
    }
    let path = normalize(path);
    if !matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("c" | "h")
    ) {
        return Err(Failure::new(
            "invalid_path",
            "managed sources must have a .c or .h extension",
        ));
    }
    Ok(path)
}

fn is_c(path: &Path) -> bool {
    path.extension().is_some_and(|extension| extension == "c")
}

/// Resolve every existing ancestor, including symlinks, without creating user files.
fn resolve_inside(root: &Path, path: &Path, required: bool) -> Result<PathBuf> {
    let mut existing = path.to_path_buf();
    let mut suffix = Vec::new();
    let canonical = loop {
        match fs::symlink_metadata(&existing) {
            Ok(metadata) => {
                if !suffix.is_empty() && !metadata.is_dir() && !metadata.file_type().is_symlink() {
                    return Err(Failure::new(
                        "invalid_path",
                        format!("path ancestor is not a directory: {}", existing.display()),
                    ));
                }
                break match fs::canonicalize(&existing) {
                    Ok(canonical) => canonical,
                    Err(error)
                        if error.kind() == std::io::ErrorKind::NotFound
                            && metadata.file_type().is_symlink() =>
                    {
                        let target = fs::read_link(&existing)
                            .map_err(|error| io_failure("invalid_path", &existing, error))?;
                        let target = if target.is_absolute() {
                            target
                        } else {
                            existing.parent().unwrap_or(root).join(target)
                        };
                        resolve_inside(root, &target, required)?
                    }
                    Err(error) => return Err(io_failure("invalid_path", &existing, error)),
                };
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                let name = existing
                    .file_name()
                    .ok_or_else(|| Failure::new("invalid_path", "cannot resolve source path"))?
                    .to_owned();
                suffix.push(name);
                if !existing.pop() {
                    return Err(Failure::new(
                        "invalid_path",
                        "cannot resolve source ancestor",
                    ));
                }
            }
            Err(error) => {
                return Err(io_failure(
                    if error.kind() == std::io::ErrorKind::NotFound {
                        "missing_file"
                    } else {
                        "invalid_path"
                    },
                    &existing,
                    error,
                ));
            }
        }
    };
    if !canonical.starts_with(root) {
        return Err(Failure::new(
            "invalid_path",
            format!("source escapes the workspace root: {}", path.display()),
        ));
    }
    if !suffix.is_empty() && !canonical.is_dir() {
        return Err(Failure::new(
            "invalid_path",
            format!("path ancestor is not a directory: {}", canonical.display()),
        ));
    }
    if required && !suffix.is_empty() {
        return Err(Failure::new(
            "missing_file",
            format!("referenced input does not exist: {}", path.display()),
        ));
    }
    let mut canonical = canonical;
    for component in suffix.into_iter().rev() {
        canonical.push(component);
    }
    path_text(&canonical)?;
    if canonical.exists() && !canonical.is_file() {
        return Err(Failure::new(
            "invalid_path",
            format!("source is not a regular file: {}", canonical.display()),
        ));
    }
    Ok(canonical)
}

fn read_source(path: &Path) -> Result<Arc<str>> {
    let metadata = fs::metadata(path).map_err(|error| {
        io_failure(
            if error.kind() == std::io::ErrorKind::NotFound {
                "missing_file"
            } else {
                "invalid_path"
            },
            path,
            error,
        )
    })?;
    if !metadata.is_file() {
        return Err(Failure::new(
            "invalid_path",
            format!("source is not a regular file: {}", path.display()),
        ));
    }
    fs::read_to_string(path).map(Arc::from).map_err(|error| {
        io_failure(
            if error.kind() == std::io::ErrorKind::NotFound {
                "missing_file"
            } else {
                "snapshot_failed"
            },
            path,
            error,
        )
    })
}

fn path_text(path: &Path) -> Result<&str> {
    path.to_str()
        .filter(|text| !text.contains('\0'))
        .ok_or_else(|| {
            Failure::new(
                "invalid_path",
                format!("path is not representable as UTF-8: {}", path.display()),
            )
        })
}

fn io_failure(code: &str, path: &Path, error: std::io::Error) -> Failure {
    Failure::new(code, format!("{}: {error}", path.display()))
}

fn write_source(path: &Path, code: &str) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| io_failure("snapshot_failed", parent, error))?;
    }
    fs::write(path, code).map_err(|error| io_failure("snapshot_failed", path, error))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<()> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| Failure::new("snapshot_failed", error.to_string()))?;
    fs::write(path, bytes).map_err(|error| io_failure("snapshot_failed", path, error))
}

fn normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            component => normalized.push(component.as_os_str()),
        }
    }
    normalized
}

#[derive(Default)]
struct OverlayDirectory {
    directories: BTreeMap<String, OverlayDirectory>,
    files: BTreeMap<String, PathBuf>,
}

impl OverlayDirectory {
    fn insert(&mut self, path: &Path, target: PathBuf) -> Result<()> {
        let mut components: Vec<String> = path
            .components()
            .map(|component| {
                component
                    .as_os_str()
                    .to_str()
                    .map(str::to_owned)
                    .ok_or_else(|| Failure::new("invalid_path", "overlay path is not UTF-8"))
            })
            .collect::<Result<_>>()?;
        let name = components
            .pop()
            .ok_or_else(|| Failure::new("invalid_path", "overlay path is empty"))?;
        let mut directory = self;
        for component in components {
            if directory.files.contains_key(&component) {
                return Err(Failure::new(
                    "conflicting_changes",
                    "overlay file is also used as a directory",
                ));
            }
            directory = directory.directories.entry(component).or_default();
        }
        if directory.directories.contains_key(&name) {
            return Err(Failure::new(
                "conflicting_changes",
                "overlay directory is also used as a file",
            ));
        }
        directory.files.insert(name, target);
        Ok(())
    }

    fn roots(&self) -> Vec<Value> {
        let mut values: Vec<Value> = self.directories.iter().map(|(name, directory)| {
            json!({ "type": "directory", "name": name, "contents": directory.roots() })
        }).collect();
        values.extend(self.files.iter().map(
            |(name, target)| json!({ "type": "file", "name": name, "external-contents": target }),
        ));
        values
    }
}

/// Canonical project paths only; encode path bytes rather than emitting temporary names.
pub fn uri(path: &Path) -> String {
    let text = path.to_string_lossy();
    let text = if cfg!(windows) {
        text.replace('\\', "/")
    } else {
        text.into_owned()
    };
    let mut uri = String::with_capacity(text.len() + 7);
    uri.push_str(if text.starts_with('/') {
        "file://"
    } else {
        "file:///"
    });
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    for byte in text.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~' | b'/') {
            uri.push(char::from(byte));
        } else {
            uri.push('%');
            uri.push(char::from(HEX[usize::from(byte >> 4)]));
            uri.push(char::from(HEX[usize::from(byte & 15)]));
        }
    }
    uri
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frozen_inputs_paths_and_utf16() {
        let directory = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(directory.path()).unwrap();
        fs::write(root.join("ref.h"), "#define VALUE 1\n").unwrap();
        let snapshot = prepare(
            root.clone(),
            vec![],
            vec![
                Change::Replace {
                    path: "new/main.c".into(),
                    code: "int x; /* 𝄞 */ int y;\n".into(),
                },
                Change::Reference {
                    path: "ref.h".into(),
                },
            ],
            vec![],
            vec![],
        )
        .unwrap();
        let file = &snapshot.files[&root.join("new/main.c")];
        let scalar = file.code.find('𝄞').unwrap();
        assert_eq!(file.offset(file.position(scalar)).unwrap(), scalar);
        assert!(
            file.offset(Position::new(0, file.position(scalar).character + 1))
                .is_err()
        );
        assert!(file.offset(Position::new(3, 0)).is_err());
        let lines = SourceFile {
            code: Arc::from("a\r\nb\rc\n"),
            disk: None,
        };
        assert_eq!(lines.offset(Position::new(2, 1)).unwrap(), 6);
        assert_eq!(lines.position(5), Position::new(2, 0));
        assert_eq!(lines.offset(Position::new(3, 0)).unwrap(), 7);
        assert!(!root.join("new/main.c").exists());
        let appended = prepare(
            root.clone(),
            snapshot.sources.clone(),
            vec![Change::Append {
                path: "new/main.c".into(),
                code: "int z;".into(),
            }],
            vec![],
            vec![],
        )
        .unwrap();
        assert_eq!(
            appended.sources[0].code.as_ref(),
            "int x; /* 𝄞 */ int y;\nint z;"
        );
        assert!(
            validate_changes(
                &root,
                &snapshot.sources,
                &[
                    Change::Replace {
                        path: "new/main.c".into(),
                        code: "".into()
                    },
                    Change::Replace {
                        path: "./new/main.c".into(),
                        code: "".into()
                    },
                ]
            )
            .is_err()
        );
        fs::write(root.join("ref.h"), "#define VALUE 2\n").unwrap();
        assert_eq!(
            snapshot.recheck_inputs().unwrap_err().code,
            "inputs_changed"
        );
        for path in [
            "../bad.c",
            "/bad.c",
            "https://host/file.c",
            "bad.txt",
            "bad\0.c",
        ] {
            assert_eq!(input_path(path).unwrap_err().code, "invalid_path");
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            symlink(root.join("ref.h"), root.join("alias.h")).unwrap();
            assert_eq!(
                validate_changes(
                    &root,
                    &snapshot.sources,
                    &[
                        Change::Reference {
                            path: "ref.h".into()
                        },
                        Change::Reference {
                            path: "alias.h".into()
                        },
                    ]
                )
                .unwrap_err()
                .code,
                "conflicting_changes"
            );
            let outside = tempfile::tempdir().unwrap();
            symlink(outside.path(), root.join("escape")).unwrap();
            assert_eq!(
                resolve_inside(&root, &root.join("escape/missing.c"), true)
                    .unwrap_err()
                    .code,
                "invalid_path"
            );
        }
        assert_eq!(
            uri(&root.join("space #𝄞.c")),
            format!("{}/space%20%23%F0%9D%84%9E.c", uri(&root))
        );
    }
}
