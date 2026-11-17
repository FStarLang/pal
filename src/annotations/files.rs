use super::{
    Overlay, Result, discover_macros_mode, extract_source_selected,
    preservation::validate_application, render_source,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::{Component, Path, PathBuf},
};
use tempfile::NamedTempFile;

struct Change {
    path: PathBuf,
    original: String,
    updated: String,
}

fn read(path: &Path) -> Result<String> {
    fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))
}

fn resolve(root: &Path, path: &Path) -> Result<PathBuf> {
    let resolved =
        fs::canonicalize(path).map_err(|error| format!("{}: {error}", path.display()))?;
    if !resolved.starts_with(root) {
        return Err(format!(
            "{} resolves outside root {}",
            path.display(),
            root.display()
        ));
    }
    if !resolved.is_file() {
        return Err(format!("{} is not a regular file", path.display()));
    }
    Ok(resolved)
}

fn stage(path: &Path, contents: &str) -> Result<NamedTempFile> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let mut temporary = NamedTempFile::new_in(parent).map_err(|error| error.to_string())?;
    temporary
        .write_all(contents.as_bytes())
        .map_err(|error| error.to_string())?;
    temporary
        .as_file()
        .sync_all()
        .map_err(|error| error.to_string())?;
    if path.exists() {
        let permissions = fs::metadata(path)
            .map_err(|error| error.to_string())?
            .permissions();
        temporary
            .as_file()
            .set_permissions(permissions)
            .map_err(|error| error.to_string())?;
    }
    Ok(temporary)
}

fn commit(changes: &[Change]) -> Result<()> {
    let mut staged = Vec::new();
    for change in changes {
        if read(&change.path)? != change.original {
            return Err(format!(
                "{} changed during the operation",
                change.path.display()
            ));
        }
        staged.push((
            stage(&change.path, &change.updated)?,
            stage(&change.path, &change.original)?,
        ));
    }
    let mut committed: Vec<(&Change, NamedTempFile)> = Vec::new();
    for (change, (updated, backup)) in changes.iter().zip(staged) {
        let result = read(&change.path).and_then(|current| {
            if current != change.original {
                Err(format!(
                    "{} changed during the operation",
                    change.path.display()
                ))
            } else {
                updated
                    .persist(&change.path)
                    .map(|_| ())
                    .map_err(|error| error.to_string())
            }
        });
        if let Err(mut error) = result {
            for (previous, backup) in committed.into_iter().rev() {
                if read(&previous.path).is_ok_and(|contents| contents == previous.updated) {
                    if let Err(failure) = backup.persist(&previous.path) {
                        let recovery = failure.file.keep().map_err(|error| error.to_string())?.1;
                        error.push_str(&format!(
                            "; rollback failed, original saved at {}",
                            recovery.display()
                        ));
                    }
                } else {
                    let recovery = backup.keep().map_err(|error| error.to_string())?.1;
                    error.push_str(&format!(
                        "; source changed, original saved at {}",
                        recovery.display()
                    ));
                }
            }
            return Err(error);
        }
        committed.push((change, backup));
    }
    Ok(())
}

fn include_graph(
    sources: &BTreeMap<PathBuf, &str>,
    include_dirs: &[PathBuf],
) -> Result<BTreeMap<PathBuf, Vec<PathBuf>>> {
    let mut graph = BTreeMap::new();
    for (path, source) in sources {
        let lexed = super::lex::lex(source)?;
        let mut includes = Vec::new();
        for directive in &lexed.directives {
            let tokens = &lexed.tokens[directive.tokens.clone()];
            if tokens.get(1).map(|token| token.text.as_str()) != Some("include") {
                continue;
            }
            let quoted = tokens.get(2).and_then(|token| {
                token
                    .text
                    .strip_prefix('"')
                    .and_then(|text| text.strip_suffix('"'))
            });
            let angled = if tokens.get(2).is_some_and(|token| token.text == "<") {
                tokens
                    .iter()
                    .skip(3)
                    .position(|token| token.text == ">")
                    .map(|end| {
                        tokens[3..3 + end]
                            .iter()
                            .map(|token| token.text.as_str())
                            .collect::<String>()
                    })
            } else {
                None
            };
            if let Some(header) = quoted.or(angled.as_deref()) {
                let mut directories = Vec::new();
                if quoted.is_some() {
                    directories.push(path.parent().ok_or("source has no parent")?.to_owned());
                }
                directories.extend_from_slice(include_dirs);
                for directory in directories {
                    if let Ok(resolved) = fs::canonicalize(directory.join(header)) {
                        // A shadowing but unlisted header must not import
                        // aliases from a later search directory.
                        if sources.contains_key(&resolved) {
                            includes.push(resolved);
                        }
                        break;
                    }
                }
            }
        }
        graph.insert(path.clone(), includes);
    }
    Ok(graph)
}

fn context<'a>(
    path: &Path,
    sources: &BTreeMap<PathBuf, &'a str>,
    graph: &BTreeMap<PathBuf, Vec<PathBuf>>,
) -> Vec<&'a str> {
    let mut pending = vec![path.to_owned()];
    let mut visited = BTreeSet::new();
    let mut context = Vec::new();
    while let Some(path) = pending.pop() {
        if visited.insert(path.clone()) {
            context.push(sources[&path]);
            pending.extend(graph[&path].iter().cloned());
        }
    }
    context
}

fn include_directories(root: &Path, inputs: &[String]) -> Result<Vec<PathBuf>> {
    inputs
        .iter()
        .map(|input| {
            let path = Path::new(input);
            if path.is_absolute()
                || path
                    .components()
                    .any(|part| !matches!(part, Component::Normal(_) | Component::CurDir))
            {
                return Err(format!("invalid include directory: {input}"));
            }
            let directory = fs::canonicalize(root.join(path)).map_err(|error| error.to_string())?;
            if !directory.starts_with(root) || !directory.is_dir() {
                return Err(format!(
                    "include directory outside root or not a directory: {input}"
                ));
            }
            Ok(directory)
        })
        .collect()
}

pub fn extract_files(
    root: &Path,
    inputs: &[PathBuf],
    output: &Path,
    proofs_only: bool,
    include_dirs: &[PathBuf],
) -> Result<String> {
    let root = fs::canonicalize(root).map_err(|error| error.to_string())?;
    let mut sources = BTreeMap::new();
    if output.symlink_metadata().is_ok() {
        return Err(format!(
            "{} already exists; refusing to overwrite",
            output.display()
        ));
    }
    for input in inputs {
        let path = resolve(&root, &root.join(input))?;
        let relative = path
            .strip_prefix(&root)
            .map_err(|error| error.to_string())?;
        let relative = relative
            .iter()
            .map(|component| component.to_str().ok_or("source path is not UTF-8"))
            .collect::<std::result::Result<Vec<_>, _>>()?
            .join("/");
        let contents = read(&path)?;
        sources.insert(relative, (path, contents));
    }
    let source_index: BTreeMap<_, _> = sources
        .values()
        .map(|(path, source)| (path.clone(), source.as_str()))
        .collect();
    let include_dirs = include_dirs
        .iter()
        .map(|path| {
            path.to_str()
                .map(str::to_owned)
                .ok_or("include directory is not UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>>>()?;
    let directories = include_directories(&root, &include_dirs)?;
    let graph = include_graph(&source_index, &directories)?;
    let mut overlay = Overlay {
        format_version: 1,
        include_dirs,
        files: Vec::new(),
    };
    let mut changes = Vec::new();
    for (relative, (path, original)) in &sources {
        let macros = discover_macros_mode(&context(path, &source_index, &graph), proofs_only)
            .map_err(|error| format!("{relative}: {error}"))?;
        let (file, updated) =
            extract_source_selected(relative.clone(), original, &macros, true, proofs_only)
                .map_err(|error| format!("{relative}: {error}"))?;
        overlay.files.push(file);
        if original != &updated {
            changes.push(Change {
                path: path.clone(),
                original: original.clone(),
                updated,
            });
        }
    }
    let serialized = toml::to_string_pretty(&overlay).map_err(|error| error.to_string())?;
    // The durable overlay is installed first, so interrupted extraction never
    // leaves stripped sources without their annotations.
    stage(output, &serialized)?
        .persist_noclobber(output)
        .map_err(|error| error.to_string())?;
    commit(&changes)?;
    let count: usize = overlay
        .files
        .iter()
        .map(|file| file.annotations.len())
        .sum();
    Ok(format!(
        "Extracted {count} annotations from {} distinct files into {}",
        overlay.files.len(),
        output.display()
    ))
}

pub fn apply_files(root: &Path, input: &Path, check: bool) -> Result<String> {
    let root = fs::canonicalize(root).map_err(|error| error.to_string())?;
    let overlay: Overlay = toml::from_str(&read(input)?).map_err(|error| error.to_string())?;
    if overlay.format_version != 1 {
        return Err(format!(
            "unsupported annotation format version {}",
            overlay.format_version
        ));
    }
    let mut candidates = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for file in &overlay.files {
        let relative = Path::new(&file.path);
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|component| !matches!(component, Component::Normal(_)))
        {
            return Err(format!("invalid source path: {}", file.path));
        }
        let path = resolve(&root, &root.join(relative))?;
        if !seen.insert(path.clone()) {
            return Err(format!("duplicate source path: {}", file.path));
        }
        let original = read(&path)?;
        let updated = render_source(file, &original, &file.macros)
            .map_err(|error| format!("{}: {error}", file.path))?;
        candidates.push(Change {
            path,
            original,
            updated,
        });
    }
    // Reconstruct wrappers from the candidate sources and their actual
    // supplied includes, never from the overlay's classification alone. Every
    // candidate (including header definitions) is validated before any write.
    let source_index: BTreeMap<_, _> = candidates
        .iter()
        .map(|change| (change.path.clone(), change.updated.as_str()))
        .collect();
    let directories = include_directories(&root, &overlay.include_dirs)?;
    let graph = include_graph(&source_index, &directories)?;
    for (file, change) in overlay.files.iter().zip(&candidates) {
        let macros = discover_macros_mode(
            &context(&change.path, &source_index, &graph),
            file.proofs_only,
        )
        .map_err(|error| format!("{}: {error}", file.path))?;
        validate_application(file, &change.original, &change.updated, &macros)
            .map_err(|error| format!("{}: {error}", file.path))?;
    }
    let changes: Vec<_> = candidates
        .into_iter()
        .filter(|change| change.original != change.updated)
        .collect();
    if !check {
        commit(&changes)?;
    }
    Ok(format!(
        "{}: {} files {}, {} already applied or unchanged",
        if check { "Applicable" } else { "Applied" },
        changes.len(),
        if check { "would change" } else { "changed" },
        overlay.files.len() - changes.len(),
    ))
}
