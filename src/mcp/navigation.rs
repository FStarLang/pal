//! Frozen, owned Clang navigation data. Clang handles never leave `index`.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, Mutex};

use clang_rs::diagnostic::Severity;
use clang_rs::source::{File, SourceLocation, SourceRange};
use clang_rs::token::{Token, TokenKind};
use clang_rs::{
    Clang, Entity, EntityKind, Index, Linkage, PrintingPolicyFlag, TranslationUnit, Unsaved,
};
use lsp_types::{
    CallHierarchyIncomingCall, CallHierarchyItem, CallHierarchyOutgoingCall, Diagnostic,
    DiagnosticSeverity, DocumentSymbol, Hover, HoverContents, Location, MarkupContent, MarkupKind,
    Position, Range, SymbolKind,
};
use rmcp::schemars::{self, JsonSchema};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::diagnostics::Diagnostics;
use super::workspace::{Failure, Result, Snapshot, SourceFile, Toolchain, uri};

#[derive(Clone, Debug, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct PositionInput {
    pub line: u32,
    pub character: u32,
}

impl From<&PositionInput> for Position {
    fn from(position: &PositionInput) -> Self {
        Self::new(position.line, position.character)
    }
}

#[derive(Clone, Debug, Deserialize, JsonSchema)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Query {
    Symbols {
        path: String,
    },
    Definition {
        path: String,
        position: PositionInput,
    },
    References {
        path: String,
        position: PositionInput,
        #[serde(default)]
        include_declaration: bool,
    },
    Callers {
        path: String,
        position: PositionInput,
    },
    Callees {
        path: String,
        position: PositionInput,
    },
    Hover {
        path: String,
        position: PositionInput,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Identity {
    Usr {
        usr: EntityUsr,
        owner: Option<PathBuf>,
    },
    Location {
        path: PathBuf,
        offset: usize,
        owner: Option<Box<Identity>>,
    },
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct SymbolId(usize);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct EntityUsr(String);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct PalModuleName(String);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Span {
    path: PathBuf,
    start: usize,
    end: usize,
}

impl Span {
    fn range(&self, snapshot: &Snapshot) -> Range {
        snapshot.files[&self.path].range(self.start, self.end)
    }

    fn location(&self, snapshot: &Snapshot) -> Result<Location> {
        Ok(Location {
            uri: public_uri(&self.path)?,
            range: self.range(snapshot),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Declaration {
    span: Span,
    range: Range,
    name: Span,
    parent: Option<SymbolId>,
    definition: bool,
}

#[derive(Debug)]
struct Symbol {
    name: String,
    kind: SymbolKind,
    text: String,
    type_name: Option<String>,
    documentation: Option<String>,
    declarations: Vec<Declaration>,
}

impl Symbol {
    fn preferred(&self) -> Option<&Declaration> {
        self.declarations
            .iter()
            .find(|declaration| declaration.definition)
            .or_else(|| self.declarations.first())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Occurrence {
    start: usize,
    end: usize,
    symbol: SymbolId,
    declaration: bool,
    // Macro invocations win over declarations synthesized at the same expansion site.
    priority: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct TokenSpan {
    start: usize,
    end: usize,
}

#[derive(Debug, Default)]
pub struct SemanticIndex {
    pub complete: bool,
    pub diagnostics: Diagnostics,
    pub failure: Option<Failure>,
    identities: BTreeMap<Identity, SymbolId>,
    symbols: Vec<Symbol>,
    occurrences: BTreeMap<PathBuf, Vec<Occurrence>>,
    tokens: BTreeMap<PathBuf, Vec<TokenSpan>>,
    calls: BTreeMap<(SymbolId, SymbolId), Vec<Span>>,
    modules: BTreeMap<PalModuleName, SymbolId>,
}

// The safe binding permits one live Clang instance per process. No native handle is shared.
static CLANG_WORKER: Mutex<()> = Mutex::new(());

/// Parse every C root once, capturing the very buffers used for its semantic index.
/// Failures retain whatever owned index was available before the failed operation.
pub fn index(snapshot: &mut Snapshot, toolchain: &Toolchain) -> Result<SemanticIndex> {
    let _worker = CLANG_WORKER
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let mut result = SemanticIndex {
        complete: true,
        ..SemanticIndex::default()
    };
    match catch_unwind(AssertUnwindSafe(|| {
        build_index(snapshot, toolchain, &mut result)
    })) {
        Ok(Ok(())) => {}
        Ok(Err(failure)) => result.reject(failure),
        Err(_) => result.reject(Failure::new(
            "snapshot_failed",
            "the safe Clang binding could not capture the source buffers",
        )),
    }
    result.finish();
    Ok(result)
}

fn build_index(
    snapshot: &mut Snapshot,
    toolchain: &Toolchain,
    result: &mut SemanticIndex,
) -> Result<()> {
    let clang = Clang::new().map_err(|message| Failure::new("snapshot_failed", message))?;
    let clang_index = Index::new(&clang, false, false);
    for root in snapshot.roots.clone() {
        let identity = snapshot.original(&root).ok_or_else(|| {
            Failure::new("snapshot_failed", "primary source has no original identity")
        })?;
        let source = snapshot.files.get(&identity).ok_or_else(|| {
            Failure::new("snapshot_failed", "primary source has no frozen buffer")
        })?;
        if source.code.as_bytes().contains(&0) {
            return Err(Failure::new(
                "snapshot_failed",
                "Clang's safe unsaved-file binding cannot represent NUL source bytes",
            ));
        }
        // Remapping every header alias makes libclang coalesce file identities and switch
        // lookup directories. Frozen header bytes already live in the authoritative VFS.
        let unsaved = [Unsaved::new(&root, source.code.as_ref())];
        let arguments = snapshot.parser_args(&root, toolchain);
        let mut parser = clang_index.parser(&root);
        parser
            .arguments(&arguments)
            .unsaved(&unsaved)
            .detailed_preprocessing_record(true)
            .keep_going(true);
        let translation_unit = match parser.parse() {
            Ok(translation_unit) => translation_unit,
            Err(error) => {
                result.reject(Failure::new(
                    "translation_failed",
                    format!(
                        "Clang could not parse {}: {error:?}",
                        original_label(snapshot, &root)
                    ),
                ));
                continue;
            }
        };
        let files = capture_files(snapshot, &translation_unit, &root)?;
        let mut annotated = Vec::with_capacity(files.len());
        for file in files {
            let observed = file.get_path();
            let Some(path) = snapshot.original(&observed) else {
                continue;
            };
            let Some(source) = snapshot.files.get(&path) else {
                continue;
            };
            let length = u32::try_from(source.code.len()).map_err(|_| {
                Failure::new(
                    "snapshot_failed",
                    "a project file exceeds Clang's source offset limit",
                )
            })?;
            let range = SourceRange::new(
                file.get_offset_location(0),
                file.get_offset_location(length),
            );
            let tokens = range.tokenize();
            if !result.tokens.contains_key(&path) {
                let ranges = tokens
                    .iter()
                    .filter_map(|token| span(snapshot, token.get_range()))
                    .filter(|range| range.path == path)
                    .map(|range| TokenSpan {
                        start: range.start,
                        end: range.end,
                    })
                    .collect();
                result.tokens.insert(path, ranges);
            }
            let entities = translation_unit.annotate(&tokens);
            annotated.push((tokens, entities));
        }
        result.walk(snapshot, translation_unit.get_entity(), None);
        for (tokens, entities) in annotated {
            for (token, entity) in tokens.into_iter().zip(entities) {
                if token.get_kind() == TokenKind::Identifier {
                    if let Some(entity) = entity {
                        result.annotated_occurrence(snapshot, token, entity);
                    }
                }
            }
        }
        result.clang_diagnostics(snapshot, &translation_unit, &root);
        // Subsequent TUs see the first TU's frozen headers, never a fresh disk read.
        snapshot.write_overlay()?;
    }
    snapshot.write_overlay()?;
    snapshot.write_database(toolchain)?;
    snapshot.recheck_inputs()
}

fn capture_files<'tu>(
    snapshot: &mut Snapshot,
    tu: &'tu TranslationUnit<'tu>,
    root: &Path,
) -> Result<Vec<File<'tu>>> {
    let main = tu.get_file(root).ok_or_else(|| {
        Failure::new(
            "snapshot_failed",
            "Clang did not expose the primary source buffer",
        )
    })?;
    let mut pending = vec![main];
    // Detailed records also expose aliases hidden by include guards.
    for child in tu.get_entity().get_children() {
        if let Some(file) = child.get_file() {
            pending.push(file);
        }
    }
    let mut observed = BTreeSet::new();
    let mut captured = BTreeMap::new();
    while let Some(file) = pending.pop() {
        let path = file.get_path();
        if !observed.insert(path.clone()) {
            continue;
        }
        pending.extend(
            file.get_includes()
                .into_iter()
                .filter_map(|include| include.get_file()),
        );
        if snapshot.original(&path).is_none() {
            continue;
        }
        let contents = file.get_contents().ok_or_else(|| {
            Failure::new(
                "snapshot_failed",
                format!(
                    "Clang did not expose a loaded project buffer: {}",
                    original_label(snapshot, &path)
                ),
            )
        })?;
        snapshot.capture(&path, Arc::from(contents))?;
        if let Some(identity) = snapshot.original(&path) {
            captured.entry(identity).or_insert(file);
        }
    }
    Ok(captured.into_values().collect())
}

impl SemanticIndex {
    fn reject(&mut self, failure: Failure) {
        self.complete = false;
        // Snapshot consistency failures take precedence over ordinary parse errors.
        if self.failure.is_none() || failure.code != "translation_failed" {
            self.failure = Some(failure);
        }
    }

    fn finish(&mut self) {
        for symbol in &mut self.symbols {
            symbol.declarations.sort_by(|a, b| {
                a.span
                    .cmp(&b.span)
                    .then(a.name.cmp(&b.name))
                    .then(a.parent.cmp(&b.parent))
                    .then(a.definition.cmp(&b.definition))
            });
            symbol.declarations.dedup();
        }
        for occurrences in self.occurrences.values_mut() {
            occurrences.sort();
            occurrences.dedup();
        }
        for ranges in self.tokens.values_mut() {
            ranges.sort_unstable();
            ranges.dedup();
        }
        for sites in self.calls.values_mut() {
            sites.sort();
            sites.dedup();
        }
        for diagnostics in self.diagnostics.values_mut() {
            diagnostics.sort_by(|a, b| {
                range_key(a.range)
                    .cmp(&range_key(b.range))
                    .then(a.message.cmp(&b.message))
            });
            diagnostics.dedup();
        }
    }

    fn ensure_symbol(&mut self, snapshot: &Snapshot, entity: Entity<'_>) -> Option<SymbolId> {
        let kind = symbol_kind(entity.get_kind())?;
        let identity = identity(snapshot, entity)?;
        if let Some(&symbol) = self.identities.get(&identity) {
            if self.symbols[symbol.0].documentation.is_none() {
                self.symbols[symbol.0].documentation = entity.get_comment().or_else(|| {
                    entity
                        .get_definition()
                        .and_then(|definition| definition.get_comment())
                });
            }
            return Some(symbol);
        }
        let name = entity.get_name().filter(|name| !name.is_empty())?;
        let representative = entity.get_definition().unwrap_or(entity);
        let text = if representative.is_declaration() {
            representative
                .get_pretty_printer()
                .set_flag(PrintingPolicyFlag::UseTerseOutput, true)
                .print()
        } else {
            representative
                .get_range()
                .and_then(|range| span(snapshot, range))
                .map(|range| snapshot.files[&range.path].code[range.start..range.end].to_owned())
                .unwrap_or_else(|| name.clone())
        };
        let symbol = SymbolId(self.symbols.len());
        self.identities.insert(identity, symbol);
        self.symbols.push(Symbol {
            name,
            kind,
            text,
            type_name: representative.get_type().map(|ty| ty.get_display_name()),
            documentation: representative
                .get_comment()
                .or_else(|| entity.get_comment()),
            declarations: Vec::new(),
        });
        self.add_declaration(snapshot, symbol, representative);
        if representative != entity {
            self.add_declaration(snapshot, symbol, entity);
        }
        Some(symbol)
    }

    fn add_declaration(&mut self, snapshot: &Snapshot, symbol: SymbolId, entity: Entity<'_>) {
        let Some(name) = self.name_spans(snapshot, entity).into_iter().next() else {
            return;
        };
        let full = entity
            .get_range()
            .and_then(|range| span(snapshot, range))
            .filter(|full| {
                full.path == name.path && full.start <= name.start && name.end <= full.end
            })
            .unwrap_or_else(|| name.clone());
        let parent = entity
            .get_semantic_parent()
            .filter(|parent| *parent != entity.get_translation_unit().get_entity())
            .and_then(|parent| self.ensure_symbol(snapshot, parent));
        let declaration = Declaration {
            range: full.range(snapshot),
            span: full,
            name: name.clone(),
            parent,
            definition: entity.is_definition() || entity.get_kind() == EntityKind::MacroDefinition,
        };
        if !self.symbols[symbol.0].declarations.contains(&declaration) {
            self.symbols[symbol.0].declarations.push(declaration);
        }
        self.occurrence(name, symbol, true, 1);
    }

    fn name_spans(&self, snapshot: &Snapshot, entity: Entity<'_>) -> Vec<Span> {
        let mut ranges: Vec<_> = entity
            .get_name_ranges()
            .into_iter()
            .filter_map(|range| span(snapshot, range))
            .filter(|range| {
                self.token_at(&range.path, range.start)
                    .is_some_and(|token| token.start == range.start && token.end == range.end)
            })
            .collect();
        if ranges.is_empty() {
            if let Some((path, offset)) = entity
                .get_location()
                .and_then(|location| point(snapshot, location))
            {
                if let Some(token) = self.token_at(&path, offset) {
                    ranges.push(Span {
                        path,
                        start: token.start,
                        end: token.end,
                    });
                }
            }
        }
        ranges
    }

    fn occurrence(&mut self, span: Span, symbol: SymbolId, declaration: bool, priority: u8) {
        self.occurrences
            .entry(span.path)
            .or_default()
            .push(Occurrence {
                start: span.start,
                end: span.end,
                symbol,
                declaration,
                priority,
            });
    }

    fn walk(&mut self, snapshot: &Snapshot, entity: Entity<'_>, caller: Option<SymbolId>) {
        let kind = entity.get_kind();
        let mut enclosing = caller;
        if entity.is_declaration() || kind == EntityKind::MacroDefinition {
            if let Some(symbol) = self.ensure_symbol(snapshot, entity) {
                self.add_declaration(snapshot, symbol, entity);
                if kind == EntityKind::FunctionDecl {
                    enclosing = Some(symbol);
                }
                let root = entity.get_translation_unit().get_entity();
                // PAL lowers top-level enum constants into Global_<name> modules too.
                if entity.get_semantic_parent().is_some_and(|parent| {
                    parent == root
                        || kind == EntityKind::EnumConstantDecl
                            && parent.get_semantic_parent() == Some(root)
                }) {
                    if let Some(module) = PalModuleName::new(kind, &self.symbols[symbol.0].name) {
                        if self
                            .modules
                            .get(&module)
                            .is_some_and(|&previous| previous != symbol)
                        {
                            self.reject(Failure::new(
                                "module_name_collision",
                                format!("distinct C symbols emit the same PAL module {}", module.0),
                            ));
                        } else {
                            self.modules.insert(module, symbol);
                        }
                    }
                }
            }
        } else if matches!(
            kind,
            EntityKind::DeclRefExpr
                | EntityKind::MemberRefExpr
                | EntityKind::TypeRef
                | EntityKind::VariableRef
                | EntityKind::MemberRef
                | EntityKind::MacroExpansion
        ) {
            if let Some(target) = entity.get_reference() {
                if let Some(symbol) = self.ensure_symbol(snapshot, target) {
                    for range in self.name_spans(snapshot, entity) {
                        self.occurrence(
                            range,
                            symbol,
                            false,
                            if kind == EntityKind::MacroExpansion {
                                0
                            } else {
                                1
                            },
                        );
                    }
                }
            }
        }
        if kind == EntityKind::CallExpr {
            if let (Some(caller), Some(target)) = (
                caller,
                entity
                    .get_reference()
                    .filter(|target| target.get_kind() == EntityKind::FunctionDecl),
            ) {
                if let Some(callee) = self.ensure_symbol(snapshot, target) {
                    if let Some(site) = self.call_site(snapshot, entity) {
                        self.calls.entry((caller, callee)).or_default().push(site);
                    }
                }
            }
        }
        for child in entity.get_children() {
            self.walk(snapshot, child, enclosing);
        }
    }

    fn call_site(&self, snapshot: &Snapshot, entity: Entity<'_>) -> Option<Span> {
        if matches!(
            entity.get_kind(),
            EntityKind::DeclRefExpr | EntityKind::MemberRefExpr
        ) {
            if let Some(range) = self.name_spans(snapshot, entity).into_iter().next() {
                return Some(range);
            }
        }
        if let Some(callee_expression) = entity.get_children().into_iter().next() {
            if let Some(range) = self.call_site(snapshot, callee_expression) {
                return Some(range);
            }
        }
        let (path, offset) = point(snapshot, entity.get_location()?)?;
        let token = self.token_at(&path, offset)?;
        Some(Span {
            path,
            start: token.start,
            end: token.end,
        })
    }

    fn annotated_occurrence(&mut self, snapshot: &Snapshot, token: Token<'_>, entity: Entity<'_>) {
        let target = entity.get_reference().unwrap_or(entity);
        if !(target.is_declaration() || target.get_kind() == EntityKind::MacroDefinition) {
            return;
        }
        let Some(range) = span(snapshot, token.get_range()) else {
            return;
        };
        if (entity.is_declaration() || entity.get_kind() == EntityKind::MacroDefinition)
            && !self.name_spans(snapshot, entity).contains(&range)
        {
            return;
        }
        let Some(symbol) = self.ensure_symbol(snapshot, target) else {
            return;
        };
        let declaration = self.symbols[symbol.0]
            .declarations
            .iter()
            .any(|declaration| declaration.name == range);
        self.occurrence(
            range,
            symbol,
            declaration,
            if entity.get_kind() == EntityKind::MacroExpansion {
                0
            } else {
                1
            },
        );
    }

    fn clang_diagnostics(&mut self, snapshot: &Snapshot, tu: &TranslationUnit<'_>, root: &Path) {
        for diagnostic in tu.get_diagnostics() {
            let severity = match diagnostic.get_severity() {
                Severity::Ignored => continue,
                Severity::Note => DiagnosticSeverity::INFORMATION,
                Severity::Warning => DiagnosticSeverity::WARNING,
                Severity::Error | Severity::Fatal => DiagnosticSeverity::ERROR,
            };
            let message = public_message(snapshot, &diagnostic.get_text());
            if severity == DiagnosticSeverity::ERROR {
                self.reject(Failure::new("translation_failed", message.clone()));
            }
            let location = point(snapshot, diagnostic.get_location())
                .or_else(|| snapshot.original(root).map(|path| (path, 0)));
            let Some((path, offset)) = location else {
                continue;
            };
            let Some(source) = snapshot.files.get(&path) else {
                continue;
            };
            let range = diagnostic
                .get_ranges()
                .into_iter()
                .filter_map(|range| span(snapshot, range))
                .find(|range| range.path == path)
                .map(|range| range.range(snapshot))
                .unwrap_or_else(|| {
                    let end = self
                        .token_at(&path, offset)
                        .map_or_else(|| next_scalar(source, offset), |token| token.end);
                    source.range(offset, end)
                });
            self.diagnostics
                .entry(uri(&path))
                .or_default()
                .push(Diagnostic {
                    range,
                    severity: Some(severity),
                    source: Some("Clang".to_owned()),
                    message,
                    ..Diagnostic::default()
                });
        }
    }

    fn token_at(&self, path: &Path, offset: usize) -> Option<TokenSpan> {
        let tokens = self.tokens.get(path)?;
        let index = tokens
            .partition_point(|token| token.start <= offset)
            .checked_sub(1)?;
        let token = tokens[index];
        (offset < token.end).then_some(token)
    }

    fn symbol_at(&self, path: &Path, offset: usize) -> Option<&Occurrence> {
        let occurrences = self.occurrences.get(path)?;
        let end = occurrences.partition_point(|occurrence| occurrence.start <= offset);
        occurrences[..end]
            .iter()
            .rev()
            .take_while(|occurrence| offset < occurrence.end)
            .min_by_key(|occurrence| (occurrence.end - occurrence.start, occurrence.priority))
    }

    /// Return LSP-shaped JSON using only locations in this frozen project's files.
    pub fn query(&self, snapshot: &Snapshot, query: &Query) -> Result<Value> {
        let (path, position) = match query {
            Query::Symbols { path } => (path, None),
            Query::Definition { path, position }
            | Query::References { path, position, .. }
            | Query::Callers { path, position }
            | Query::Callees { path, position }
            | Query::Hover { path, position } => (path, Some(position)),
        };
        let path = query_path(snapshot, path)?;
        if matches!(query, Query::Symbols { .. }) {
            return json(self.document_symbols(snapshot, &path));
        }
        let source = &snapshot.files[&path];
        let offset = source
            .offset(Position::from(position.ok_or_else(|| {
                Failure::new("invalid_position", "a source position is required")
            })?))?;
        let Some(occurrence) = self.symbol_at(&path, offset) else {
            return Ok(if matches!(query, Query::Hover { .. }) {
                Value::Null
            } else {
                Value::Array(Vec::new())
            });
        };
        let symbol = &self.symbols[occurrence.symbol.0];
        match query {
            Query::Definition { .. } => {
                let definitions: Vec<_> = symbol
                    .declarations
                    .iter()
                    .filter(|declaration| declaration.definition)
                    .collect();
                let declarations = if definitions.is_empty() {
                    symbol.declarations.iter().collect()
                } else {
                    definitions
                };
                locations(
                    snapshot,
                    declarations
                        .into_iter()
                        .map(|declaration| declaration.name.clone()),
                )
            }
            Query::References {
                include_declaration,
                ..
            } => {
                let spans = self.occurrences.iter().flat_map(|(path, occurrences)| {
                    occurrences
                        .iter()
                        .filter(move |reference| {
                            reference.symbol == occurrence.symbol
                                && (*include_declaration || !reference.declaration)
                        })
                        .map(move |reference| Span {
                            path: path.clone(),
                            start: reference.start,
                            end: reference.end,
                        })
                });
                locations(snapshot, spans)
            }
            Query::Callers { .. } => {
                let mut calls = Vec::new();
                for (&(caller, callee), sites) in &self.calls {
                    if callee == occurrence.symbol {
                        if let Some(item) = self.call_item(snapshot, caller)? {
                            let ranges = sites
                                .iter()
                                .filter(|site| uri(&site.path) == item.uri.as_str())
                                .map(|site| site.range(snapshot))
                                .collect();
                            calls.push(CallHierarchyIncomingCall {
                                from: item,
                                from_ranges: ranges,
                            });
                        }
                    }
                }
                calls.sort_by(|a, b| {
                    a.from.uri.as_str().cmp(b.from.uri.as_str()).then(
                        range_key(a.from.selection_range).cmp(&range_key(b.from.selection_range)),
                    )
                });
                json(calls)
            }
            Query::Callees { .. } => {
                let mut calls = Vec::new();
                for (&(caller, callee), sites) in &self.calls {
                    if caller == occurrence.symbol {
                        if let Some(item) = self.call_item(snapshot, callee)? {
                            calls.push(CallHierarchyOutgoingCall {
                                to: item,
                                from_ranges: sites
                                    .iter()
                                    .map(|site| site.range(snapshot))
                                    .collect(),
                            });
                        }
                    }
                }
                calls.sort_by(|a, b| {
                    a.to.uri
                        .as_str()
                        .cmp(b.to.uri.as_str())
                        .then(range_key(a.to.selection_range).cmp(&range_key(b.to.selection_range)))
                });
                json(calls)
            }
            Query::Hover { .. } => {
                let mut text = public_message(snapshot, &symbol.text);
                if let Some(ty) = &symbol.type_name {
                    if !ty.is_empty() {
                        text.push_str("\nType: ");
                        text.push_str(&public_message(snapshot, ty));
                    }
                }
                if let Some(documentation) = &symbol.documentation {
                    text.push_str("\n\n");
                    text.push_str(&public_message(snapshot, documentation));
                }
                json(Hover {
                    contents: HoverContents::Markup(MarkupContent {
                        kind: MarkupKind::PlainText,
                        value: text,
                    }),
                    range: Some(source.range(occurrence.start, occurrence.end)),
                })
            }
            Query::Symbols { .. } => unreachable!("symbols handled before position lookup"),
        }
    }

    fn call_item(
        &self,
        snapshot: &Snapshot,
        symbol: SymbolId,
    ) -> Result<Option<CallHierarchyItem>> {
        let symbol = &self.symbols[symbol.0];
        let Some(declaration) = symbol.preferred() else {
            return Ok(None);
        };
        Ok(Some(CallHierarchyItem {
            name: symbol.name.clone(),
            kind: SymbolKind::FUNCTION,
            tags: None,
            detail: Some(public_message(snapshot, &symbol.text)),
            uri: public_uri(&declaration.name.path)?,
            range: declaration.span.range(snapshot),
            selection_range: declaration.name.range(snapshot),
            data: None,
        }))
    }

    fn document_symbols(&self, snapshot: &Snapshot, path: &Path) -> Vec<DocumentSymbol> {
        let mut records: Vec<_> = self
            .symbols
            .iter()
            .enumerate()
            .flat_map(|(symbol, data)| {
                data.declarations
                    .iter()
                    .filter(move |declaration| declaration.name.path == path)
                    .map(move |declaration| (SymbolId(symbol), declaration))
            })
            .collect();
        records.sort_by(|a, b| a.1.span.cmp(&b.1.span).then(a.0.cmp(&b.0)));
        records.dedup_by(|a, b| a.0 == b.0 && a.1.name == b.1.name);
        let mut children: BTreeMap<Option<usize>, Vec<usize>> = BTreeMap::new();
        for (index, (_, declaration)) in records.iter().enumerate() {
            let parent = declaration.parent.and_then(|parent| {
                records
                    .iter()
                    .enumerate()
                    .filter(|(other, (symbol, candidate))| {
                        *other != index
                            && *symbol == parent
                            && candidate.span.start <= declaration.span.start
                            && declaration.span.end <= candidate.span.end
                    })
                    .min_by_key(|(_, (_, candidate))| candidate.span.end - candidate.span.start)
                    .map(|(index, _)| index)
            });
            children.entry(parent).or_default().push(index);
        }
        self.document_children(snapshot, &records, &children, None)
    }

    #[allow(deprecated)]
    fn document_children(
        &self,
        snapshot: &Snapshot,
        records: &[(SymbolId, &Declaration)],
        children: &BTreeMap<Option<usize>, Vec<usize>>,
        parent: Option<usize>,
    ) -> Vec<DocumentSymbol> {
        children
            .get(&parent)
            .into_iter()
            .flatten()
            .map(|&index| {
                let (symbol, declaration) = records[index];
                let symbol = &self.symbols[symbol.0];
                let nested = self.document_children(snapshot, records, children, Some(index));
                DocumentSymbol {
                    name: symbol.name.clone(),
                    detail: symbol
                        .type_name
                        .as_ref()
                        .map(|ty| public_message(snapshot, ty)),
                    kind: symbol.kind,
                    tags: None,
                    deprecated: None,
                    range: declaration.span.range(snapshot),
                    selection_range: declaration.name.range(snapshot),
                    children: (!nested.is_empty()).then_some(nested),
                }
            })
            .collect()
    }

    /// Owned Clang declaration extent, for coarse C ownership of verifier issues.
    pub fn declaration_range(&self, path: &Path, name: &str) -> Option<Range> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .flat_map(|symbol| &symbol.declarations)
            .filter(|declaration| declaration.span.path == path)
            .max_by_key(|declaration| {
                (
                    declaration.definition,
                    declaration.span.end - declaration.span.start,
                )
            })
            .map(|declaration| declaration.range)
    }

    /// Normalize PAL's inclusive byte columns without reusing its byte-based LSP conversion.
    pub fn normalize_range(&self, snapshot: &Snapshot, path: &Path, range: Range) -> Result<Range> {
        let path = snapshot
            .original(path)
            .ok_or_else(|| Failure::new("missing_file", "diagnostic source is not captured"))?;
        let source = snapshot
            .files
            .get(&path)
            .ok_or_else(|| Failure::new("missing_file", "diagnostic source is not captured"))?;
        let start = source.byte_position(range.start.line, range.start.character)?;
        let end = source.byte_position(range.end.line, range.end.character)?;
        if end < start {
            return Err(Failure::new(
                "invalid_position",
                "diagnostic range ends before it starts",
            ));
        }
        let end = self
            .token_at(&path, end)
            .map_or_else(|| next_scalar(source, end), |token| token.end);
        Ok(source.range(start, end))
    }
}

fn identity(snapshot: &Snapshot, entity: Entity<'_>) -> Option<Identity> {
    let canonical = entity.get_canonical_entity();
    let anchor = canonical.get_definition().unwrap_or(canonical);
    let (path, offset) = point(snapshot, anchor.get_location()?)?;
    if let Some(usr) = canonical.get_usr().filter(|usr| !usr.0.is_empty()) {
        let owner = (!matches!(
            canonical.get_linkage(),
            Some(Linkage::External | Linkage::UniqueExternal)
        ))
        .then_some(path);
        Some(Identity::Usr {
            usr: EntityUsr(usr.0),
            owner,
        })
    } else {
        let owner = canonical
            .get_semantic_parent()
            .filter(|parent| *parent != canonical.get_translation_unit().get_entity())
            .and_then(|parent| identity(snapshot, parent))
            .map(Box::new);
        Some(Identity::Location {
            path,
            offset,
            owner,
        })
    }
}

fn point(snapshot: &Snapshot, location: SourceLocation<'_>) -> Option<(PathBuf, usize)> {
    let location = location.get_expansion_location();
    let path = snapshot.original(&location.file?.get_path())?;
    let source = snapshot.files.get(&path)?;
    let offset = usize::try_from(location.offset).ok()?;
    (offset <= source.code.len() && source.code.is_char_boundary(offset)).then_some((path, offset))
}

fn span(snapshot: &Snapshot, range: SourceRange<'_>) -> Option<Span> {
    let (path, start) = point(snapshot, range.get_start())?;
    let (end_path, end) = point(snapshot, range.get_end())?;
    (path == end_path && start <= end).then_some(Span { path, start, end })
}

fn symbol_kind(kind: EntityKind) -> Option<SymbolKind> {
    Some(match kind {
        EntityKind::FunctionDecl => SymbolKind::FUNCTION,
        EntityKind::VarDecl | EntityKind::ParmDecl => SymbolKind::VARIABLE,
        EntityKind::FieldDecl => SymbolKind::FIELD,
        EntityKind::StructDecl | EntityKind::UnionDecl => SymbolKind::STRUCT,
        EntityKind::EnumDecl => SymbolKind::ENUM,
        EntityKind::EnumConstantDecl => SymbolKind::ENUM_MEMBER,
        EntityKind::TypedefDecl => SymbolKind::TYPE_PARAMETER,
        EntityKind::MacroDefinition => SymbolKind::CONSTANT,
        _ => return None,
    })
}

impl PalModuleName {
    fn new(kind: EntityKind, name: &str) -> Option<Self> {
        let prefix = match kind {
            EntityKind::FunctionDecl => "Func_",
            EntityKind::VarDecl | EntityKind::EnumConstantDecl => "Global_",
            EntityKind::TypedefDecl => "Typedef_",
            EntityKind::StructDecl => "Struct_",
            EntityKind::UnionDecl => "Union_",
            _ => return None,
        };
        Some(Self(format!("{prefix}{name}")))
    }
}

fn query_path(snapshot: &Snapshot, path: &str) -> Result<PathBuf> {
    let relative = Path::new(path);
    if path.is_empty()
        || path.contains('\0')
        || path.contains("://")
        || relative.is_absolute()
        || relative
            .components()
            .any(|component| !matches!(component, Component::Normal(_) | Component::CurDir))
        || !matches!(
            relative
                .extension()
                .and_then(|extension| extension.to_str()),
            Some("c" | "h")
        )
    {
        return Err(Failure::new(
            "invalid_path",
            "query paths must be workspace-relative .c or .h files",
        ));
    }
    snapshot
        .original(&snapshot.root.join(relative))
        .filter(|path| snapshot.files.contains_key(path))
        .ok_or_else(|| Failure::new("missing_file", "query source is not part of this snapshot"))
}

fn public_uri(path: &Path) -> Result<lsp_types::Uri> {
    uri(path).parse().map_err(|_| {
        Failure::new(
            "snapshot_failed",
            "a project path cannot be represented as a file URI",
        )
    })
}

fn original_label(snapshot: &Snapshot, path: &Path) -> String {
    snapshot
        .original(path)
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "project source".to_owned())
}

fn public_message(snapshot: &Snapshot, message: &str) -> String {
    message.replace(
        snapshot.mirror().to_string_lossy().as_ref(),
        snapshot.root.to_string_lossy().as_ref(),
    )
}

fn next_scalar(source: &SourceFile, offset: usize) -> usize {
    source
        .code
        .get(offset..)
        .and_then(|rest| rest.chars().next())
        .map_or(offset, |character| offset + character.len_utf8())
}

fn locations(snapshot: &Snapshot, spans: impl IntoIterator<Item = Span>) -> Result<Value> {
    let spans: BTreeSet<_> = spans.into_iter().collect();
    let mut locations = spans
        .iter()
        .map(|span| span.location(snapshot))
        .collect::<Result<Vec<_>>>()?;
    locations.sort_by(|a, b| {
        a.uri
            .as_str()
            .cmp(b.uri.as_str())
            .then(range_key(a.range).cmp(&range_key(b.range)))
    });
    json(locations)
}

fn range_key(range: Range) -> (u32, u32, u32, u32) {
    (
        range.start.line,
        range.start.character,
        range.end.line,
        range.end.character,
    )
}

fn json(value: impl Serialize) -> Result<Value> {
    serde_json::to_value(value).map_err(|error| {
        Failure::new(
            "snapshot_failed",
            format!("could not serialize navigation data: {error}"),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::super::workspace::{Change, prepare};
    use super::*;

    #[test]
    fn frozen_clang_identity_navigation_and_partial_failures() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().canonicalize().unwrap();
        std::fs::write(root.join("defs.h"), "#define VALUE 7\n").unwrap();
        let code = concat!(
            "#include \"defs.h\"\n",
            "int target(int x) { return x; }\n",
            "int caller(int x) { int y=x; { int x=y; /* 𝄞 */ y=target(x); } return y; }\n",
            "int pointer(int x) { int (*fp)(int)=target; return fp(x); }\n",
            "int value(void) { return VALUE; }\n",
        );
        let toolchain = Toolchain::discover().unwrap();
        let mut snapshot = prepare(
            root.clone(),
            Vec::new(),
            vec![Change::Replace {
                path: "navigation.c".to_owned(),
                code: code.to_owned(),
            }],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let index = index(&mut snapshot, &toolchain).unwrap();
        assert!(index.complete, "{:?}", index.failure);
        assert_eq!(
            snapshot.files[&root.join("defs.h")].code.as_ref(),
            "#define VALUE 7\n"
        );
        let file = &snapshot.files[&root.join("navigation.c")];
        let position = |offset| {
            let position = file.position(offset);
            PositionInput {
                line: position.line,
                character: position.character,
            }
        };
        let at = |needle: &str| position(code.find(needle).unwrap());
        let inner_argument = code.find("target(x)").unwrap() + "target(".len();
        let definition: Vec<Location> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Definition {
                        path: "navigation.c".to_owned(),
                        position: position(inner_argument),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(
            definition[0].range.start,
            file.position(code.find("int x=y").unwrap() + 4)
        );
        let callers: Vec<CallHierarchyIncomingCall> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Callers {
                        path: "navigation.c".to_owned(),
                        position: at("target("),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(callers.len(), 1);
        assert_eq!(callers[0].from.name, "caller");
        assert_eq!(
            callers[0].from_ranges,
            vec![file.range(
                code.find("target(x)").unwrap(),
                code.find("target(x)").unwrap() + 6
            )]
        );
        let callees: Vec<CallHierarchyOutgoingCall> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Callees {
                        path: "navigation.c".to_owned(),
                        position: at("caller("),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(callees.len(), 1);
        assert_eq!(callees[0].to.name, "target");
        let references: Vec<Location> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::References {
                        path: "navigation.c".to_owned(),
                        position: at("target("),
                        include_declaration: false,
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(references.len(), 2);
        let macro_definition: Vec<Location> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Definition {
                        path: "navigation.c".to_owned(),
                        position: at("VALUE"),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(macro_definition[0].uri.as_str(), uri(&root.join("defs.h")));
        let symbols: Vec<DocumentSymbol> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Symbols {
                        path: "navigation.c".to_owned(),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert!(symbols.iter().any(|symbol| symbol.name == "caller"));
        let hover: Option<Hover> = serde_json::from_value(
            index
                .query(
                    &snapshot,
                    &Query::Hover {
                        path: "navigation.c".to_owned(),
                        position: at("target(x)"),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert!(hover.is_some());
        let mut surrogate = at("𝄞");
        surrogate.character += 1;
        assert_eq!(
            index
                .query(
                    &snapshot,
                    &Query::Hover {
                        path: "navigation.c".to_owned(),
                        position: surrogate
                    }
                )
                .unwrap_err()
                .code,
            "invalid_position"
        );
        let raw_start = code.find("target(x)").unwrap();
        let line_start = code[..raw_start].rfind('\n').unwrap() + 1;
        let byte_column = u32::try_from(raw_start - line_start).unwrap();
        let raw = Range::new(
            Position::new(2, byte_column),
            Position::new(2, byte_column + 1),
        );
        assert_eq!(
            index
                .normalize_range(&snapshot, &root.join("navigation.c"), raw)
                .unwrap(),
            file.range(raw_start, raw_start + 6)
        );
        let mut failed = prepare(
            root.clone(),
            snapshot.sources.clone(),
            vec![Change::Append {
                path: "navigation.c".to_owned(),
                code: "\nint broken( {\n".to_owned(),
            }],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let partial = super::index(&mut failed, &toolchain).unwrap();
        assert!(!partial.complete);
        assert_eq!(partial.failure.as_ref().unwrap().code, "translation_failed");
        assert!(
            !partial
                .query(
                    &failed,
                    &Query::Definition {
                        path: "navigation.c".to_owned(),
                        position: at("target(x)")
                    }
                )
                .unwrap()
                .as_array()
                .unwrap()
                .is_empty()
        );
        let mut documented = prepare(root.clone(), Vec::new(), vec![
            Change::Replace { path: "doc.h".to_owned(), code: "int documented(int value);\n".to_owned() },
            Change::Replace { path: "doc_caller.c".to_owned(), code: "#include \"doc.h\"\nint doc_caller(int value) { return documented(value); }\n".to_owned() },
            Change::Replace { path: "doc_def.c".to_owned(), code: "#include \"doc.h\"\n/** cross-unit documentation */\nint documented(int value) { return value; }\n".to_owned() },
        ], Vec::new(), Vec::new()).unwrap();
        let documented_index = super::index(&mut documented, &toolchain).unwrap();
        assert!(documented_index.complete, "{:?}", documented_index.failure);
        let caller = &documented.files[&root.join("doc_caller.c")];
        let point = caller.position(caller.code.find("documented(value)").unwrap());
        let at_call = PositionInput {
            line: point.line,
            character: point.character,
        };
        let definitions: Vec<Location> = serde_json::from_value(
            documented_index
                .query(
                    &documented,
                    &Query::Definition {
                        path: "doc_caller.c".to_owned(),
                        position: at_call.clone(),
                    },
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(definitions[0].uri.as_str(), uri(&root.join("doc_def.c")));
        let hover = documented_index
            .query(
                &documented,
                &Query::Hover {
                    path: "doc_caller.c".to_owned(),
                    position: at_call,
                },
            )
            .unwrap();
        assert!(
            hover.to_string().contains("cross-unit documentation"),
            "{hover}"
        );

        let mut collision = prepare(
            root.clone(),
            Vec::new(),
            vec![
                Change::Replace {
                    path: "a/unit.c".to_owned(),
                    code: "static int duplicate(void) { return 1; }".to_owned(),
                },
                Change::Replace {
                    path: "b/unit.c".to_owned(),
                    code: "static int duplicate(void) { return 2; }".to_owned(),
                },
            ],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let collision = super::index(&mut collision, &toolchain).unwrap();
        assert_eq!(
            collision.failure.as_ref().unwrap().code,
            "module_name_collision"
        );

        std::fs::create_dir(root.join("sub")).unwrap();
        std::fs::write(
            root.join("sub/shared.h"),
            "#ifndef FIRST\n#include \"only_second.h\"\n#endif\n",
        )
        .unwrap();
        std::fs::write(root.join("sub/only_second.h"), "#define SECOND_VALUE 2\n").unwrap();
        std::fs::write(root.join("sub/available.h"), "").unwrap();
        std::fs::write(root.join("sub/probe.h"), "#if __has_include(\"available.h\")\n#define PROBED 1\n#else\n#define PROBED 2\n#endif\n").unwrap();
        std::fs::write(root.join("real.h"), "#define ALIASED 1\n").unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink(root.join("real.h"), root.join("alias.h")).unwrap();
        #[cfg(windows)]
        std::os::windows::fs::symlink_file(root.join("real.h"), root.join("alias.h")).unwrap();
        let mut sparse = prepare(
            root,
            Vec::new(),
            vec![
                Change::Replace {
                    path: "first.c".to_owned(),
                    code: "#define FIRST\n#include \"sub/shared.h\"\n".to_owned(),
                },
                Change::Replace {
                    path: "second.c".to_owned(),
                    code: "#include \"sub/shared.h\"\nint second(void) { return SECOND_VALUE; }\n"
                        .to_owned(),
                },
                Change::Replace {
                    path: "probe.c".to_owned(),
                    code: "#include \"sub/probe.h\"\nint probe(void) { return PROBED; }\n"
                        .to_owned(),
                },
                Change::Replace {
                    path: "alias.c".to_owned(),
                    code: "#include \"alias.h\"\nint aliased(void) { return ALIASED; }\n"
                        .to_owned(),
                },
                Change::Replace {
                    path: "real.h".to_owned(),
                    code: "#define ALIASED 3\n".to_owned(),
                },
            ],
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        let indexed = super::index(&mut sparse, &toolchain).unwrap();
        assert!(indexed.complete, "{:?}", indexed.failure);
        for (source, expected) in [("probe.c", "return 1;"), ("alias.c", "return 3;")] {
            let private = sparse.mirror().join(source);
            let output = std::process::Command::new(&toolchain.clang)
                .args(sparse.parser_args(&private, &toolchain))
                .args(["-E", "-P"])
                .arg(private)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(String::from_utf8(output.stdout).unwrap().contains(expected));
        }
    }
}
