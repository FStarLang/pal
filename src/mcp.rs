//! Optional local MCP service. Compiler state never crosses a worker boundary.

mod diagnostics;
mod navigation;
mod process;
mod verify;
mod workspace;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::{
    Arc, Mutex, MutexGuard,
    atomic::{AtomicBool, AtomicU64, Ordering},
};
use std::time::{Duration, Instant};

use rmcp::handler::server::{router::tool::ToolRouter, wrapper::Parameters};
use rmcp::model::*;
use rmcp::schemars::{self, JsonSchema};
use rmcp::service::{RequestContext, RoleServer, SubscriptionContext};
use rmcp::{ErrorData, ServerHandler, tool, tool_handler, tool_router};
use serde::{Deserialize, Serialize};
use serde_json::json;
use tokio::sync::{broadcast, watch};

use diagnostics::Diagnostics;
use navigation::{Query, SemanticIndex};
use process::Cancellation;
use verify::{VerifiedArtifacts, Verifier};
use workspace::{Change, Failure, ManagedSource, Snapshot, Toolchain};

#[derive(clap::Parser)]
#[command(
    name = "pal mcp",
    bin_name = "pal mcp",
    about = "Serve incremental PAL verification and Clang navigation over MCP stdio"
)]
struct McpCli {
    #[arg(long, default_value = "fstar.exe")]
    fstar_exe: PathBuf,
    #[arg(long, default_value_os_t = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("pulse"))]
    pulse_dir: PathBuf,
}

pub(super) fn dispatch_if_requested() -> bool {
    use clap::Parser;
    use rmcp::ServiceExt;
    if std::env::args_os().nth(1).as_deref() != Some(std::ffi::OsStr::new("mcp")) {
        return false;
    }
    let cli = McpCli::parse_from(std::env::args_os().skip(1));
    let result = (|| {
        let server = PalMcpServer::new(cli.fstar_exe, cli.pulse_dir)?;
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()
            .map_err(|error| {
                Failure::new(
                    "worker_failed",
                    format!("cannot start MCP runtime: {error}"),
                )
            })?;
        runtime.block_on(async {
            let result = match server.clone().serve(rmcp::transport::stdio()).await {
                Ok(service) => service.waiting().await.map(|_| ()).map_err(|error| {
                    Failure::new("worker_failed", format!("MCP transport failed: {error}"))
                }),
                Err(error) => Err(Failure::new(
                    "worker_failed",
                    format!("MCP initialization failed: {error}"),
                )),
            };
            server.shutdown().await;
            result
        })
    })();
    if let Err(error) = result {
        eprintln!("pal mcp: {error}");
        std::process::exit(1);
    }
    true
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Deserialize, Serialize, JsonSchema)]
#[serde(transparent)]
struct SessionId(String);

impl SessionId {
    fn next() -> Result<Self, ErrorData> {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map(|id| Self(format!("s{id}")))
            .map_err(|_| ErrorData::internal_error("session IDs exhausted", None))
    }
    fn status_uri(&self) -> String {
        format!("pal://sessions/{}/status", self.0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(transparent)]
struct JobId(String);

impl JobId {
    fn next() -> Result<Self, ErrorData> {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map(|id| Self(format!("j{id}")))
            .map_err(|_| ErrorData::internal_error("job IDs exhausted", None))
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(transparent)]
struct Revision(u64);

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(transparent)]
struct StatusSequence(u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Phase {
    Idle,
    Queued,
    Snapshotting,
    Translating,
    Verifying,
    Accepted,
    Failed,
    Cancelled,
}

impl Phase {
    fn terminal(self) -> bool {
        matches!(self, Self::Accepted | Self::Failed | Self::Cancelled)
    }
}

#[derive(Serialize)]
struct Status {
    session_id: SessionId,
    job_id: Option<JobId>,
    base_revision: Revision,
    accepted_revision: Revision,
    sequence: StatusSequence,
    phase: Phase,
    elapsed_ms: u64,
    message: String,
    verification_cache_hit: bool,
    diagnostics: Diagnostics,
    error: Option<Failure>,
}

struct Indexed {
    snapshot: Arc<Snapshot>,
    index: Arc<SemanticIndex>,
}
struct Accepted {
    job_id: JobId,
    indexed: Arc<Indexed>,
    proofs: Arc<VerifiedArtifacts>,
}
struct Job {
    id: JobId,
    cancel: Cancellation,
    done: watch::Sender<Option<Phase>>,
    indexed: Option<Arc<Indexed>>,
    active: bool,
    started: Instant,
    last_update: Instant,
    pending_message: String,
}
struct Session {
    includes: Vec<PathBuf>,
    defines: Vec<String>,
    revision: Revision,
    accepted: Option<Accepted>,
    job: Option<Job>,
    status: Status,
    closing: bool,
}
struct Project {
    root: Option<PathBuf>,
    sessions: BTreeMap<SessionId, Session>,
}
struct Shared {
    verifier: Verifier,
    project: Mutex<Project>,
    reset: tokio::sync::Mutex<()>,
    shutting_down: AtomicBool,
    updates: broadcast::Sender<String>,
}
impl Shared {
    fn project(&self) -> MutexGuard<'_, Project> {
        self.project
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }
    fn publish(&self, session: &mut Session) {
        session.status.sequence.0 = session.status.sequence.0.saturating_add(1);
        if let Some(job) = &mut session.job {
            session.status.elapsed_ms =
                u64::try_from(job.started.elapsed().as_millis()).unwrap_or(u64::MAX);
            job.last_update = Instant::now();
        }
        let _ = self.updates.send(session.status.session_id.status_uri());
    }
    fn progress(
        &self,
        session_id: &SessionId,
        job_id: &JobId,
        phase: Phase,
        message: &str,
        force: bool,
    ) {
        let mut project = self.project();
        let Some(session) = project.sessions.get_mut(session_id) else {
            return;
        };
        let Some(job) = session
            .job
            .as_mut()
            .filter(|job| job.id == *job_id && job.active)
        else {
            return;
        };
        if session.status.phase.terminal() {
            return;
        }
        let changed_phase = session.status.phase != phase;
        session.status.phase = phase;
        if !message.is_empty() {
            job.pending_message = public_text(job.indexed.as_deref(), message);
        }
        if force || changed_phase || job.last_update.elapsed() >= Duration::from_secs(1) {
            if !job.pending_message.is_empty() {
                session.status.message = std::mem::take(&mut job.pending_message);
            }
            self.publish(session);
        }
    }
    fn existing_uris(&self, requested: &[String]) -> Vec<String> {
        let project = self.project();
        requested
            .iter()
            .filter(|uri| project.sessions.keys().any(|id| id.status_uri() == **uri))
            .cloned()
            .collect()
    }
}

#[derive(Clone)]
pub(super) struct PalMcpServer {
    shared: Arc<Shared>,
    tool_router: ToolRouter<Self>,
}

#[derive(Deserialize, JsonSchema)]
#[serde(tag = "action", rename_all = "snake_case", deny_unknown_fields)]
#[schemars(extend("type" = "object"))]
enum SessionAction {
    Open {
        #[serde(default)]
        include_paths: Vec<String>,
        #[serde(default)]
        defines: Vec<String>,
    },
    Cancel {
        session_id: SessionId,
        job_id: JobId,
    },
    Close {
        session_id: SessionId,
    },
}
#[derive(Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
struct VerifyInput {
    session_id: SessionId,
    base_revision: Revision,
    changes: Vec<Change>,
}
#[derive(Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
struct QueryInput {
    session_id: SessionId,
    job_id: Option<JobId>,
    query: Query,
}

#[derive(Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
struct IncludePathsInput {
    session_id: SessionId,
    include_paths: Vec<String>,
}

#[derive(Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
struct PreprocessorDefinitionInput {
    session_id: SessionId,
    defines: Vec<String>,
}

#[derive(Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
struct RootInput {
    path: String,
}

impl PalMcpServer {
    pub(super) fn new(fstar: PathBuf, pulse: PathBuf) -> workspace::Result<Self> {
        let verifier = Verifier::new(Toolchain::discover()?, fstar, pulse)?;
        Ok(Self {
            shared: Arc::new(Shared {
                verifier,
                project: Mutex::new(Project {
                    root: None,
                    sessions: BTreeMap::new(),
                }),
                reset: tokio::sync::Mutex::new(()),
                shutting_down: AtomicBool::new(false),
                updates: broadcast::channel(64).0,
            }),
            tool_router: Self::tool_router(),
        })
    }

    fn add_compile_options(
        &self,
        session_id: SessionId,
        include_paths: Vec<String>,
        defines: Vec<String>,
    ) -> Result<CallToolResult, ErrorData> {
        validate_compile_options(&include_paths, &defines)?;
        let mut project = self.shared.project();
        let root = project
            .root
            .clone()
            .ok_or_else(|| params("no_root", "call new_root before opening a session"))?;
        let session = project
            .sessions
            .get_mut(&session_id)
            .filter(|session| !session.closing)
            .ok_or_else(|| params("unknown_session", "session does not exist"))?;
        if session.job.as_ref().is_some_and(|job| job.active) {
            return Err(params("session_busy", "session already has an active job"));
        }
        self.shared
            .verifier
            .invalidate_all()
            .map_err(|error| ErrorData::internal_error(error.message, None))?;
        session
            .includes
            .extend(include_paths.into_iter().map(|path| root.join(path)));
        session.defines.extend(defines);
        Ok(CallToolResult::structured(json!({
            "session_id": session_id,
            "accepted_revision": session.revision,
            "include_paths": session.includes,
            "defines": session.defines,
        })))
    }

    async fn reset_project(&self, root: Option<PathBuf>) -> workspace::Result<()> {
        let _reset = self.shared.reset.lock().await;
        if root.is_some() && self.shared.shutting_down.load(Ordering::Relaxed) {
            return Err(Failure::new("worker_failed", "PAL server is shutting down"));
        }
        let pending: Vec<_> = {
            let mut project = self.shared.project();
            project.root = None;
            project
                .sessions
                .values_mut()
                .filter_map(|session| {
                    session.closing = true;
                    session.job.as_ref().filter(|job| job.active).map(|job| {
                        job.cancel.cancel();
                        job.done.subscribe()
                    })
                })
                .collect()
        };
        for mut done in pending {
            let _ = done.wait_for(|done| done.is_some()).await;
        }
        let invalidated = self.shared.verifier.clear().await;
        let mut project = self.shared.project();
        for id in project.sessions.keys() {
            let _ = self.shared.updates.send(id.status_uri());
        }
        project.sessions.clear();
        invalidated?;
        if !self.shared.shutting_down.load(Ordering::Relaxed) {
            project.root = root;
        } else if root.is_some() {
            return Err(Failure::new("worker_failed", "PAL server is shutting down"));
        }
        Ok(())
    }

    pub(super) async fn shutdown(&self) {
        self.shared.shutting_down.store(true, Ordering::Relaxed);
        let _ = self.reset_project(None).await;
    }
}

#[tool_router]
impl PalMcpServer {
    #[tool(
        description = "Start a new PAL project at path. Cancels and joins all old jobs, removes sessions and status resources, and clears all verification caches. Relative paths use the server process working directory; invalid paths leave the current project intact."
    )]
    async fn new_root(
        &self,
        Parameters(input): Parameters<RootInput>,
    ) -> Result<CallToolResult, ErrorData> {
        if input.path.is_empty() || input.path.contains('\0') {
            return Err(params(
                "invalid_path",
                "root path must be a nonempty filesystem path",
            ));
        }
        let root = PathBuf::from(input.path).canonicalize().map_err(|error| {
            params(
                "invalid_path",
                &format!("cannot open workspace root: {error}"),
            )
        })?;
        if !root.is_dir() {
            return Err(params("invalid_path", "workspace root must be a directory"));
        }
        // Finish the reset even if the client cancels this tool request.
        let server = self.clone();
        tokio::spawn(async move {
            server
                .reset_project(Some(root.clone()))
                .await
                .map_err(|error| ErrorData::internal_error(error.message, None))?;
            Ok(CallToolResult::structured(json!({"root":root})))
        })
        .await
        .map_err(|error| {
            ErrorData::internal_error(format!("project reset failed: {error}"), None)
        })?
    }

    #[tool(description = "Open a PAL verification session, cancel its job, or close it.")]
    async fn pal_session(
        &self,
        Parameters(action): Parameters<SessionAction>,
    ) -> Result<CallToolResult, ErrorData> {
        match action {
            SessionAction::Open {
                include_paths,
                defines,
            } => {
                validate_compile_options(&include_paths, &defines)?;
                let id = SessionId::next()?;
                let status = Status {
                    session_id: id.clone(),
                    job_id: None,
                    base_revision: Revision(0),
                    accepted_revision: Revision(0),
                    sequence: StatusSequence(0),
                    phase: Phase::Idle,
                    elapsed_ms: 0,
                    message: String::new(),
                    verification_cache_hit: false,
                    diagnostics: Diagnostics::new(),
                    error: None,
                };
                let mut project = self.shared.project();
                if self.shared.shutting_down.load(Ordering::Relaxed) {
                    return Err(ErrorData::internal_error(
                        "PAL server is shutting down",
                        None,
                    ));
                }
                let root = project
                    .root
                    .as_ref()
                    .ok_or_else(|| params("no_root", "call new_root before opening a session"))?;
                let includes = include_paths
                    .into_iter()
                    .map(|path| root.join(path))
                    .collect();
                project.sessions.insert(
                    id.clone(),
                    Session {
                        includes,
                        defines,
                        revision: Revision(0),
                        accepted: None,
                        job: None,
                        status,
                        closing: false,
                    },
                );
                Ok(CallToolResult::structured(
                    json!({"session_id":id,"accepted_revision":0,"status_uri":id.status_uri()}),
                ))
            }
            SessionAction::Cancel { session_id, job_id } => {
                let mut done = {
                    let project = self.shared.project();
                    let session = project
                        .sessions
                        .get(&session_id)
                        .ok_or_else(|| params("unknown_session", "session does not exist"))?;
                    if let Some(job) = session.job.as_ref().filter(|job| job.id == job_id) {
                        if job.active {
                            job.cancel.cancel();
                        }
                        job.done.subscribe()
                    } else if session
                        .accepted
                        .as_ref()
                        .is_some_and(|accepted| accepted.job_id == job_id)
                    {
                        return Ok(CallToolResult::structured(
                            json!({"session_id":session_id,"job_id":job_id,"phase":Phase::Accepted}),
                        ));
                    } else {
                        return Err(params("unknown_job", "job is no longer retained"));
                    }
                };
                let phase = (*done.wait_for(|phase| phase.is_some()).await.map_err(|_| {
                    ErrorData::internal_error("job completion channel closed", None)
                })?)
                .ok_or_else(|| ErrorData::internal_error("job has no terminal phase", None))?;
                Ok(CallToolResult::structured(
                    json!({"session_id":session_id,"job_id":job_id,"phase":phase}),
                ))
            }
            SessionAction::Close { session_id } => {
                let pending = {
                    let mut project = self.shared.project();
                    let session = project
                        .sessions
                        .get_mut(&session_id)
                        .ok_or_else(|| params("unknown_session", "session does not exist"))?;
                    session.closing = true;
                    session.job.as_ref().filter(|job| job.active).map(|job| {
                        job.cancel.cancel();
                        job.done.subscribe()
                    })
                };
                if let Some(mut done) = pending {
                    let _ = done.wait_for(|done| done.is_some()).await;
                }
                self.shared.project().sessions.remove(&session_id);
                Ok(CallToolResult::structured(
                    json!({"session_id":session_id,"closed":true}),
                ))
            }
        }
    }

    #[tool(
        description = "Append include directories in order, like -I<path>, for the session's next verification. Relative paths use the server root. Invalidates all verification caches; active jobs reject updates."
    )]
    async fn add_include_paths(
        &self,
        Parameters(input): Parameters<IncludePathsInput>,
    ) -> Result<CallToolResult, ErrorData> {
        self.add_compile_options(input.session_id, input.include_paths, Vec::new())
    }

    #[tool(
        description = "Append preprocessor definitions in order, like -DFOO or -DFOO=bar, for the session's next verification. Invalidates all verification caches; active jobs reject updates."
    )]
    async fn add_preprocessor_definition(
        &self,
        Parameters(input): Parameters<PreprocessorDefinitionInput>,
    ) -> Result<CallToolResult, ErrorData> {
        self.add_compile_options(input.session_id, Vec::new(), input.defines)
    }

    #[tool(
        description = "Reserve a background verification job against the accepted revision. Changes never patch a rejected candidate."
    )]
    async fn pal_verify(
        &self,
        Parameters(input): Parameters<VerifyInput>,
    ) -> Result<CallToolResult, ErrorData> {
        let (root, job_id, cancel, done, sources, includes, defines, proofs) = {
            let mut project = self.shared.project();
            let root = project
                .root
                .clone()
                .ok_or_else(|| params("no_root", "call new_root before opening a session"))?;
            let session = project
                .sessions
                .get_mut(&input.session_id)
                .filter(|session| !session.closing)
                .ok_or_else(|| params("unknown_session", "session does not exist"))?;
            if session.revision != input.base_revision {
                return Err(params(
                    "stale_revision",
                    "base_revision is not the accepted revision",
                ));
            }
            if session.job.as_ref().is_some_and(|job| job.active) {
                return Err(params("session_busy", "session already has an active job"));
            }
            let sources = session
                .accepted
                .as_ref()
                .map(|accepted| accepted.indexed.snapshot.sources.clone())
                .unwrap_or_default();
            workspace::validate_changes(&root, &sources, &input.changes).map_err(invalid)?;
            let job_id = JobId::next()?;
            let cancel = Cancellation::new();
            let done = watch::channel(None).0;
            session.job = Some(Job {
                id: job_id.clone(),
                cancel: cancel.clone(),
                done: done.clone(),
                indexed: None,
                active: true,
                started: Instant::now(),
                last_update: Instant::now(),
                pending_message: String::new(),
            });
            session.status.job_id = Some(job_id.clone());
            session.status.base_revision = input.base_revision;
            session.status.phase = Phase::Queued;
            session.status.elapsed_ms = 0;
            session.status.message.clear();
            session.status.verification_cache_hit = false;
            session.status.diagnostics.clear();
            session.status.error = None;
            self.shared.publish(session);
            (
                root,
                job_id,
                cancel,
                done,
                sources,
                session.includes.clone(),
                session.defines.clone(),
                session
                    .accepted
                    .as_ref()
                    .map(|accepted| accepted.proofs.clone()),
            )
        };
        let shared = self.shared.clone();
        let id = input.session_id.clone();
        let job = job_id.clone();
        tokio::spawn(async move {
            let worker_shared = shared.clone();
            let worker_id = id.clone();
            let worker_job = job.clone();
            let worker_cancel = cancel.clone();
            let mut worker = tokio::spawn(async move {
                run_job(
                    worker_shared,
                    root,
                    worker_id,
                    worker_job,
                    sources,
                    input.changes,
                    includes,
                    defines,
                    proofs,
                    worker_cancel,
                )
                .await
            });
            let mut heartbeat = tokio::time::interval(Duration::from_secs(1));
            let result = loop {
                tokio::select! {
                    result = &mut worker => break result.unwrap_or_else(|error| Err(Failure::new("worker_failed", format!("verification worker failed: {error}")))),
                    _ = heartbeat.tick() => {
                        let phase = shared.project().sessions.get(&id).map(|session| session.status.phase);
                        if let Some(phase) = phase { shared.progress(&id, &job, phase, "", false); }
                    }
                }
            };
            let phase = finish_job(&shared, &id, &job, &cancel, result);
            done.send_replace(Some(phase));
        });
        Ok(CallToolResult::structured(
            json!({"session_id":input.session_id,"job_id":job_id,"base_revision":input.base_revision,"status_uri":input.session_id.status_uri()}),
        ))
    }

    #[tool(
        description = "Query frozen Clang definitions, references, direct calls, symbols or hover. Omit job_id to query accepted code."
    )]
    async fn pal_query(
        &self,
        Parameters(input): Parameters<QueryInput>,
    ) -> Result<CallToolResult, ErrorData> {
        let (indexed, revision, job_id, complete) = {
            let project = self.shared.project();
            let session = project
                .sessions
                .get(&input.session_id)
                .filter(|session| !session.closing)
                .ok_or_else(|| params("unknown_session", "session does not exist"))?;
            if let Some(job_id) = &input.job_id {
                if let Some(accepted) = session
                    .accepted
                    .as_ref()
                    .filter(|accepted| accepted.job_id == *job_id)
                {
                    (
                        accepted.indexed.clone(),
                        session.revision,
                        accepted.job_id.clone(),
                        true,
                    )
                } else if let Some(job) = session.job.as_ref().filter(|job| job.id == *job_id) {
                    (
                        job.indexed.clone().ok_or_else(|| {
                            params("index_not_ready", "candidate has not been indexed")
                        })?,
                        session.revision,
                        job.id.clone(),
                        false,
                    )
                } else {
                    return Err(params("unknown_job", "job is no longer retained"));
                }
            } else {
                let accepted = session.accepted.as_ref().ok_or_else(|| {
                    params("no_accepted_revision", "session has no accepted snapshot")
                })?;
                (
                    accepted.indexed.clone(),
                    session.revision,
                    accepted.job_id.clone(),
                    true,
                )
            }
        };
        let data = indexed
            .index
            .query(&indexed.snapshot, &input.query)
            .map_err(invalid)?;
        Ok(CallToolResult::structured(
            json!({"session_id":input.session_id,"accepted_revision":revision,"job_id":job_id,"complete":complete && indexed.index.complete,"data":data}),
        ))
    }
}

fn validate_compile_options(include_paths: &[String], defines: &[String]) -> Result<(), ErrorData> {
    if include_paths
        .iter()
        .chain(defines)
        .any(|value| value.contains('\0'))
    {
        return Err(params(
            "invalid_path",
            "include paths and definitions cannot contain NUL",
        ));
    }
    Ok(())
}

struct JobSuccess {
    indexed: Arc<Indexed>,
    result: verify::VerificationResult,
    _permit: tokio::sync::OwnedSemaphorePermit,
}

async fn run_job(
    shared: Arc<Shared>,
    root: PathBuf,
    id: SessionId,
    job: JobId,
    sources: Vec<ManagedSource>,
    changes: Vec<Change>,
    includes: Vec<PathBuf>,
    defines: Vec<String>,
    proofs: Option<Arc<VerifiedArtifacts>>,
    cancel: Cancellation,
) -> workspace::Result<JobSuccess> {
    let _permit = tokio::select! {
        _ = cancel.cancelled() => return Err(Failure::new("cancelled", "verification cancelled while queued")),
        permit = shared.verifier.gate.clone().acquire_owned() => permit.map_err(|_| Failure::new("worker_failed", "verifier queue closed"))?,
    };
    cancel.check()?;
    shared.progress(
        &id,
        &job,
        Phase::Snapshotting,
        "preparing frozen sources and semantic index",
        true,
    );
    let tools = shared.verifier.toolchain.clone();
    let indexed = tokio::task::spawn_blocking(move || {
        let mut snapshot = workspace::prepare(root, sources, changes, includes, defines)?;
        let index = navigation::index(&mut snapshot, &tools)?;
        Ok::<_, Failure>(Arc::new(Indexed {
            snapshot: Arc::new(snapshot),
            index: Arc::new(index),
        }))
    })
    .await
    .map_err(|error| Failure::new("worker_failed", format!("snapshot worker failed: {error}")))??;
    {
        let mut project = shared.project();
        let session = project
            .sessions
            .get_mut(&id)
            .ok_or_else(|| Failure::new("cancelled", "session closed"))?;
        let active = session
            .job
            .as_mut()
            .filter(|active| active.id == job)
            .ok_or_else(|| Failure::new("cancelled", "job no longer owns the session"))?;
        active.indexed = Some(indexed.clone());
        session.status.diagnostics = indexed.index.diagnostics.clone();
        shared.publish(session);
    }
    cancel.check()?;
    let progress_shared = shared.clone();
    let progress_id = id.clone();
    let progress_job = job.clone();
    let progress = verify::Progress::new(move |phase: &str, message: &str| {
        let phase = if phase == "translating" {
            Phase::Translating
        } else {
            Phase::Verifying
        };
        progress_shared.progress(&progress_id, &progress_job, phase, message, false);
    });
    let result = shared
        .verifier
        .verify(
            indexed.snapshot.clone(),
            indexed.index.clone(),
            proofs,
            cancel.clone(),
            progress,
            &id.status_uri(),
        )
        .await;
    cancel.check()?;
    Ok(JobSuccess {
        indexed,
        result,
        _permit,
    })
}

fn finish_job(
    shared: &Shared,
    id: &SessionId,
    job_id: &JobId,
    cancel: &Cancellation,
    result: workspace::Result<JobSuccess>,
) -> Phase {
    let mut _publication_permit = None;
    let mut project = shared.project();
    let Some(session) = project.sessions.get_mut(id) else {
        return Phase::Cancelled;
    };
    if !session
        .job
        .as_ref()
        .is_some_and(|job| job.id == *job_id && job.active)
    {
        return Phase::Cancelled;
    }
    let failure = if cancel.is_cancelled() || session.closing {
        Some(Failure::new("cancelled", "verification cancelled"))
    } else {
        match result {
            Err(failure) => Some(failure),
            Ok(success) => {
                _publication_permit = Some(success._permit);
                session.status.diagnostics = success.result.diagnostics;
                session.status.verification_cache_hit = success.result.cache_hit;
                if let Some(failure) = success.result.failure {
                    Some(failure)
                } else if let Some(proofs) = success.result.artifacts {
                    match session.revision.0.checked_add(1) {
                        Some(revision) => {
                            session.revision = Revision(revision);
                            session.accepted = Some(Accepted {
                                job_id: job_id.clone(),
                                indexed: success.indexed,
                                proofs,
                            });
                            session.status.accepted_revision = session.revision;
                            None
                        }
                        None => Some(Failure::new("worker_failed", "accepted revision exhausted")),
                    }
                } else {
                    Some(Failure::new(
                        "worker_failed",
                        "verifier returned no accepted proof artifacts",
                    ))
                }
            }
        }
    };
    if let Some(failure) = failure {
        session.status.phase = if failure.code == "cancelled" {
            Phase::Cancelled
        } else {
            Phase::Failed
        };
        session.status.message = public_text(
            session.job.as_ref().and_then(|job| job.indexed.as_deref()),
            &failure.message,
        );
        session.status.error = Some(Failure::new(&failure.code, session.status.message.clone()));
    } else {
        session.status.phase = Phase::Accepted;
        session.status.message = "verification accepted".to_owned();
        session.status.error = None;
    }
    if let Some(job) = &mut session.job {
        job.active = false;
    }
    shared.publish(session);
    session.status.phase
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for PalMcpServer {
    fn get_info(&self) -> ServerConfig {
        ServerConfig::new(
            ServerCapabilities::builder()
                .enable_tools()
                .enable_resources()
                .enable_resources_subscribe()
                .build(),
        )
        .with_server_info(Implementation::new("pal", env!("CARGO_PKG_VERSION")))
    }
    async fn list_resources(
        &self,
        _: Option<PaginatedRequestParams>,
        _: RequestContext<RoleServer>,
    ) -> Result<ListResourcesResult, ErrorData> {
        let resources = self
            .shared
            .project()
            .sessions
            .keys()
            .map(|id| {
                Resource::new(id.status_uri(), format!("PAL session {} status", id.0))
                    .with_mime_type("application/json")
            })
            .collect();
        let mut result = ListResourcesResult::default();
        result.resources = resources;
        Ok(result)
    }
    async fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        _: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResponse, ErrorData> {
        let text = {
            let project = self.shared.project();
            let session = project
                .sessions
                .values()
                .find(|session| session.status.session_id.status_uri() == request.uri)
                .ok_or_else(|| {
                    ErrorData::resource_not_found(
                        "PAL session status resource does not exist",
                        None,
                    )
                })?;
            serde_json::to_string(&session.status)
                .map_err(|error| ErrorData::internal_error(error.to_string(), None))?
        };
        Ok(ReadResourceResult::new(vec![
            ResourceContents::text(text, request.uri).with_mime_type("application/json"),
        ])
        .into())
    }
    fn accepted_subscription_filter(
        &self,
        requested: &SubscriptionFilter,
    ) -> Option<SubscriptionFilter> {
        let uris = self.shared.existing_uris(
            requested
                .resource_subscriptions
                .as_deref()
                .unwrap_or_default(),
        );
        Some(
            SubscriptionFilter::builder()
                .resource_subscriptions(uris)
                .build(),
        )
    }
    async fn listen(&self, context: SubscriptionContext) -> Result<(), ErrorData> {
        let mut receiver = self.shared.updates.subscribe();
        let accepted = context
            .accepted()
            .resource_subscriptions
            .clone()
            .unwrap_or_default();
        if self.shared.existing_uris(&accepted).is_empty() {
            return Ok(());
        }
        for uri in self.shared.existing_uris(&accepted) {
            if context.sink().notify_resource_updated(uri).await.is_err() {
                return Ok(());
            }
        }
        loop {
            let uris = tokio::select! {
                _ = context.cancelled() => return Ok(()),
                update = receiver.recv() => match update {
                    Ok(uri) => if accepted.contains(&uri) { self.shared.existing_uris(&[uri]) } else { Vec::new() },
                    Err(broadcast::error::RecvError::Lagged(_)) => self.shared.existing_uris(&accepted),
                    Err(broadcast::error::RecvError::Closed) => return Ok(()),
                }
            };
            if self.shared.existing_uris(&accepted).is_empty() {
                return Ok(());
            }
            for uri in uris {
                if context.sink().notify_resource_updated(uri).await.is_err() {
                    return Ok(());
                }
            }
        }
    }
}

fn params(reason: &str, message: &str) -> ErrorData {
    ErrorData::invalid_params(message.to_owned(), Some(json!({"reason":reason})))
}
fn invalid(failure: Failure) -> ErrorData {
    ErrorData::invalid_params(failure.message, Some(json!({"reason":failure.code})))
}
fn public_text(indexed: Option<&Indexed>, message: &str) -> String {
    let mut message = message.to_owned();
    if let Some(indexed) = indexed {
        let snapshot = &indexed.snapshot;
        message = message.replace(
            snapshot.mirror().to_string_lossy().as_ref(),
            snapshot.root.to_string_lossy().as_ref(),
        );
        message = message
            .replace(&format!("{}/", snapshot.out().display()), "")
            .replace(&format!("{}/", snapshot.checked().display()), "");
        message = message.replace(
            snapshot.storage.path().to_string_lossy().as_ref(),
            "<candidate>",
        );
    }
    let mut length = message.len().min(1024);
    while !message.is_char_boundary(length) {
        length -= 1;
    }
    message.truncate(length);
    message
}
