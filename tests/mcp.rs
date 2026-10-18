#![cfg(feature = "mcp")]

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use lsp_types::{
    CallHierarchyIncomingCall, CallHierarchyOutgoingCall, DocumentSymbol, Hover, Location,
    Position, Range,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

const PROTOCOL: &str = "2026-07-28";
const SUBSCRIPTION_ID: &str = "io.modelcontextprotocol/subscriptionId";
const JOB_TIMEOUT: Duration = Duration::from_secs(900);
const RPC_TIMEOUT: Duration = Duration::from_secs(120);
const EXAMPLE_PATH: &str = "examples/mcp_example.c";
const HELPER: &str =
    "\nint use_max(int x)\n    _ensures(return >= x)\n{\n    return max(x, x);\n}\n";
const HEADER: &str = "#ifndef MCP_CONSTANTS_H\n#define MCP_CONSTANTS_H\n#include \"pal.h\"\n#define HEADER_VALUE 1\nstatic inline int header_value(void)\n    _ensures(return == HEADER_VALUE)\n{ return HEADER_VALUE; }\n#endif\n";
const HEADER_ROOT: &str = "#include \"constants.h\"\nint read_header(void)\n    _ensures(return == HEADER_VALUE)\n{ return header_value(); }\n";
const NAVIGATION: &str = "#include \"pal.h\"\nint nav_target(int x) _ensures(return == x) { return x; }\nint nav_shadow(int x) _ensures(return == x) {\n    int y = x;\n    { int x = y; /* 𝄞 */ y = nav_target(x); }\n    return y;\n}\nint nav_pointer(int x) {\n    int (*fp)(int) = nav_target;\n    return fp(x);\n}\n";

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(transparent)]
struct SessionId(String);
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(transparent)]
struct JobId(String);
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(transparent)]
struct Revision(u64);
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
struct RequestId(u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SubscriptionId(RequestId);
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(transparent)]
struct StatusUri(String);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ProcessId(u32);
#[derive(Clone, Copy)]
struct TraceOffset(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BatchCount(usize);
struct Trace(String);

#[derive(Debug, Deserialize)]
struct Session {
    root: PathBuf,
    session_id: SessionId,
    accepted_revision: Revision,
    status_uri: StatusUri,
}
#[derive(Debug, Deserialize)]
struct Job {
    session_id: SessionId,
    job_id: JobId,
    base_revision: Revision,
    status_uri: StatusUri,
}

// One wire reader routes by ID; long-lived listen requests must not block ordinary RPCs.
struct Client {
    root: PathBuf,
    child: Child,
    stdin: Option<BufWriter<ChildStdin>>,
    wire: Receiver<Result<Value, String>>,
    reader: Option<JoinHandle<()>>,
    responses: BTreeMap<RequestId, Value>,
    notifications: Vec<Value>,
    next_id: RequestId,
    stderr: PathBuf,
    stopped: bool,
}

impl Client {
    fn start(root: &Path, wrapper: &Wrapper, repo: &Path) -> Self {
        let stderr = wrapper.directory.path().join("server.stderr");
        let mut command = Command::new(env!("CARGO_BIN_EXE_pal"));
        command
            .args(["mcp", "--fstar-exe"])
            .arg(&wrapper.executable)
            .arg("--pulse-dir")
            .arg(repo.join("pulse"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(File::create(&stderr).expect("create server stderr"));
        let mut child = command
            .spawn()
            .expect("start feature-enabled PAL executable");
        let stdin = BufWriter::new(child.stdin.take().unwrap());
        let stdout = child.stdout.take().unwrap();
        let (tx, wire) = mpsc::channel();
        let reader = thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                let value = line.map_err(|error| error.to_string()).and_then(|line| {
                    serde_json::from_str(&line)
                        .map_err(|error| format!("non-JSON MCP stdout: {error}: {line}"))
                });
                if tx.send(value).is_err() {
                    return;
                }
            }
        });
        let mut client = Self {
            root: root.to_path_buf(),
            child,
            stdin: Some(stdin),
            wire,
            reader: Some(reader),
            responses: BTreeMap::new(),
            notifications: Vec::new(),
            next_id: RequestId(1),
            stderr,
            stopped: false,
        };
        let initialized = client.rpc("initialize", json!({"protocolVersion":PROTOCOL,"capabilities":{},"clientInfo":{"name":"pal-real-integration","version":"1"}}));
        assert!(initialized.get("error").is_none(), "{initialized}");
        let capabilities = &initialized["result"]["capabilities"];
        assert!(capabilities["tools"].is_object(), "{initialized}");
        assert_eq!(
            capabilities["resources"]["subscribe"], true,
            "{initialized}"
        );
        client.notify("notifications/initialized", json!({}));
        let templates = client.rpc("resources/templates/list", json!({}));
        assert!(
            templates["result"]["resourceTemplates"]
                .as_array()
                .unwrap()
                .iter()
                .any(
                    |template| template["uriTemplate"] == "pal://sessions/{session_id}/status"
                        && template["mimeType"] == "application/json"
                ),
            "{templates}"
        );
        client
    }

    fn send(&mut self, method: &str, mut params: Value, id: Option<RequestId>) {
        // RMCP 3.5.1 negotiates legacy initialize, but modern requests select the draft per-message.
        if id.is_some() && method != "initialize" {
            params["_meta"] = json!({"io.modelcontextprotocol/protocolVersion":PROTOCOL,"io.modelcontextprotocol/clientCapabilities":{}});
        }
        let mut request = json!({"jsonrpc":"2.0","method":method,"params":params});
        if let Some(id) = id {
            request["id"] = json!(id);
        }
        let stdin = self.stdin.as_mut().expect("server stdin still open");
        serde_json::to_writer(&mut *stdin, &request).expect("write MCP request");
        stdin.write_all(b"\n").unwrap();
        stdin.flush().unwrap();
    }

    fn request(&mut self, method: &str, params: Value) -> RequestId {
        let id = self.next_id;
        self.next_id.0 += 1;
        self.send(method, params, Some(id));
        id
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(method, params, None);
    }

    fn receive(&mut self, timeout: Duration) {
        let message = self
            .wire
            .recv_timeout(timeout)
            .unwrap_or_else(|error| {
                panic!(
                    "MCP read failed: {error}; server stderr:\n{}",
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                )
            })
            .unwrap_or_else(|error| panic!("{error}"));
        if let Some(id) = message.get("id") {
            let id: RequestId = serde_json::from_value(id.clone()).expect("numeric response ID");
            assert!(
                self.responses.insert(id, message).is_none(),
                "duplicate MCP response"
            );
        } else {
            self.notifications.push(message);
        }
    }

    fn response(&mut self, id: RequestId) -> Value {
        let deadline = Instant::now() + RPC_TIMEOUT;
        loop {
            if let Some(response) = self.responses.remove(&id) {
                return response;
            }
            self.receive(deadline.saturating_duration_since(Instant::now()));
        }
    }

    fn rpc(&mut self, method: &str, params: Value) -> Value {
        let id = self.request(method, params);
        self.response(id)
    }

    fn tool_response(&mut self, name: &str, arguments: Value) -> Value {
        self.rpc("tools/call", json!({"name":name,"arguments":arguments}))
    }

    fn tool(&mut self, name: &str, arguments: Value) -> Value {
        let response = self.tool_response(name, arguments);
        assert!(response.get("error").is_none(), "{response}");
        assert_ne!(response["result"]["isError"], true, "{response}");
        response["result"]
            .get("structuredContent")
            .unwrap_or_else(|| panic!("tool result is not structured: {response}"))
            .clone()
    }

    fn open(&mut self, include_paths: &[&str]) -> Session {
        let session: Session = serde_json::from_value(self.tool(
            "pal_session",
            json!({"action":"open","root":self.root,"include_paths":include_paths}),
        ))
        .unwrap();
        assert_eq!(session.root, self.root);
        let status = self.status(&session.status_uri);
        assert_eq!(
            status,
            json!({"session_id":session.session_id,"job_id":null,"base_revision":0,"accepted_revision":0,"sequence":0,"phase":"idle","elapsed_ms":0,"message":"","verification_cache_hit":false,"diagnostics":{},"error":null})
        );
        let resources = self.rpc("resources/list", json!({}));
        assert!(
            resources["result"]["resources"]
                .as_array()
                .unwrap()
                .iter()
                .any(|resource| resource["uri"] == json!(session.status_uri)
                    && resource["mimeType"] == "application/json")
        );
        session
    }

    fn status(&mut self, uri: &StatusUri) -> Value {
        let response = self.rpc("resources/read", json!({"uri":uri}));
        assert!(response.get("error").is_none(), "{response}");
        let contents = &response["result"]["contents"][0];
        assert_eq!(contents["mimeType"], "application/json");
        assert_eq!(contents["uri"], json!(uri));
        serde_json::from_str(contents["text"].as_str().unwrap()).unwrap()
    }

    fn listen(&mut self, uri: &StatusUri) -> SubscriptionId {
        let id = SubscriptionId(self.request(
            "subscriptions/listen",
            json!({"notifications":{"resourceSubscriptions":[uri]}}),
        ));
        let deadline = Instant::now() + RPC_TIMEOUT;
        loop {
            if self.notifications.iter().any(|event| {
                event["method"] == "notifications/subscriptions/acknowledged"
                    && event["params"]["_meta"][SUBSCRIPTION_ID] == json!(id.0)
            }) {
                return id;
            }
            assert!(
                !self.responses.contains_key(&id.0),
                "listen returned before acknowledgement: {:?}",
                self.responses
            );
            self.receive(deadline.saturating_duration_since(Instant::now()));
        }
    }

    fn updated(&self, since: usize, subscription: SubscriptionId, uri: &StatusUri) -> bool {
        self.notifications[since..].iter().any(|event| {
            event["method"] == "notifications/resources/updated"
                && event["params"]["uri"] == json!(uri)
                && event["params"]["_meta"][SUBSCRIPTION_ID] == json!(subscription.0)
        })
    }

    fn await_updates(&mut self, since: usize, subscriptions: &[SubscriptionId], uri: &StatusUri) {
        let deadline = Instant::now() + RPC_TIMEOUT;
        while !subscriptions.iter().all(|&id| self.updated(since, id, uri)) {
            self.receive(deadline.saturating_duration_since(Instant::now()));
        }
    }

    fn submit(&mut self, session: &Session, changes: Value) -> Job {
        let start = Instant::now();
        let job: Job = serde_json::from_value(self.tool("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":changes}))).unwrap();
        assert!(
            start.elapsed() < Duration::from_secs(5),
            "pal_verify must reserve, not await verification: {:?}",
            start.elapsed()
        );
        assert_eq!(job.session_id, session.session_id);
        assert_eq!(job.base_revision, session.accepted_revision);
        assert_eq!(job.status_uri, session.status_uri);
        job
    }

    fn terminal(&mut self, session: &mut Session, job: &Job) -> Value {
        let deadline = Instant::now() + JOB_TIMEOUT;
        let mut last_sequence = 0;
        loop {
            let status = self.status(&session.status_uri);
            assert_eq!(status["job_id"], json!(job.job_id));
            let sequence = status["sequence"].as_u64().unwrap();
            assert!(
                sequence >= last_sequence,
                "status sequence regressed: {status}"
            );
            last_sequence = sequence;
            assert!(status["message"].as_str().unwrap().len() <= 1024);
            match status["phase"].as_str().unwrap() {
                "accepted" => {
                    assert_eq!(
                        status["accepted_revision"],
                        session.accepted_revision.0 + 1,
                        "{status}"
                    );
                    assert!(status["error"].is_null(), "{status}");
                    session.accepted_revision.0 += 1;
                    return status;
                }
                "failed" | "cancelled" => {
                    assert_eq!(
                        status["accepted_revision"],
                        json!(session.accepted_revision),
                        "failed candidate advanced acceptance: {status}"
                    );
                    return status;
                }
                "queued" | "snapshotting" | "translating" | "verifying" => {}
                phase => panic!("unexpected job phase {phase}: {status}"),
            }
            assert!(
                Instant::now() < deadline,
                "verification timed out: {status}"
            );
            thread::sleep(Duration::from_millis(50));
        }
    }

    fn run(
        &mut self,
        session: &mut Session,
        changes: Value,
        wrapper: &Wrapper,
    ) -> (Job, Value, Trace) {
        let mark = wrapper.mark();
        let job = self.submit(session, changes);
        let status = self.terminal(session, &job);
        (job, status, wrapper.trace(mark))
    }

    fn query(&mut self, session: &Session, job: Option<&JobId>, query: Value) -> Value {
        let mut arguments = json!({"session_id":session.session_id,"query":query});
        if let Some(job) = job {
            arguments["job_id"] = json!(job);
        }
        let result = self.tool("pal_query", arguments);
        assert_eq!(result["session_id"], json!(session.session_id));
        assert_eq!(
            result["accepted_revision"],
            json!(session.accepted_revision)
        );
        if let Some(job) = job {
            assert_eq!(result["job_id"], json!(job));
        }
        result
    }

    fn close(&mut self, session: &Session) {
        assert_eq!(
            self.tool(
                "pal_session",
                json!({"action":"close","session_id":session.session_id})
            ),
            json!({"session_id":session.session_id,"closed":true})
        );
        let response = self.rpc("resources/read", json!({"uri":session.status_uri}));
        assert!(
            response.get("error").is_some(),
            "closed status resource is still readable: {response}"
        );
        let resources = self.rpc("resources/list", json!({}));
        assert!(
            !resources["result"]["resources"]
                .as_array()
                .unwrap()
                .iter()
                .any(|resource| resource["uri"] == json!(session.status_uri))
        );
    }

    fn shutdown(&mut self) {
        self.stdin.take();
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(
                    status.success(),
                    "MCP shutdown failed: {status}; {}",
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                );
                break;
            }
            assert!(
                Instant::now() < deadline,
                "MCP transport shutdown did not join workers"
            );
            thread::sleep(Duration::from_millis(20));
        }
        self.stopped = true;
        if let Some(reader) = self.reader.take() {
            reader.join().expect("wire reader panicked");
        }
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        if self.stopped {
            return;
        }
        self.stdin.take();
        // Even assertions during a solver run must not orphan PAL, F*, or solver children.
        let mut processes = descendants(ProcessId(self.child.id()));
        let deadline = Instant::now() + Duration::from_secs(10);
        while Instant::now() < deadline {
            if self.child.try_wait().ok().flatten().is_some() {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }
        processes.extend(descendants(ProcessId(self.child.id())));
        for pid in processes.iter().rev() {
            if process_alive(*pid) {
                let _ = Command::new("kill")
                    .args(["-KILL", &pid.0.to_string()])
                    .status();
            }
        }
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
        if thread::panicking() {
            eprintln!(
                "PAL MCP stderr:\n{}",
                fs::read_to_string(&self.stderr).unwrap_or_default()
            );
        }
    }
}

struct Wrapper {
    directory: tempfile::TempDir,
    executable: PathBuf,
    trace: PathBuf,
    batches: PathBuf,
}

impl Wrapper {
    fn new() -> Self {
        assert!(
            cfg!(target_os = "linux"),
            "real process-descendant/FIFO regression requires Linux /proc and POSIX tools; no scenarios are skipped"
        );
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("fstar-qa");
        let trace = directory.path().join("trace.log");
        let batches = directory.path().join("batches.log");
        let script = format!(
            r#"#!/bin/sh
set -u
case "${{1-}}" in
  --version|--locate_lib|--expand_include) exec fstar.exe "$@" ;;
esac
qa={qa}
printf '%s\n' "$$ $*" >> "$qa/batches.log"
if [ -f "$qa/arm" ]; then
  rm "$qa/arm"
  sleep 600 &
  sentinel=$!
  printf '%s %s\n' "$$" "$sentinel" > "$qa/ready"
  IFS= read -r release < "$qa/barrier"
  kill "$sentinel"
  wait "$sentinel" 2>/dev/null || :
fi
fstar.exe --debug CheckedFiles "$@" > "$qa/root.$$.stdout" 2> "$qa/root.$$.stderr" &
verifier=$!
printf '%s %s\n' "$$" "$verifier" >> "$qa/children.log"
wait "$verifier"
result=$?
cat "$qa/root.$$.stdout" "$qa/root.$$.stderr" >> "$qa/trace.log"
cat "$qa/root.$$.stdout"
cat "$qa/root.$$.stderr" >&2
exit "$result"
"#,
            qa = shell_quote(directory.path())
        );
        fs::write(&executable, script).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
        }
        fs::write(&trace, "").unwrap();
        fs::write(&batches, "").unwrap();
        assert!(
            Command::new("mkfifo")
                .arg(directory.path().join("barrier"))
                .status()
                .expect("mkfifo is required for real cancellation QA")
                .success()
        );
        Self {
            directory,
            executable,
            trace,
            batches,
        }
    }
    fn mark(&self) -> TraceOffset {
        TraceOffset(fs::read(&self.trace).unwrap().len())
    }
    fn trace(&self, mark: TraceOffset) -> Trace {
        let trace = fs::read(&self.trace).unwrap();
        Trace(String::from_utf8(trace[mark.0..].to_vec()).unwrap())
    }
    fn batches(&self) -> BatchCount {
        BatchCount(fs::read_to_string(&self.batches).unwrap().lines().count())
    }
    fn arm(&self) {
        let ready = self.directory.path().join("ready");
        if ready.exists() {
            fs::remove_file(ready).unwrap();
        }
        fs::write(
            self.directory.path().join("arm"),
            "pause before delegating to real F*\n",
        )
        .unwrap();
    }
    fn paused(&self) -> Vec<ProcessId> {
        let deadline = Instant::now() + RPC_TIMEOUT;
        loop {
            if let Ok(ready) = fs::read_to_string(self.directory.path().join("ready")) {
                let pids: Vec<_> = ready
                    .split_whitespace()
                    .map(|pid| ProcessId(pid.parse().unwrap()))
                    .collect();
                if pids.len() == 2 {
                    return pids;
                }
            }
            assert!(
                Instant::now() < deadline,
                "real F* wrapper never reached cancellation barrier"
            );
            thread::sleep(Duration::from_millis(20));
        }
    }
}

impl Trace {
    fn filenames<'a>(&'a self, marker: &'a str) -> impl Iterator<Item = &'a str> + 'a {
        self.0
            .lines()
            .filter_map(move |line| line.strip_prefix(marker))
            .filter_map(|line| line.split_whitespace().next())
            .filter_map(|path| Path::new(path).file_name()?.to_str())
    }
    fn reused(&self, source: &str) {
        let checked = format!("{source}.checked");
        assert!(
            self.filenames("Successfully loaded module from checked file ")
                .any(|name| name == checked),
            "no native checked-file load for {source}"
        );
        // Match only the stored filename, never a dependency later on the same trace line.
        assert!(
            !self
                .filenames("Storing checked file for ")
                .any(|name| name == source),
            "unchanged unit was rechecked: {source}"
        );
    }
    fn reused_module(&self, module: &str) {
        self.reused(&format!("{module}.fsti"));
        self.reused(&format!("{module}.fst"));
    }
    fn stored(&self, source: &str) {
        assert!(
            self.filenames("Storing checked file for ")
                .any(|name| name == source),
            "changed proof was not checked: {source}"
        );
    }
}

fn shell_quote(path: &Path) -> String {
    format!("'{}'", path.to_str().unwrap().replace('\'', "'\\''"))
}

fn descendants(parent: ProcessId) -> Vec<ProcessId> {
    let mut result = Vec::new();
    let mut pending = vec![parent];
    while let Some(pid) = pending.pop() {
        let Ok(tasks) = fs::read_dir(format!("/proc/{}/task", pid.0)) else {
            continue;
        };
        for task in tasks.flatten() {
            if let Ok(children) = fs::read_to_string(task.path().join("children")) {
                for child in children
                    .split_whitespace()
                    .filter_map(|pid| pid.parse().ok())
                    .map(ProcessId)
                {
                    if !result.contains(&child) {
                        result.push(child);
                        pending.push(child);
                    }
                }
            }
        }
    }
    result
}

fn process_alive(pid: ProcessId) -> bool {
    let Ok(stat) = fs::read_to_string(format!("/proc/{}/stat", pid.0)) else {
        return false;
    };
    // A reparented zombie has exited; it cannot retain a solver or execute more work.
    !stat
        .rsplit_once(") ")
        .is_some_and(|(_, fields)| fields.starts_with("Z "))
}

fn assert_exited(pids: &[ProcessId]) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while pids.iter().any(|pid| process_alive(*pid)) {
        assert!(
            Instant::now() < deadline,
            "cancellation left live descendants: {:?}",
            pids.iter()
                .filter(|pid| process_alive(**pid))
                .collect::<Vec<_>>()
        );
        thread::sleep(Duration::from_millis(20));
    }
}

fn invalid(response: &Value, reason: &str) {
    assert_eq!(response["error"]["code"], -32602, "{response}");
    assert_eq!(response["error"]["data"]["reason"], reason, "{response}");
}
fn accepted(status: &Value) {
    assert_eq!(status["phase"], "accepted", "{status}");
}
fn failed(status: &Value, reason: &str) {
    assert_eq!(status["phase"], "failed", "{status}");
    assert_eq!(status["error"]["code"], reason, "{status}");
}
fn replace(path: &str, code: &str) -> Value {
    json!({"op":"replace","path":path,"code":code})
}
fn append(path: &str, code: &str) -> Value {
    json!({"op":"append","path":path,"code":code})
}
fn reference(path: &str) -> Value {
    json!({"op":"reference","path":path})
}
fn at(code: &str, needle: &str) -> Position {
    position(
        code,
        code.find(needle)
            .unwrap_or_else(|| panic!("missing fixture text {needle}")),
    )
}
fn position(code: &str, offset: usize) -> Position {
    let prefix = &code[..offset];
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    Position::new(
        u32::try_from(prefix.bytes().filter(|&byte| byte == b'\n').count()).unwrap(),
        u32::try_from(code[line_start..offset].encode_utf16().count()).unwrap(),
    )
}
fn name_range(code: &str, needle: &str, name: &str) -> Range {
    let offset = code.find(needle).unwrap();
    assert!(needle.starts_with(name));
    Range::new(position(code, offset), position(code, offset + name.len()))
}
fn query_at(kind: &str, path: &str, point: Position) -> Value {
    json!({"kind":kind,"path":path,"position":point})
}
fn data<T: for<'a> Deserialize<'a>>(result: Value) -> T {
    serde_json::from_value(result["data"].clone())
        .unwrap_or_else(|error| panic!("unexpected LSP shape: {error}: {result}"))
}

fn project_uri(root: &Path, relative: &str) -> String {
    let path = root.join(relative);
    let mut uri = String::from("file://");
    for byte in path.to_str().unwrap().bytes() {
        if byte.is_ascii_alphanumeric() || b"/-._~".contains(&byte) {
            uri.push(char::from(byte));
        } else {
            use std::fmt::Write;
            write!(uri, "%{byte:02X}").unwrap();
        }
    }
    uri
}
fn assert_locations(locations: &[Location], uri: &str, ranges: &[Range]) {
    let expected: Vec<_> = ranges
        .iter()
        .map(|range| json!({"uri":uri,"range":range}))
        .collect();
    assert_eq!(serde_json::to_value(locations).unwrap(), json!(expected));
}
fn assert_public(value: &Value, root: &Path) {
    match value {
        Value::Object(fields) => {
            for (key, value) in fields {
                if key == "uri" && value.as_str().is_some_and(|uri| uri.starts_with("file://")) {
                    let prefix = project_uri(root, "");
                    assert!(
                        value.as_str().unwrap().starts_with(&prefix),
                        "private/non-project URI: {value}"
                    );
                    assert!(
                        !value.as_str().unwrap().contains("/mirror/"),
                        "private mirror URI: {value}"
                    );
                }
                assert_public(value, root);
            }
        }
        Value::Array(values) => {
            for value in values {
                assert_public(value, root);
            }
        }
        Value::String(text) => assert!(
            !text.contains("/checked/") && !text.contains("/mirror/"),
            "private candidate path leaked: {text}"
        ),
        _ => {}
    }
}

fn helper_navigation(client: &mut Client, session: &Session, source: &str, root: &Path) {
    let uri = project_uri(root, EXAMPLE_PATH);
    let call = at(source, "max(x, x)");
    let target_range = name_range(source, "max(int a", "max");
    let call_range = name_range(source, "max(x, x)", "max");
    let definition = client.query(session, None, query_at("definition", EXAMPLE_PATH, call));
    assert_eq!(definition["complete"], true);
    assert_public(&definition, root);
    assert_locations(&data::<Vec<Location>>(definition), &uri, &[target_range]);
    let references: Vec<Location> =
        data(client.query(session, None, query_at("references", EXAMPLE_PATH, call)));
    assert_locations(&references, &uri, &[call_range]);
    let mut with_declaration = query_at("references", EXAMPLE_PATH, call);
    with_declaration["include_declaration"] = json!(true);
    let references: Vec<Location> = data(client.query(session, None, with_declaration));
    assert_locations(&references, &uri, &[target_range, call_range]);
    let callers: Vec<CallHierarchyIncomingCall> = data(client.query(
        session,
        None,
        query_at("callers", EXAMPLE_PATH, at(source, "max(int a")),
    ));
    assert_eq!(callers.len(), 1);
    assert_eq!(callers[0].from.name, "use_max");
    assert_eq!(callers[0].from.uri.as_str(), uri);
    assert_eq!(callers[0].from_ranges, vec![call_range]);
    let callees: Vec<CallHierarchyOutgoingCall> = data(client.query(
        session,
        None,
        query_at("callees", EXAMPLE_PATH, at(source, "use_max(int")),
    ));
    assert_eq!(callees.len(), 1);
    assert_eq!(callees[0].to.name, "max");
    assert_eq!(callees[0].to.selection_range, target_range);
    assert_eq!(callees[0].from_ranges, vec![call_range]);
    let hover: Option<Hover> =
        data(client.query(session, None, query_at("hover", EXAMPLE_PATH, call)));
    let hover = serde_json::to_value(hover.expect("Clang max hover")).unwrap();
    assert_eq!(hover["range"], json!(call_range));
    assert!(hover["contents"]["value"].as_str().unwrap().contains("max"));
    assert_public(&hover, root);
    let symbols: Vec<DocumentSymbol> =
        data(client.query(session, None, json!({"kind":"symbols","path":EXAMPLE_PATH})));
    for name in ["swap", "max", "multiply_by_repeated_addition", "use_max"] {
        assert!(
            symbols.iter().any(|symbol| symbol.name == name),
            "missing symbol {name}: {symbols:?}"
        );
    }
}

fn semantic_navigation(client: &mut Client, session: &mut Session, wrapper: &Wrapper, root: &Path) {
    let revision = session.accepted_revision;
    let (job, status, _) = client.run(
        session,
        json!([replace("navigation.c", NAVIGATION)]),
        wrapper,
    );
    assert!(
        matches!(status["phase"].as_str(), Some("accepted" | "failed")),
        "{status}"
    );
    if status["phase"] == "failed" {
        assert!(
            matches!(
                status["error"]["code"].as_str(),
                Some("translation_failed" | "verification_failed")
            ),
            "{status}"
        );
        assert_eq!(session.accepted_revision, revision);
    }
    let uri = project_uri(root, "navigation.c");
    let query = |kind: &str, point| query_at(kind, "navigation.c", point);
    let inner_use = position(
        NAVIGATION,
        NAVIGATION.find("nav_target(x)").unwrap() + "nav_target(".len(),
    );
    let inner_declaration = position(
        NAVIGATION,
        NAVIGATION.find("{ int x = y").unwrap() + "{ int ".len(),
    );
    let inner_range = Range::new(
        inner_declaration,
        Position::new(inner_declaration.line, inner_declaration.character + 1),
    );
    let result = client.query(session, Some(&job.job_id), query("definition", inner_use));
    assert_eq!(result["complete"], status["phase"] == "accepted");
    assert_public(&result, root);
    assert_locations(&data::<Vec<Location>>(result), &uri, &[inner_range]);
    let y_use = position(
        NAVIGATION,
        NAVIGATION.find("return y;").unwrap() + "return ".len(),
    );
    let y_declaration = position(
        NAVIGATION,
        NAVIGATION.find("int y = x").unwrap() + "int ".len(),
    );
    assert_locations(
        &data::<Vec<Location>>(client.query(
            session,
            Some(&job.job_id),
            query("definition", y_use),
        )),
        &uri,
        &[Range::new(
            y_declaration,
            Position::new(y_declaration.line, y_declaration.character + 1),
        )],
    );
    let call_range = name_range(NAVIGATION, "nav_target(x)", "nav_target");
    let raw = NAVIGATION.find("nav_target(x)").unwrap();
    let line_start = NAVIGATION[..raw].rfind('\n').unwrap() + 1;
    assert_eq!(
        usize::try_from(call_range.start.character).unwrap(),
        raw - line_start - 2,
        "non-BMP scalar must consume two, not four, UTF-16 units"
    );
    let target_range = name_range(NAVIGATION, "nav_target(int", "nav_target");
    assert_locations(
        &data::<Vec<Location>>(client.query(
            session,
            Some(&job.job_id),
            query("definition", call_range.start),
        )),
        &uri,
        &[target_range],
    );
    let pointer_reference = name_range(NAVIGATION, "nav_target;", "nav_target");
    assert_locations(
        &data::<Vec<Location>>(client.query(
            session,
            Some(&job.job_id),
            query("definition", pointer_reference.start),
        )),
        &uri,
        &[target_range],
    );
    let refs: Vec<Location> = data(client.query(
        session,
        Some(&job.job_id),
        query("references", target_range.start),
    ));
    assert_locations(&refs, &uri, &[call_range, pointer_reference]);
    let callers: Vec<CallHierarchyIncomingCall> = data(client.query(
        session,
        Some(&job.job_id),
        query("callers", target_range.start),
    ));
    assert_eq!(
        callers.len(),
        1,
        "function-pointer reference must not invent a direct call"
    );
    assert_eq!(callers[0].from.name, "nav_shadow");
    assert_eq!(callers[0].from_ranges, vec![call_range]);
    let callees: Vec<CallHierarchyOutgoingCall> = data(client.query(
        session,
        Some(&job.job_id),
        query("callees", at(NAVIGATION, "nav_shadow(int")),
    ));
    assert_eq!(callees.len(), 1);
    assert_eq!(callees[0].to.name, "nav_target");
    assert_eq!(callees[0].from_ranges, vec![call_range]);
    let pointer_calls: Vec<CallHierarchyOutgoingCall> = data(client.query(
        session,
        Some(&job.job_id),
        query("callees", at(NAVIGATION, "nav_pointer(int")),
    ));
    assert!(
        pointer_calls.is_empty(),
        "indirect call resolved to a fictional direct target: {pointer_calls:?}"
    );
    let hover: Option<Hover> =
        data(client.query(session, Some(&job.job_id), query("hover", call_range.start)));
    assert_eq!(hover.unwrap().range, Some(call_range));
    let mut surrogate = at(NAVIGATION, "𝄞");
    surrogate.character += 1;
    let response = client.tool_response("pal_query", json!({"session_id":session.session_id,"job_id":job.job_id,"query":query("definition", surrogate)}));
    invalid(&response, "invalid_position");
    let response = client.tool_response("pal_query", json!({"session_id":session.session_id,"job_id":job.job_id,"query":query("hover", Position::new(9999, 0))}));
    invalid(&response, "invalid_position");
    let response = client.tool_response("pal_query", json!({"session_id":session.session_id,"job_id":job.job_id,"query":query("hover", Position::new(0, 9999))}));
    invalid(&response, "invalid_position");
}

fn header_navigation(client: &mut Client, session: &Session, root: &Path, value: u32) {
    let query = query_at("definition", "constants.c", at(HEADER_ROOT, "HEADER_VALUE"));
    let definitions: Vec<Location> = data(client.query(session, None, query));
    assert_locations(
        &definitions,
        &project_uri(root, "constants.h"),
        &[name_range(HEADER, "HEADER_VALUE 1", "HEADER_VALUE")],
    );
    let result = client.query(
        session,
        None,
        query_at("hover", "constants.c", at(HEADER_ROOT, "HEADER_VALUE")),
    );
    assert_public(&result, root);
    let hover: Option<Hover> = data(result);
    let text = serde_json::to_value(hover.unwrap()).unwrap();
    assert!(
        text["contents"]["value"]
            .as_str()
            .unwrap()
            .contains(&format!("HEADER_VALUE {value}")),
        "macro hover does not reflect frozen header: {text}"
    );
    let symbols: Vec<DocumentSymbol> = data(client.query(
        session,
        None,
        json!({"kind":"symbols","path":"constants.h"}),
    ));
    assert!(symbols.iter().any(|symbol| symbol.name == "header_value"));
}

fn directory_entries(path: &Path) -> BTreeSet<std::ffi::OsString> {
    fs::read_dir(path)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect()
}

#[test]
fn real_mcp_incremental_verification_navigation_and_lifecycle() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .canonicalize()
        .unwrap();
    let example = fs::read_to_string(repo.join("examples/example.c")).unwrap();
    let example_header = fs::read(repo.join("examples/pal.h")).unwrap();
    let example_entries = directory_entries(&repo.join("examples"));
    let lines: Vec<_> = example.lines().collect();
    assert_eq!(
        lines.len(),
        36,
        "acceptance slices track the unchanged example"
    );
    let swap = lines[..10].join("\n") + "\n";
    let max = "\n".to_owned() + &lines[11..20].join("\n") + "\n";
    let multiplication = "\n".to_owned() + &lines[21..36].join("\n") + "\n";
    let wrapper = Wrapper::new();
    let mut client = Client::start(&repo, &wrapper, &repo);
    let mut session = client.open(&[]);
    let first = client.listen(&session.status_uri);
    let second = client.listen(&session.status_uri);
    assert_ne!(first, second);
    let result = client.tool_response(
        "pal_query",
        json!({"session_id":session.session_id,"query":{"kind":"symbols","path":EXAMPLE_PATH}}),
    );
    invalid(&result, "no_accepted_revision");

    let mut source = swap.clone();
    for (change, previously_accepted) in [
        (replace(EXAMPLE_PATH, &swap), Vec::<&str>::new()),
        (append(EXAMPLE_PATH, &max), vec!["Func_swap"]),
        (
            append(EXAMPLE_PATH, &multiplication),
            vec!["Func_swap", "Func_max"],
        ),
    ] {
        let since = client.notifications.len();
        let mark = wrapper.mark();
        let job = client.submit(&session, json!([change]));
        let progress = client.status(&session.status_uri);
        assert!(
            matches!(
                progress["phase"].as_str(),
                Some("queued" | "snapshotting" | "translating" | "verifying")
            ),
            "job did not expose nonterminal progress: {progress}"
        );
        let status = client.terminal(&mut session, &job);
        accepted(&status);
        assert_eq!(status["verification_cache_hit"], false);
        client.await_updates(since, &[first, second], &session.status_uri);
        let trace = wrapper.trace(mark);
        for module in previously_accepted {
            trace.reused_module(module);
        }
    }
    source.push_str(&max);
    source.push_str(&multiplication);
    let symbols: Vec<DocumentSymbol> = data(client.query(
        &session,
        None,
        json!({"kind":"symbols","path":EXAMPLE_PATH}),
    ));
    for name in ["swap", "max", "multiply_by_repeated_addition"] {
        assert!(symbols.iter().any(|symbol| symbol.name == name));
    }

    let before = wrapper.batches();
    let (cached_job, status, trace) = client.run(&mut session, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(status["verification_cache_hit"], true);
    assert_eq!(wrapper.batches(), before, "full-artifact hit invoked F*");
    assert!(trace.0.is_empty());
    assert_eq!(
        client.tool(
            "pal_session",
            json!({"action":"cancel","session_id":session.session_id,"job_id":cached_job.job_id})
        )["phase"],
        "accepted"
    );
    let stale = client.status(&session.status_uri);
    let response = client.tool_response(
        "pal_verify",
        json!({"session_id":session.session_id,"base_revision":0,"changes":[]}),
    );
    invalid(&response, "stale_revision");
    let response = client.tool_response("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":[replace(EXAMPLE_PATH, &source), replace(EXAMPLE_PATH, &source)]}));
    invalid(&response, "conflicting_changes");
    assert_eq!(
        client.status(&session.status_uri),
        stale,
        "parameter failure reserved a job or published status"
    );

    let (_, status, trace) = client.run(
        &mut session,
        json!([append(EXAMPLE_PATH, HELPER)]),
        &wrapper,
    );
    accepted(&status);
    trace.reused_module("Func_swap");
    trace.reused_module("Func_max");
    source.push_str(HELPER);
    helper_navigation(&mut client, &session, &source, &repo);
    let body = source.replace("if (a <= b)", "if (a < b)");
    let (_, status, trace) = client.run(
        &mut session,
        json!([replace(EXAMPLE_PATH, &body)]),
        &wrapper,
    );
    accepted(&status);
    trace.stored("Func_max.fst");
    trace.reused("Func_max.fsti");
    trace.reused_module("Func_use_max");
    trace.reused_module("Func_swap");
    let strong = body.replace(
        "a <= return && b <= return",
        "a <= return && b <= return && (return == a || return == b)",
    );
    let (accepted_job, status, trace) = client.run(
        &mut session,
        json!([replace(EXAMPLE_PATH, &strong)]),
        &wrapper,
    );
    accepted(&status);
    trace.stored("Func_max.fsti");
    trace.stored("Func_max.fst");
    trace.stored("Func_use_max.fst");
    trace.reused_module("Func_swap");
    let old_query = client.query(
        &session,
        None,
        query_at("hover", EXAMPLE_PATH, at(&strong, "max(x, x)")),
    );
    let invalid_max = format!(
        "{swap}\nint max(int a, int b)\n    _ensures(a <= return && b <= return)\n{{ return a; }}\n{multiplication}{HELPER}"
    );
    let (bad_job, status, _) = client.run(
        &mut session,
        json!([replace(EXAMPLE_PATH, &invalid_max)]),
        &wrapper,
    );
    failed(&status, "verification_failed");
    let uri = project_uri(&repo, EXAMPLE_PATH);
    assert!(
        status["diagnostics"][&uri]
            .as_array()
            .is_some_and(|diagnostics| diagnostics
                .iter()
                .any(|diagnostic| diagnostic["severity"] == 1 && diagnostic["source"] == "F*")),
        "failed proof lacked a C-owned F* diagnostic: {status}"
    );
    assert_public(&status, &repo);
    assert_eq!(
        client.query(
            &session,
            None,
            query_at("hover", EXAMPLE_PATH, at(&strong, "max(x, x)"))
        ),
        old_query,
        "rejected candidate replaced accepted navigation"
    );
    let accepted_query = client.query(
        &session,
        Some(&accepted_job.job_id),
        json!({"kind":"symbols","path":EXAMPLE_PATH}),
    );
    assert_eq!(accepted_query["complete"], true);
    let failed_query = client.query(
        &session,
        Some(&bad_job.job_id),
        json!({"kind":"symbols","path":EXAMPLE_PATH}),
    );
    assert_eq!(failed_query["complete"], false);
    let before = wrapper.batches();
    let (_, status, _) = client.run(
        &mut session,
        json!([replace(EXAMPLE_PATH, &strong)]),
        &wrapper,
    );
    accepted(&status);
    assert_eq!(status["verification_cache_hit"], true);
    assert_eq!(
        wrapper.batches(),
        before,
        "rollback damaged valid accepted proof artifacts"
    );
    let response = client.tool_response("pal_query", json!({"session_id":session.session_id,"job_id":bad_job.job_id,"query":{"kind":"symbols","path":EXAMPLE_PATH}}));
    invalid(&response, "unknown_job");
    helper_navigation(&mut client, &session, &strong, &repo);

    // Cancel one listener only, and leave the other application's notifications unread until terminal.
    client.notify(
        "notifications/cancelled",
        json!({"requestId":first.0,"reason":"exercise independent listener lifetime"}),
    );
    let _ = client.rpc("ping", json!({}));
    let since = client.notifications.len();
    let shifted = format!("/* same proofs, refreshed source positions */\n{strong}");
    let before = wrapper.batches();
    let (_, status, _) = client.run(
        &mut session,
        json!([replace(EXAMPLE_PATH, &shifted)]),
        &wrapper,
    );
    accepted(&status);
    assert_eq!(status["verification_cache_hit"], true);
    assert_eq!(
        wrapper.batches(),
        before,
        "comment-only line shift invalidated proof identity"
    );
    helper_navigation(&mut client, &session, &shifted, &repo);
    client.await_updates(since, &[second], &session.status_uri);
    assert!(
        !client.updated(since, first, &session.status_uri),
        "cancelled listener still receives job updates"
    );
    let latest = client.status(&session.status_uri);
    assert_eq!(
        latest, status,
        "lagged listener cannot recover the latest terminal state by rereading"
    );

    let mut referenced = client.open(&[]);
    let (_, status, _) = client.run(
        &mut referenced,
        json!([reference("examples/example.c"), reference("examples/pal.h")]),
        &wrapper,
    );
    accepted(&status);
    let symbols: Vec<DocumentSymbol> = data(client.query(
        &referenced,
        None,
        json!({"kind":"symbols","path":"examples/example.c"}),
    ));
    assert!(
        symbols
            .iter()
            .any(|symbol| symbol.name == "multiply_by_repeated_addition")
    );
    client.close(&referenced);

    // FIFO holds a genuine future F* invocation; a real descendant exercises process-group kill.
    wrapper.arm();
    let job = client.submit(
        &session,
        json!([append(
            EXAMPLE_PATH,
            "\nint cancelled_value(void) _ensures(return == 17) { return 17; }\n"
        )]),
    );
    let paused = wrapper.paused();
    assert!(
        paused.iter().all(|pid| process_alive(*pid)),
        "wrapper/sentinel did not reach live barrier"
    );
    let progress = client.status(&session.status_uri);
    assert_eq!(progress["phase"], "verifying");
    let response = client.tool_response("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":[]}));
    invalid(&response, "session_busy");
    let mut queued_session = client.open(&[]);
    let queued = client.submit(&queued_session, json!([replace("queued.c", &swap)]));
    let response = client.tool_response("pal_query", json!({"session_id":queued_session.session_id,"job_id":queued.job_id,"query":{"kind":"symbols","path":"queued.c"}}));
    invalid(&response, "index_not_ready");
    let response = client.tool(
        "pal_session",
        json!({"action":"cancel","session_id":queued_session.session_id,"job_id":queued.job_id}),
    );
    assert_eq!(response["phase"], "cancelled");
    assert_eq!(
        client.terminal(&mut queued_session, &queued)["phase"],
        "cancelled"
    );
    client.close(&queued_session);
    thread::sleep(Duration::from_millis(2200));
    let heartbeat = client.status(&session.status_uri);
    assert_eq!(heartbeat["phase"], "verifying");
    assert!(
        heartbeat["sequence"].as_u64().unwrap() > progress["sequence"].as_u64().unwrap(),
        "silent verifier did not publish heartbeats"
    );
    assert!(heartbeat["elapsed_ms"].as_u64().unwrap() > progress["elapsed_ms"].as_u64().unwrap());
    let mut processes = descendants(ProcessId(client.child.id()));
    processes.extend(paused);
    let result = client.tool(
        "pal_session",
        json!({"action":"cancel","session_id":session.session_id,"job_id":job.job_id}),
    );
    assert_eq!(result["phase"], "cancelled");
    let status = client.terminal(&mut session, &job);
    assert_eq!(status["phase"], "cancelled");
    assert_exited(&processes);
    assert_eq!(
        client.tool(
            "pal_session",
            json!({"action":"cancel","session_id":session.session_id,"job_id":job.job_id})
        )["phase"],
        "cancelled"
    );
    helper_navigation(&mut client, &session, &shifted, &repo);
    client.close(&session);
    let reopened = client.open(&[]);
    assert_ne!(
        reopened.session_id, session.session_id,
        "closed session identity was reused"
    );
    client.close(&reopened);
    let response = client.tool_response("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":[]}));
    invalid(&response, "unknown_session");
    let arbitrary = client.rpc(
        "resources/read",
        json!({"uri":project_uri(&repo, "examples/example.c")}),
    );
    assert!(
        arbitrary.get("error").is_some(),
        "resource API accepted an arbitrary filesystem URI"
    );
    client.shutdown();
    assert_eq!(
        fs::read_to_string(repo.join("examples/example.c")).unwrap(),
        example
    );
    assert_eq!(
        fs::read(repo.join("examples/pal.h")).unwrap(),
        example_header
    );
    assert_eq!(
        directory_entries(&repo.join("examples")),
        example_entries,
        "server wrote output beside an example"
    );

    let fixtures = tempfile::tempdir().unwrap();
    let root = fixtures.path().canonicalize().unwrap();
    fs::write(root.join("pal.h"), &example_header).unwrap();
    fs::write(root.join("swap.c"), &swap).unwrap();
    fs::write(root.join("constants.h"), HEADER).unwrap();
    fs::write(root.join("constants.c"), HEADER_ROOT).unwrap();
    for (directory, name, value) in [("a", "in_a", 1), ("b", "in_b", 2)] {
        fs::create_dir(root.join(directory)).unwrap();
        fs::write(root.join(directory).join("unit.c"), format!("#include \"pal.h\"\nint {name}(void) _ensures(return == {value}) {{ return {value}; }}\n")).unwrap();
    }
    let wrapper = Wrapper::new();
    let mut client = Client::start(&root, &wrapper, &repo);
    let mut session = client.open(&["."]);
    let (_, status, _) = client.run(
        &mut session,
        json!([reference("swap.c"), reference("constants.c")]),
        &wrapper,
    );
    accepted(&status);
    header_navigation(&mut client, &session, &root, 1);
    fs::write(
        root.join("constants.h"),
        HEADER.replace("HEADER_VALUE 1", "HEADER_VALUE 2"),
    )
    .unwrap();
    let (_, status, trace) = client.run(&mut session, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(status["verification_cache_hit"], false);
    trace.stored("Func_read_header.fst");
    trace.reused_module("Func_swap");
    header_navigation(&mut client, &session, &root, 2);
    let overlay = HEADER.replace("HEADER_VALUE 1", "HEADER_VALUE 3");
    let (_, status, trace) = client.run(
        &mut session,
        json!([replace("constants.h", &overlay)]),
        &wrapper,
    );
    accepted(&status);
    trace.stored("Func_read_header.fst");
    trace.reused_module("Func_swap");
    header_navigation(&mut client, &session, &root, 3);
    assert_eq!(
        fs::read_to_string(root.join("constants.h")).unwrap(),
        HEADER.replace("HEADER_VALUE 1", "HEADER_VALUE 2"),
        "inline header overwrote disk"
    );
    let (_, status, _) = client.run(
        &mut session,
        json!([reference("a/unit.c"), reference("b/unit.c")]),
        &wrapper,
    );
    accepted(&status);
    for (path, expected) in [("a/unit.c", "in_a"), ("b/unit.c", "in_b")] {
        let result = client.query(&session, None, json!({"kind":"symbols","path":path}));
        assert_public(&result, &root);
        let symbols: Vec<DocumentSymbol> = data(result);
        assert!(
            symbols.iter().any(|symbol| symbol.name == expected),
            "duplicate basename lost {expected}"
        );
    }
    let (_, status, _) = client.run(&mut session, json!([replace("a/unit.c", "#include \"pal.h\"\nstatic int duplicate(void) _ensures(return == 1) { return 1; }\n"), replace("b/unit.c", "#include \"pal.h\"\nstatic int duplicate(void) _ensures(return == 2) { return 2; }\n")]), &wrapper);
    failed(&status, "module_name_collision");
    let (_, status, _) = client.run(
        &mut session,
        json!([
            replace(
                "a/unit.c",
                "#include \"pal.h\"\nenum first_enum { DUPLICATE_ENUM = 1 };\n"
            ),
            replace(
                "b/unit.c",
                "#include \"pal.h\"\nenum second_enum { DUPLICATE_ENUM = 2 };\n"
            )
        ]),
        &wrapper,
    );
    failed(&status, "module_name_collision");
    let symbols: Vec<DocumentSymbol> =
        data(client.query(&session, None, json!({"kind":"symbols","path":"a/unit.c"})));
    assert!(symbols.iter().any(|symbol| symbol.name == "in_a"));
    semantic_navigation(&mut client, &mut session, &wrapper, &root);

    let status_before = client.status(&session.status_uri);
    for (changes, reason) in [
        (json!([reference("../outside.c")]), "invalid_path"),
        (
            json!([reference(root.join("swap.c").to_str().unwrap())]),
            "invalid_path",
        ),
        (
            json!([reference("https://example.test/source.c")]),
            "invalid_path",
        ),
        (json!([reference("bad\0.c")]), "invalid_path"),
        (json!([reference("unsupported.cpp")]), "invalid_path"),
        (json!([append("not-managed.c", "int x;")]), "missing_file"),
    ] {
        let response = client.tool_response("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":changes}));
        invalid(&response, reason);
        assert_eq!(
            client.status(&session.status_uri),
            status_before,
            "invalid parameters started a job"
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        symlink(root.join("a/unit.c"), root.join("alias.c")).unwrap();
        let response = client.tool_response("pal_verify", json!({"session_id":session.session_id,"base_revision":session.accepted_revision,"changes":[reference("a/unit.c"), reference("alias.c")]}));
        invalid(&response, "conflicting_changes");
    }
    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("escape.c"), &swap).unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(outside.path().join("escape.c"), root.join("escape.c")).unwrap();
    let (_, status, _) = client.run(&mut session, json!([reference("escape.c")]), &wrapper);
    failed(&status, "invalid_path");
    let (_, status, _) = client.run(&mut session, json!([reference("missing.c")]), &wrapper);
    failed(&status, "missing_file");
    fs::write(root.join("not-utf8.c"), [0xff, 0xfe]).unwrap();
    let (_, status, _) = client.run(&mut session, json!([reference("not-utf8.c")]), &wrapper);
    failed(&status, "snapshot_failed");
    let (_, status, _) = client.run(
        &mut session,
        json!([replace("broken.c", "#include \"pal.h\"\nint broken( {\n")]),
        &wrapper,
    );
    failed(&status, "translation_failed");
    assert!(
        status["diagnostics"]
            .as_object()
            .unwrap()
            .values()
            .any(|diagnostics| diagnostics
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["severity"] == 1)),
        "syntax failure lost compiler diagnostics: {status}"
    );
    let before = wrapper.batches();
    let (_, status, _) = client.run(
        &mut session,
        json!([replace(
            "unsupported.c",
            "#include \"pal.h\"\nlong double unsupported_float(long double x) { return x; }\n"
        )]),
        &wrapper,
    );
    failed(&status, "translation_failed");
    assert!(
        status["diagnostics"]
            .as_object()
            .unwrap()
            .get(&project_uri(&root, "unsupported.c"))
            .and_then(Value::as_array)
            .is_some_and(|diagnostics| diagnostics
                .iter()
                .any(|diagnostic| diagnostic["severity"] == 1)),
        "PAL's zero-exit diagnostic errors were not retained: {status}"
    );
    assert_eq!(
        wrapper.batches(),
        before,
        "PAL diagnostic error reached F* despite translation failure"
    );
    let mut empty = client.open(&["."]);
    let response = client.tool_response("pal_verify", json!({"session_id":empty.session_id,"base_revision":0,"changes":[replace("only.h", "#define VALUE 1\n")]}));
    invalid(&response, "no_translation_units");
    let (_, status, _) = client.run(&mut empty, json!([replace("empty.c", "")]), &wrapper);
    accepted(&status);
    client.close(&empty);
    client.close(&session);
    client.shutdown();
}

#[test]
fn real_mcp_add_compile_options() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .canonicalize()
        .unwrap();
    let fixtures = tempfile::tempdir().unwrap();
    let root = fixtures.path().canonicalize().unwrap();
    fs::write(
        root.join("pal.h"),
        fs::read(repo.join("examples/pal.h")).unwrap(),
    )
    .unwrap();
    for (directory, value) in [("first include", 7), ("second", 9)] {
        fs::create_dir(root.join(directory)).unwrap();
        fs::write(
            root.join(directory).join("config.h"),
            format!("#define HEADER_VALUE {value}\n"),
        )
        .unwrap();
    }
    fs::create_dir(root.join("third")).unwrap();
    fs::write(root.join("third/extra.h"), "#define EXTRA 1\n").unwrap();
    let source = r#"#include "pal.h"
#include <config.h>
#if ENABLED != 1 || HEADER_VALUE != 7
#error incorrect compile options
#endif
#if FACTOR == 2
int configured_two(void) _ensures(return == 14) { return HEADER_VALUE * FACTOR; }
#elif FACTOR == 3
#include <extra.h>
int configured_three(void) _ensures(return == 22) { return HEADER_VALUE * FACTOR + EXTRA; }
#else
#error incorrect definition order
#endif
"#;
    let wrapper = Wrapper::new();
    let mut client = Client::start(&root, &wrapper, &repo);
    let mut session = client.open(&[]);
    client.tool(
        "add_include_paths",
        json!({"session_id":session.session_id,"include_paths":["first include","second"]}),
    );
    client.tool(
        "add_preprocessor_definition",
        json!({"session_id":session.session_id,"defines":["ENABLED","FACTOR=2"]}),
    );
    let (_, status, _) = client.run(
        &mut session,
        json!([replace("configured.c", source)]),
        &wrapper,
    );
    accepted(&status);
    let symbols = |client: &mut Client, session: &Session| -> Vec<DocumentSymbol> {
        data(client.query(
            session,
            None,
            json!({"kind":"symbols","path":"configured.c"}),
        ))
    };
    assert!(
        symbols(&mut client, &session)
            .iter()
            .any(|symbol| symbol.name == "configured_two")
    );
    client.tool(
        "add_include_paths",
        json!({"session_id":session.session_id,"include_paths":["third"]}),
    );
    client.tool(
        "add_preprocessor_definition",
        json!({"session_id":session.session_id,"defines":["FACTOR=1","FACTOR=3"]}),
    );
    assert_eq!(client.status(&session.status_uri)["accepted_revision"], 1);
    assert!(
        symbols(&mut client, &session)
            .iter()
            .any(|symbol| symbol.name == "configured_two")
    );
    for (tool, arguments) in [
        (
            "add_include_paths",
            json!({"session_id":session.session_id,"include_paths":["second","bad\0path"]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":session.session_id,"defines":["FACTOR=4","bad\0define"]}),
        ),
    ] {
        invalid(&client.tool_response(tool, arguments), "invalid_path");
    }
    wrapper.arm();
    let job = client.submit(&session, json!([]));
    let paused = wrapper.paused();
    for (tool, arguments) in [
        (
            "add_include_paths",
            json!({"session_id":session.session_id,"include_paths":["second"]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":session.session_id,"defines":["FACTOR=4"]}),
        ),
    ] {
        invalid(&client.tool_response(tool, arguments), "session_busy");
    }
    client.tool(
        "pal_session",
        json!({"action":"cancel","session_id":session.session_id,"job_id":job.job_id}),
    );
    let status = client.terminal(&mut session, &job);
    assert_eq!(status["phase"], "cancelled");
    assert_exited(&paused);
    let (_, status, trace) = client.run(&mut session, json!([]), &wrapper);
    accepted(&status);
    trace.stored("Func_configured_three.fst");
    let updated = symbols(&mut client, &session);
    assert!(
        updated
            .iter()
            .any(|symbol| symbol.name == "configured_three")
    );
    assert!(!updated.iter().any(|symbol| symbol.name == "configured_two"));
    let mut isolated = client.open(&["first include"]);
    let (_, status, _) = client.run(
        &mut isolated,
        json!([replace("configured.c", source)]),
        &wrapper,
    );
    failed(&status, "translation_failed");
    client.close(&isolated);
    let mut other = client.open(&[]);
    let (_, status, _) = client.run(
        &mut other,
        json!([replace(
            "independent.c",
            "#include \"pal.h\"\nint independent(void) _ensures(return == 1) { return 1; }\n"
        )]),
        &wrapper,
    );
    accepted(&status);
    for (tool, arguments) in [
        (
            "add_include_paths",
            json!({"session_id":session.session_id,"include_paths":["second"]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":session.session_id,"defines":["UNUSED=1"]}),
        ),
        (
            "add_include_paths",
            json!({"session_id":session.session_id,"include_paths":[]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":session.session_id,"defines":[]}),
        ),
    ] {
        for current in [&mut session, &mut other] {
            let before = wrapper.batches();
            let (_, status, _) = client.run(current, json!([]), &wrapper);
            accepted(&status);
            assert_eq!(status["verification_cache_hit"], true);
            assert_eq!(wrapper.batches(), before);
        }
        let revision = session.accepted_revision;
        client.tool(tool, arguments);
        assert_eq!(
            client.status(&session.status_uri)["accepted_revision"],
            json!(revision)
        );
        assert!(
            symbols(&mut client, &session)
                .iter()
                .any(|symbol| symbol.name == "configured_three")
        );
        let (_, status, _) = client.run(
            &mut session,
            json!([replace("configured.c", "#error rejected candidate\n")]),
            &wrapper,
        );
        failed(&status, "translation_failed");
        for (current, name) in [
            (&mut session, "configured_three"),
            (&mut other, "independent"),
        ] {
            let before = wrapper.batches();
            let (_, status, trace) = client.run(current, json!([]), &wrapper);
            accepted(&status);
            assert_eq!(
                status["verification_cache_hit"], false,
                "{tool} retained a cached full result: {status}"
            );
            assert!(wrapper.batches().0 > before.0, "{tool} skipped F*");
            for source in [
                format!("Func_{name}.fst"),
                format!("Func_{name}.fsti"),
                "TranslationErrors.fst".to_owned(),
            ] {
                trace.stored(&source);
            }
        }
    }
    wrapper.arm();
    let job = client.submit(
        &other,
        json!([replace(
            "independent.c",
            "#include \"pal.h\"\nint independent(void) _ensures(return == 2) { return 2; }\n"
        )]),
    );
    wrapper.paused();
    client.tool(
        "add_include_paths",
        json!({"session_id":session.session_id,"include_paths":[]}),
    );
    fs::write(wrapper.directory.path().join("barrier"), "release\n").unwrap();
    accepted(&client.terminal(&mut other, &job));
    let (_, status, trace) = client.run(&mut other, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(
        status["verification_cache_hit"], false,
        "in-flight verification revived the invalidated cache"
    );
    trace.stored("Func_independent.fst");
    trace.stored("Func_independent.fsti");
    for (tool, arguments) in [
        (
            "add_include_paths",
            json!({"session_id":other.session_id,"include_paths":["bad\0path"]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":"unknown","defines":[]}),
        ),
    ] {
        let reason = if tool == "add_include_paths" {
            "invalid_path"
        } else {
            "unknown_session"
        };
        invalid(&client.tool_response(tool, arguments), reason);
    }
    let (_, status, _) = client.run(&mut other, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(
        status["verification_cache_hit"], true,
        "rejected option updates invalidated the cache"
    );
    client.close(&other);
    client.close(&session);
    for (tool, arguments) in [
        (
            "add_include_paths",
            json!({"session_id":session.session_id,"include_paths":[]}),
        ),
        (
            "add_preprocessor_definition",
            json!({"session_id":session.session_id,"defines":[]}),
        ),
    ] {
        invalid(&client.tool_response(tool, arguments), "unknown_session");
    }
    client.shutdown();
}

#[test]
fn real_mcp_open_root_resets_project() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .canonicalize()
        .unwrap();
    let fixtures = tempfile::tempdir().unwrap();
    let source = "#include \"pal.h\"\n#include <value.h>\n#ifdef OLD\nint old_option(void) _ensures(return == 0) { return 0; }\n#endif\nint project_value(void) _ensures(return == VALUE) { return VALUE; }\n";
    let roots: Vec<_> = [1, 2]
        .into_iter()
        .map(|value| {
            let root = fixtures.path().join(format!("project{value}"));
            fs::create_dir_all(root.join("inc")).unwrap();
            fs::write(
                root.join("pal.h"),
                fs::read(repo.join("examples/pal.h")).unwrap(),
            )
            .unwrap();
            fs::write(root.join("inc/value.h"), format!("#define VALUE {value}\n")).unwrap();
            fs::write(root.join("main.c"), source).unwrap();
            root.canonicalize().unwrap()
        })
        .collect();
    let wrapper = Wrapper::new();
    let mut client = Client::start(&roots[0], &wrapper, &repo);
    let response = client.tool_response("pal_session", json!({"action":"open"}));
    assert_eq!(response["result"]["isError"], true, "{response}");
    let mut old = client.open(&["inc"]);
    client.tool(
        "add_preprocessor_definition",
        json!({"session_id":old.session_id,"defines":["OLD"]}),
    );
    let (_, status, _) = client.run(&mut old, json!([reference("main.c")]), &wrapper);
    accepted(&status);
    for path in [
        String::new(),
        "bad\0root".to_owned(),
        roots[0].join("main.c").to_string_lossy().into_owned(),
        roots[0].join("missing").to_string_lossy().into_owned(),
    ] {
        invalid(
            &client.tool_response("pal_session", json!({"action":"open","root":path})),
            "invalid_path",
        );
    }
    let (_, status, _) = client.run(&mut old, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(
        status["verification_cache_hit"], true,
        "invalid roots discarded the working project"
    );
    let listener = client.listen(&old.status_uri);
    wrapper.arm();
    let active = client.submit(
        &old,
        json!([append(
            "main.c",
            "int pending(void) _ensures(return == 3) { return 3; }\n"
        )]),
    );
    let paused = wrapper.paused();
    let queued = client.open(&[]);
    client.submit(
        &queued,
        json!([replace("queued.c", "int queued(void) { return 1; }\n")]),
    );
    let started = Instant::now();
    client.root = roots[1].clone();
    let mut fresh = client.open(&[]);
    assert!(
        started.elapsed() < Duration::from_secs(30),
        "root reset did not terminate old jobs promptly"
    );
    assert_ne!(fresh.session_id, old.session_id);
    assert_exited(&paused);
    assert!(
        client.response(listener.0).get("error").is_none(),
        "old subscription did not finish cleanly"
    );
    let resources = client.rpc("resources/list", json!({}));
    let resources = resources["result"]["resources"].as_array().unwrap();
    assert_eq!(resources.len(), 1);
    assert_eq!(resources[0]["uri"], json!(fresh.status_uri));
    for previous in [&old, &queued] {
        assert!(
            client
                .rpc("resources/read", json!({"uri":previous.status_uri}))
                .get("error")
                .is_some()
        );
        invalid(&client.tool_response("pal_verify", json!({"session_id":previous.session_id,"base_revision":previous.accepted_revision,"changes":[]})), "unknown_session");
        invalid(&client.tool_response("pal_query", json!({"session_id":previous.session_id,"job_id":active.job_id,"query":{"kind":"symbols","path":"main.c"}})), "unknown_session");
    }
    let (_, status, _) = client.run(&mut fresh, json!([reference("main.c")]), &wrapper);
    failed(&status, "translation_failed");
    client.tool(
        "add_include_paths",
        json!({"session_id":fresh.session_id,"include_paths":["inc"]}),
    );
    let (_, status, _) = client.run(&mut fresh, json!([reference("main.c")]), &wrapper);
    accepted(&status);
    let symbols: Vec<DocumentSymbol> =
        data(client.query(&fresh, None, json!({"kind":"symbols","path":"main.c"})));
    assert!(symbols.iter().any(|symbol| symbol.name == "project_value"));
    assert!(
        !symbols
            .iter()
            .any(|symbol| symbol.name == "old_option" || symbol.name == "pending")
    );
    let hover = client.query(
        &fresh,
        None,
        query_at("hover", "main.c", at(source, "VALUE)")),
    );
    assert!(hover.to_string().contains("VALUE 2"), "{hover}");
    assert_public(&hover, &roots[1]);
    let (_, status, _) = client.run(&mut fresh, json!([]), &wrapper);
    accepted(&status);
    assert_eq!(status["verification_cache_hit"], true);
    let mut restarted = client.open(&["inc"]);
    assert_eq!(restarted.accepted_revision, Revision(0));
    assert_ne!(restarted.session_id, fresh.session_id);
    let (_, status, _) = client.run(&mut restarted, json!([reference("main.c")]), &wrapper);
    accepted(&status);
    assert_eq!(
        status["verification_cache_hit"], true,
        "same-root open discarded cached results"
    );
    assert_eq!(
        client.status(&fresh.status_uri)["phase"],
        "accepted",
        "same-root open removed an existing session"
    );
    client.close(&restarted);
    client.shutdown();
}
