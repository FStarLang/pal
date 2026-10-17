//! Owned subprocess groups with cooperative cancellation and separately captured logs.
//!
//! Shutdown must cancel and join the owning job, rather than abort its future. The drop guard is
//! only a last-resort group kill; the normal cancellation path also waits and drains both pipes.

use std::io::{self, Write};
use std::path::Path;
use std::process::{ExitStatus, Stdio};
use std::sync::Arc;

#[cfg(windows)]
use process_wrap::tokio::JobObject;
#[cfg(unix)]
use process_wrap::tokio::ProcessGroup;
use process_wrap::tokio::{ChildWrapper, CommandWrap, KillOnDrop};
use tokio::io::{AsyncRead, AsyncReadExt};
use tokio::sync::watch;

use super::workspace::{Failure, Result};

/// A sticky, cloneable cancellation signal, including for workers not yet started.
#[derive(Clone, Debug)]
pub struct Cancellation {
    sender: watch::Sender<bool>,
}

impl Cancellation {
    pub fn new() -> Self {
        Self {
            sender: watch::channel(false).0,
        }
    }

    pub fn cancel(&self) {
        self.sender.send_replace(true);
    }

    pub fn is_cancelled(&self) -> bool {
        *self.sender.borrow()
    }

    pub async fn cancelled(&self) {
        let mut receiver = self.sender.subscribe();
        let _ = receiver.wait_for(|cancelled| *cancelled).await;
    }

    pub fn check(&self) -> Result<()> {
        if self.is_cancelled() {
            Err(Failure::new("cancelled", "verification cancelled"))
        } else {
            Ok(())
        }
    }
}

#[derive(Clone)]
pub struct Output(Arc<dyn Fn(String) + Send + Sync>);

impl Output {
    pub fn new(callback: impl Fn(String) + Send + Sync + 'static) -> Self {
        Self(Arc::new(callback))
    }
    fn emit(&self, line: String) {
        (self.0)(line);
    }
}

#[derive(Debug)]
pub struct ProcessOutput {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

struct OwnedChild {
    child: Box<dyn ChildWrapper>,
    armed: bool,
}

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if self.armed {
            // Tokio's Unix KillOnDrop kills only the leader; use the wrapper for its whole group.
            let _ = self.child.start_kill();
        }
    }
}

/// Run directly without a shell or process-global working-directory changes.
///
/// Both raw streams are copied to server stderr and captured independently. The callback receives
/// complete lines (or the final unterminated line), with lossy UTF-8 only in the callback text.
/// Cancellation returns only after the wrapped group has been waited and both pipes have closed.
pub async fn run(
    program: &Path,
    args: &[String],
    cwd: &Path,
    cancel: &Cancellation,
    output: Output,
) -> Result<ProcessOutput> {
    cancel.check()?;
    let mut command = CommandWrap::with_new(program, |command| {
        command
            .args(args)
            .current_dir(cwd)
            .env_remove("OTHERFLAGS")
            .env_remove("ADMIT")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
    });
    command.wrap(KillOnDrop);
    #[cfg(unix)]
    command.wrap(ProcessGroup::leader());
    #[cfg(windows)]
    command.wrap(JobObject);

    let child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            cancel.check()?;
            return Err(worker_failed("cannot start subprocess", error));
        }
    };
    let mut owned = OwnedChild { child, armed: true };
    drop(command);
    let stdout_pipe = owned.child.stdout().take();
    let stderr_pipe = owned.child.stderr().take();
    let stdout_capture = capture(stdout_pipe, &output);
    let stderr_capture = capture(stderr_pipe, &output);
    tokio::pin!(stdout_capture, stderr_capture);

    let mut stdout = None;
    let mut stderr = None;
    let mut status = None;
    let mut waited = false;
    let mut terminated = false;
    let mut cancelled = false;
    let mut failure = None;
    let mut kill_error = None;

    while !waited || stdout.is_none() || stderr.is_none() {
        let stop = tokio::select! {
            biased;
            _ = cancel.cancelled(), if !cancelled => {
                cancelled = true;
                true
            }
            result = owned.child.wait(), if !waited => {
                waited = true;
                match result {
                    Ok(exit) => { status = Some(exit); false }
                    Err(error) => {
                        failure.get_or_insert_with(|| worker_failed("cannot wait for subprocess", error));
                        true
                    }
                }
            }
            result = &mut stdout_capture, if stdout.is_none() => {
                let failed = result.is_err();
                if let Err(error) = &result {
                    failure.get_or_insert_with(|| worker_failed("cannot capture subprocess stdout", error));
                }
                stdout = Some(result);
                failed
            }
            result = &mut stderr_capture, if stderr.is_none() => {
                let failed = result.is_err();
                if let Err(error) = &result {
                    failure.get_or_insert_with(|| worker_failed("cannot capture subprocess stderr", error));
                }
                stderr = Some(result);
                failed
            }
        };
        if stop && !terminated {
            terminated = true;
            // kill() targets the wrapped group/job and waits; always wait again even if killing
            // raced a natural exit. Never leave a detached reader or return before pipe EOF.
            kill_error = Box::into_pin(owned.child.kill()).await.err();
            waited = true;
            match owned.child.wait().await {
                Ok(exit) => status = Some(exit),
                Err(error) => {
                    failure.get_or_insert_with(|| worker_failed("cannot reap subprocess", error));
                }
            }
        }
    }

    // A failed wait keeps the last-resort group kill armed even when both pipes are already closed.
    owned.armed = status.is_none();
    if let Some(failure) = failure {
        return Err(failure);
    }
    // A group can already be gone when cancellation wins the select. A successful wait plus both
    // completed drains lets that kill/exit race remain cancellation, rather than a spurious error.
    cancel.check()?;
    if let Some(error) = kill_error {
        return Err(worker_failed("cannot terminate subprocess", error));
    }
    match (status, stdout, stderr) {
        (Some(status), Some(Ok(stdout)), Some(Ok(stderr))) => Ok(ProcessOutput {
            status,
            stdout,
            stderr,
        }),
        _ => Err(Failure::new(
            "worker_failed",
            "subprocess finished without complete output",
        )),
    }
}

async fn capture(pipe: Option<impl AsyncRead + Unpin>, output: &Output) -> io::Result<Vec<u8>> {
    let mut pipe = pipe.ok_or_else(|| io::Error::other("subprocess pipe is missing"))?;
    let mut bytes = Vec::new();
    let mut line_start = 0;
    let mut buffer = [0; 8192];
    loop {
        let count = pipe.read(&mut buffer).await?;
        if count == 0 {
            if line_start != bytes.len() {
                output.emit(String::from_utf8_lossy(&bytes[line_start..]).into_owned());
            }
            return Ok(bytes);
        }
        io::stderr().lock().write_all(&buffer[..count])?;
        let start = bytes.len();
        bytes.extend_from_slice(&buffer[..count]);
        for (offset, byte) in buffer[..count].iter().enumerate() {
            if *byte == b'\n' {
                let end = start + offset;
                output.emit(String::from_utf8_lossy(&bytes[line_start..end]).into_owned());
                line_start = end + 1;
            }
        }
    }
}

fn worker_failed(context: &str, error: impl std::fmt::Display) -> Failure {
    Failure::new("worker_failed", format!("{context}: {error}"))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn captures_separately_and_cancels_descendants_before_returning() {
        let cancel = Cancellation::new();
        let output = Output::new(|_| {});
        let captured = run(
            Path::new("sh"),
            &["-c".into(), "printf 'out\\n'; printf 'err\\n' >&2".into()],
            Path::new("."),
            &cancel,
            output.clone(),
        )
        .await
        .unwrap();
        assert!(captured.status.success());
        assert_eq!(captured.stdout, b"out\n");
        assert_eq!(captured.stderr, b"err\n");

        let signal = cancel.clone();
        let output = Output::new(move |line| {
            if line == "ready" {
                signal.cancel();
            }
        });
        // The background process inherits both pipes. If only its shell is killed, draining
        // cannot finish until sleep exits, so the timeout detects a surviving descendant.
        let result = tokio::time::timeout(
            Duration::from_secs(5),
            run(
                Path::new("sh"),
                &["-c".into(), "sleep 60 & printf 'ready\\n'; wait".into()],
                Path::new("."),
                &cancel,
                output,
            ),
        )
        .await
        .expect("cancellation left a descendant holding a pipe");
        assert_eq!(result.unwrap_err().code, "cancelled");
        cancel.cancelled().await;
        assert_eq!(
            run(
                Path::new("nonexistent-pal-process"),
                &[],
                Path::new("."),
                &cancel,
                Output::new(|_| {})
            )
            .await
            .unwrap_err()
            .code,
            "cancelled"
        );
    }
}
