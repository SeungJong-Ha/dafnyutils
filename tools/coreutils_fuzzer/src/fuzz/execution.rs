use super::comparison::fs_snapshot::restore_path_times;
use super::comparison::process_outcome::run_result;
use super::{FsTimes, ResolvedPaths, ResolvedTarget, RunResult, VariantKind};
use crate::utils::cli::{ExecHelperArgs, ExecKind};
use crate::utils::execution_context::{
    canonical_environment_config, canonical_process_environment, validate_process_umask,
};
use crate::utils::paths::format_path_error;
use crate::utils::process::{PreparedProcess, ProcessError};
use crate::{
    fuzzer_outcome_marker, FUZZER_DOTNET_RUNTIME_FAILURE, FUZZER_TARGET_SPAWN_FAILURE,
    FUZZER_TIMEOUT,
};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::fd::{AsRawFd, FromRawFd};

pub(crate) const CONTROLLED_FIXTURE_ATIME_SEC: i64 = 4_102_444_800;
pub(crate) const CONTROLLED_FIXTURE_MTIME_SEC: i64 = 2_000_000_000;
pub(crate) const CONTROLLED_FIXTURE_TIME_NSEC: i64 = 0;

pub(crate) fn control_chmod_fixture_node(path: &Path, is_symlink: bool) -> Result<(), String> {
    suppress_fixture_atime_updates_for_node(path, is_symlink)?;

    #[cfg(unix)]
    return restore_path_times(
        path,
        FsTimes {
            atime_sec: CONTROLLED_FIXTURE_ATIME_SEC,
            atime_nsec: CONTROLLED_FIXTURE_TIME_NSEC,
            mtime_sec: CONTROLLED_FIXTURE_MTIME_SEC,
            mtime_nsec: CONTROLLED_FIXTURE_TIME_NSEC,
            ctime_sec: 0,
            ctime_nsec: 0,
        },
        is_symlink,
    );
    #[cfg(not(unix))]
    Err(format!(
        "strict chmod fixture control requires Unix timestamp support for `{}`",
        path.display()
    ))
}

pub(crate) fn suppress_fixture_atime_updates_for_node(
    path: &Path,
    is_symlink: bool,
) -> Result<(), String> {
    #[cfg(target_os = "linux")]
    if !is_symlink {
        set_linux_noatime(path)?;
    }
    #[cfg(not(target_os = "linux"))]
    if !is_symlink {
        return Err(format!(
            "strict read fixture control requires Linux FS_NOATIME_FL for `{}`",
            path.display()
        ));
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn set_linux_noatime(path: &Path) -> Result<(), String> {
    use std::fs::OpenOptions;
    use std::os::fd::AsRawFd;
    use std::os::raw::{c_int, c_long, c_ulong};

    const IOC_NRBITS: c_ulong = 8;
    const IOC_TYPEBITS: c_ulong = 8;
    const IOC_SIZEBITS: c_ulong = 14;
    const IOC_NRSHIFT: c_ulong = 0;
    const IOC_TYPESHIFT: c_ulong = IOC_NRSHIFT + IOC_NRBITS;
    const IOC_SIZESHIFT: c_ulong = IOC_TYPESHIFT + IOC_TYPEBITS;
    const IOC_DIRSHIFT: c_ulong = IOC_SIZESHIFT + IOC_SIZEBITS;
    const IOC_WRITE: c_ulong = 1;
    const IOC_READ: c_ulong = 2;
    const FS_IOC_GETFLAGS: c_ulong = (IOC_READ << IOC_DIRSHIFT)
        | ((b'f' as c_ulong) << IOC_TYPESHIFT)
        | (1 << IOC_NRSHIFT)
        | ((std::mem::size_of::<c_long>() as c_ulong) << IOC_SIZESHIFT);
    const FS_IOC_SETFLAGS: c_ulong = (IOC_WRITE << IOC_DIRSHIFT)
        | ((b'f' as c_ulong) << IOC_TYPESHIFT)
        | (2 << IOC_NRSHIFT)
        | ((std::mem::size_of::<c_long>() as c_ulong) << IOC_SIZESHIFT);
    const FS_NOATIME_FL: c_long = 0x0000_0080;

    unsafe extern "C" {
        fn ioctl(fd: c_int, request: c_ulong, argument: *mut c_long) -> c_int;
    }

    let file = OpenOptions::new()
        .read(true)
        .open(path)
        .map_err(|error| format_path_error("open fixture node for FS_NOATIME_FL", path, error))?;
    let mut flags: c_long = 0;
    if unsafe { ioctl(file.as_raw_fd(), FS_IOC_GETFLAGS, &mut flags) } != 0 {
        return Err(format!(
            "failed to read inode flags on `{}`: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    flags |= FS_NOATIME_FL;
    if unsafe { ioctl(file.as_raw_fd(), FS_IOC_SETFLAGS, &mut flags) } != 0 {
        return Err(format!(
            "failed to set FS_NOATIME_FL on `{}`: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ControlledUmaskProbe {
    pub(crate) observed_umask: u32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
    pub(crate) exit_code: i32,
}

#[cfg(test)]
pub(crate) fn apply_deterministic_env(cmd: &mut Command) {
    cmd.env_clear();
    for (key, value) in canonical_process_environment() {
        cmd.env(key, value);
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn run_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    umask: u32,
    identity: Option<(u32, u32)>,
    timeout: Duration,
) -> Result<RunResult, String> {
    prepare_variant(kind, paths, argv, cwd, root, umask, identity)?.go_and_collect(stdin, timeout)
}

/// Prepares any target at READY using the same environment, umask and identity policy.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedTarget, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    prepare_controlled_target(
        target,
        argv,
        cwd,
        root,
        &canonical_process_environment(),
        umask,
        identity,
    )
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn run_controlled_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    timeout: Duration,
) -> Result<RunResult, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    run_controlled_target(target, argv, stdin, cwd, root, env, umask, timeout)
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn prepare_controlled_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedTarget, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    prepare_unobserved_target(target, argv, cwd, root, env, umask, identity)
}

fn apply_process_umask(command: &mut Command, requested_umask: u32) -> Result<(), String> {
    validate_process_umask(requested_umask)?;
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;

        unsafe extern "C" {
            fn umask(mask: u32) -> u32;
        }
        unsafe {
            command.pre_exec(move || {
                umask(requested_umask);
                Ok(())
            });
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = requested_umask;
        Err("controlled child umask requires Unix".to_string())
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn run_controlled_target(
    target: &ResolvedTarget,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    timeout: Duration,
) -> Result<RunResult, String> {
    prepare_unobserved_target(target, argv, cwd, root, env, umask, None)?
        .go_and_collect(stdin, timeout)
}

/// Owns a helper waiting at READY and reaps it if execution is abandoned.
pub(crate) struct PreparedTarget {
    target: ResolvedTarget,
    argv: Vec<String>,
    cwd: PathBuf,
    #[cfg(unix)]
    go: Option<File>,
    #[cfg(unix)]
    status: File,
    process: PreparedProcess,
}

/// Inclusive realtime bounds around a target's execution and collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExecutionWindow {
    pub(crate) start: (i64, i64),
    pub(crate) end: (i64, i64),
}

impl ExecutionWindow {
    pub(crate) fn contains(self, value: (i64, i64)) -> bool {
        (0..1_000_000_000).contains(&value.1)
            && (0..1_000_000_000).contains(&self.start.1)
            && (0..1_000_000_000).contains(&self.end.1)
            && self.start <= value
            && value <= self.end
    }
}

fn wall_clock_now() -> Result<(i64, i64), String> {
    let value = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|error| format!("execution wall clock is before epoch: {error}"))?;
    Ok((
        i64::try_from(value.as_secs())
            .map_err(|error| format!("execution wall clock overflow: {error}"))?,
        i64::from(value.subsec_nanos()),
    ))
}

fn completed_window(start: (i64, i64)) -> Result<ExecutionWindow, String> {
    let end = wall_clock_now()?;
    if end < start {
        return Err("execution wall clock moved backwards".into());
    }
    Ok(ExecutionWindow { start, end })
}

/// Describes fixture reuse and the actual realtime interval for each execution.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExecutionEvidence {
    pub(crate) fixture_sharing: bool,
    pub(crate) reference_window: ExecutionWindow,
    pub(crate) dut_window: ExecutionWindow,
}

impl PreparedTarget {
    /// Runs an untraced target and returns its observable process result.
    #[cfg(test)]
    pub(crate) fn go_and_collect(
        self,
        stdin: &[u8],
        timeout: Duration,
    ) -> Result<RunResult, String> {
        self.go_and_collect_timed(stdin, timeout)
            .map(|(result, _)| result)
    }

    pub(crate) fn go_and_collect_timed(
        mut self,
        stdin: &[u8],
        timeout: Duration,
    ) -> Result<(RunResult, ExecutionWindow), String> {
        #[cfg(unix)]
        {
            let start = wall_clock_now()?;
            let started = Instant::now();
            self.go
                .as_mut()
                .expect("live GO writer")
                .write_all(b"GO")
                .map_err(|error| self.phase_error("send GO", error))?;
            self.go.take();
            let exec_error =
                read_exec_status(&mut self.status, remaining_timeout(started, timeout))
                    .map_err(|error| self.phase_error("read exec status", error))?;
            let remaining = remaining_timeout(started, timeout);
            if let Some(error) = exec_error {
                let output = self
                    .process
                    .collect(&[], remaining)
                    .map_err(|process_error| {
                        format_target_process_error(
                            &self.target,
                            &self.argv,
                            &self.cwd,
                            timeout,
                            process_error,
                        )
                    })?;
                return Err(format!(
                    "{}\nstdout={:?} stderr={:?}",
                    format_target_process_error(
                        &self.target,
                        &self.argv,
                        &self.cwd,
                        timeout,
                        ProcessError::Spawn(error),
                    ),
                    output.stdout,
                    output.stderr
                ));
            }
            let output = self
                .process
                .collect(stdin, remaining)
                .map_err(|process_error| {
                    format_target_process_error(
                        &self.target,
                        &self.argv,
                        &self.cwd,
                        timeout,
                        process_error,
                    )
                })?;
            Ok((run_result(output), completed_window(start)?))
        }
        #[cfg(not(unix))]
        {
            let _ = (stdin, timeout);
            Err("controlled target helper requires Unix".to_string())
        }
    }

    fn phase_error(&self, phase: &str, error: io::Error) -> String {
        format!(
            "failed to {phase} for {} variant argv={:?} cwd=`{}`: {error}",
            self.target.label,
            self.argv,
            self.cwd.display()
        )
    }
}

fn remaining_timeout(started: Instant, timeout: Duration) -> Duration {
    timeout.saturating_sub(started.elapsed())
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn prepare_unobserved_target(
    target: &ResolvedTarget,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedTarget, String> {
    prepare_controlled_target(target, argv, cwd, root, env, umask, identity)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_controlled_target(
    target: &ResolvedTarget,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedTarget, String> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;

        const READY_TIMEOUT: Duration = Duration::from_secs(10);
        let (mut parent_ready, child_ready) = pipe_cloexec()
            .map_err(|error| format!("failed to create execution READY channel: {error}"))?;
        let (child_go, parent_go) = pipe_cloexec()
            .map_err(|error| format!("failed to create execution GO channel: {error}"))?;
        let (parent_status, child_status) = pipe_cloexec()
            .map_err(|error| format!("failed to create execution status channel: {error}"))?;
        let ready_fd = child_ready.as_raw_fd();
        let go_fd = child_go.as_raw_fd();
        let status_fd = child_status.as_raw_fd();
        let mut command = Command::new(helper_executable()?);
        command
            .arg("__exec-helper")
            .arg("--exec-kind")
            .arg(match target.kind {
                ExecKind::Native => "native",
                ExecKind::DotnetDll => "dotnet-dll",
            })
            .arg("--target")
            .arg(&target.path)
            .arg("--native-argv0")
            .arg(target.path.file_name().unwrap_or_default())
            .arg("--ready-fd")
            .arg(ready_fd.to_string())
            .arg("--go-fd")
            .arg(go_fd.to_string())
            .arg("--status-fd")
            .arg(status_fd.to_string());
        if let Some((uid, gid)) = identity {
            command
                .arg("--target-uid")
                .arg(uid.to_string())
                .arg("--target-gid")
                .arg(gid.to_string());
        }
        command.arg("--").args(argv);
        command.current_dir(root.join(cwd));
        configure_controlled_child(&mut command, env, umask)?;
        unsafe {
            command.pre_exec(move || {
                set_cloexec_io(ready_fd, false)?;
                set_cloexec_io(go_fd, false)?;
                set_cloexec_io(status_fd, false)?;
                Ok(())
            });
        }
        let process = PreparedProcess::spawn(&mut command).map_err(|error| {
            format_target_process_error(target, argv, cwd, READY_TIMEOUT, error)
        })?;
        drop(child_ready);
        drop(child_go);
        drop(child_status);
        let ready = read_to_end_bounded(&mut parent_ready, READY_TIMEOUT).map_err(|error| {
            format!(
                "failed to receive READY for {} variant argv={argv:?} cwd=`{}`: {error}",
                target.label,
                cwd.display()
            )
        })?;
        if ready != b"READY" {
            return Err(format!(
                "malformed READY for {} variant argv={argv:?} cwd=`{}`: {ready:?}",
                target.label,
                cwd.display()
            ));
        }
        Ok(PreparedTarget {
            target: target.clone(),
            argv: argv.to_vec(),
            cwd: cwd.to_path_buf(),
            go: Some(parent_go),
            status: parent_status,
            process,
        })
    }
    #[cfg(not(unix))]
    {
        let _ = (target, argv, cwd, root, env, umask, identity);
        Err("controlled target helper requires Unix".to_string())
    }
}

#[cfg(test)]
pub(crate) fn run_controlled_umask_probe(
    env: &BTreeMap<String, String>,
    umask: u32,
    cwd: &Path,
) -> Result<ControlledUmaskProbe, String> {
    let mut command = Command::new("/bin/sh");
    command.arg("-c").arg("umask").current_dir(cwd);
    configure_controlled_child(&mut command, env, umask)?;
    let output = crate::utils::process::run_command_with_timeout_and_input(
        &mut command,
        &[],
        Duration::from_secs(10),
    )
    .map_err(|err| format!("controlled umask probe failed: {err:?}"))?;
    let termination = super::comparison::process_outcome::Termination::from_status(output.status);
    let exit_code = termination
        .exit_code()
        .ok_or_else(|| format!("controlled umask probe terminated by signal: {termination:?}"))?;
    if exit_code != 0 || !output.stderr.is_empty() {
        return Err(format!(
            "controlled umask probe rejected: exit={exit_code} stderr={:?}",
            output.stderr
        ));
    }
    let text = std::str::from_utf8(&output.stdout)
        .map_err(|err| format!("controlled umask probe output is not UTF-8: {err}"))?;
    let digits = text.trim();
    let observed_umask = u32::from_str_radix(digits, 8)
        .map_err(|_| format!("controlled umask probe returned invalid octal `{digits}`"))?;
    Ok(ControlledUmaskProbe {
        observed_umask,
        stdout: output.stdout,
        stderr: output.stderr,
        exit_code,
    })
}

fn configure_controlled_child(
    command: &mut Command,
    env: &BTreeMap<String, String>,
    requested_umask: u32,
) -> Result<(), String> {
    validate_process_umask(requested_umask)?;
    let expected = canonical_environment_config(requested_umask)?;
    if env != &expected {
        return Err("controlled target environment is not canonical".to_string());
    }
    command.env_clear();
    for (key, value) in env {
        command.env(key, value);
    }
    apply_process_umask(command, requested_umask)
}

#[cfg(unix)]
fn helper_executable() -> Result<PathBuf, String> {
    #[cfg(test)]
    {
        use std::sync::OnceLock;

        static HELPER: OnceLock<Result<PathBuf, String>> = OnceLock::new();
        HELPER
            .get_or_init(|| {
                let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
                let status = Command::new("cargo")
                    .arg("build")
                    .arg("--quiet")
                    .arg("--manifest-path")
                    .arg(&manifest)
                    .arg("--bin")
                    .arg("coreutils_fuzzer")
                    .status()
                    .map_err(|error| {
                        format!("failed to build execution helper executable: {error}")
                    })?;
                if !status.success() {
                    return Err(format!(
                        "failed to build execution helper executable: status {:?}",
                        status.code()
                    ));
                }
                Ok(Path::new(env!("CARGO_MANIFEST_DIR")).join("target/debug/coreutils_fuzzer"))
            })
            .clone()
    }
    #[cfg(not(test))]
    std::env::current_exe()
        .map_err(|error| format!("failed to resolve execution helper executable: {error}"))
}

#[cfg(unix)]
pub(super) fn pipe_cloexec() -> io::Result<(File, File)> {
    #[cfg(target_os = "linux")]
    {
        const O_CLOEXEC: i32 = 0o2_000_000;
        unsafe extern "C" {
            fn pipe2(fds: *mut i32, flags: i32) -> i32;
        }

        let mut fds = [-1, -1];
        if unsafe { pipe2(fds.as_mut_ptr(), O_CLOEXEC) } < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) })
    }
    #[cfg(not(target_os = "linux"))]
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled target helper requires Linux close-on-exec pipes",
    ))
}

#[cfg(unix)]
pub(super) fn set_cloexec_io(fd: i32, enabled: bool) -> io::Result<()> {
    const F_GETFD: i32 = 1;
    const F_SETFD: i32 = 2;
    const FD_CLOEXEC: i32 = 1;
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    let flags = unsafe { fcntl(fd, F_GETFD) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    let updated = if enabled {
        flags | FD_CLOEXEC
    } else {
        flags & !FD_CLOEXEC
    };
    if unsafe { fcntl(fd, F_SETFD, updated) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn set_nonblocking(fd: i32, enabled: bool) -> io::Result<i32> {
    const F_GETFL: i32 = 3;
    const O_NONBLOCK: i32 = 0o4_000;
    let flags = get_file_status_flags(fd, F_GETFL)?;
    set_file_status_flags(
        fd,
        if enabled {
            flags | O_NONBLOCK
        } else {
            flags & !O_NONBLOCK
        },
    )?;
    Ok(flags)
}

#[cfg(not(target_os = "linux"))]
fn set_nonblocking(_fd: i32, _enabled: bool) -> io::Result<i32> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled target helper requires Linux nonblocking pipes",
    ))
}

#[cfg(target_os = "linux")]
fn get_file_status_flags(fd: i32, command: i32) -> io::Result<i32> {
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    let flags = unsafe { fcntl(fd, command) };
    if flags < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(flags)
    }
}

#[cfg(target_os = "linux")]
fn set_file_status_flags(fd: i32, flags: i32) -> io::Result<()> {
    const F_SETFL: i32 = 4;
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    if unsafe { fcntl(fd, F_SETFL, flags) } < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

#[cfg(not(target_os = "linux"))]
fn set_file_status_flags(_fd: i32, _flags: i32) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled target helper requires Linux nonblocking pipes",
    ))
}

#[cfg(unix)]
fn read_exec_status(status: &mut File, timeout: Duration) -> io::Result<Option<String>> {
    let frame = read_to_end_bounded(status, timeout)?;
    if frame.is_empty() {
        return Ok(None);
    }
    if frame.len() < 4 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "truncated exec status frame",
        ));
    }
    let mut length = [0_u8; 4];
    length.copy_from_slice(&frame[..4]);
    let length = u32::from_be_bytes(length) as usize;
    if length > 1024 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "exec status frame is too large",
        ));
    }
    if frame.len() != length + 4 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "malformed exec status frame length",
        ));
    }
    Ok(Some(String::from_utf8_lossy(&frame[4..]).into_owned()))
}

#[cfg(unix)]
fn read_to_end_bounded(stream: &mut File, timeout: Duration) -> io::Result<Vec<u8>> {
    if timeout.is_zero() {
        return Err(io::Error::new(io::ErrorKind::TimedOut, "channel timed out"));
    }
    let flags = set_nonblocking(stream.as_raw_fd(), true)?;
    let deadline = Instant::now() + timeout;
    let mut bytes = Vec::new();
    loop {
        match stream.read_to_end(&mut bytes) {
            Ok(_) => {
                set_file_status_flags(stream.as_raw_fd(), flags)?;
                return Ok(bytes);
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if Instant::now() >= deadline {
                    set_file_status_flags(stream.as_raw_fd(), flags)?;
                    return Err(io::Error::new(io::ErrorKind::TimedOut, "channel timed out"));
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(unix)]
fn write_exec_error(status: &mut File, message: &str) -> io::Result<()> {
    let bytes = message.as_bytes();
    let length = u32::try_from(bytes.len())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "exec error is too large"))?;
    status.write_all(&length.to_be_bytes())?;
    status.write_all(bytes)
}

#[cfg(unix)]
pub(crate) fn run_exec_helper(args: ExecHelperArgs) -> ! {
    use std::os::unix::process::CommandExt;

    let mut ready = unsafe { File::from_raw_fd(args.ready_fd) };
    let mut go_reader = unsafe { File::from_raw_fd(args.go_fd) };
    let mut status = unsafe { File::from_raw_fd(args.status_fd) };
    let fail = |status: &mut File, message: String| -> ! {
        let _ = write_exec_error(status, &message);
        std::process::exit(127);
    };
    if let Err(error) = set_cloexec_io(args.status_fd, true) {
        fail(
            &mut status,
            format!("failed to restore exec-status close-on-exec: {error}"),
        );
    }
    if let Err(error) = ready.write_all(b"READY") {
        fail(&mut status, format!("failed to send READY: {error}"));
    }
    drop(ready);
    let mut go = Vec::new();
    if let Err(error) = go_reader.read_to_end(&mut go) {
        fail(&mut status, format!("failed to receive GO: {error}"));
    }
    if go != b"GO" {
        fail(&mut status, format!("malformed GO: {go:?}"));
    }
    drop(go_reader);

    let mut command = match args.exec_kind {
        ExecKind::Native => {
            let mut command = Command::new(&args.target);
            command.arg0(&args.native_argv0).args(&args.argv);
            command
        }
        ExecKind::DotnetDll => {
            let mut command = Command::new("dotnet");
            command.arg(&args.target).args(&args.argv);
            command
        }
    };
    if let (Some(uid), Some(gid)) = (args.target_uid, args.target_gid) {
        if let Err(error) = set_current_process_identity(uid, gid) {
            fail(&mut status, error);
        }
    }
    let error = command.exec();
    fail(&mut status, error.to_string())
}

#[cfg(unix)]
fn set_current_process_identity(uid: u32, gid: u32) -> Result<(), String> {
    unsafe extern "C" {
        fn setgroups(size: usize, groups: *const u32) -> i32;
        fn setgid(gid: u32) -> i32;
        fn setuid(uid: u32) -> i32;
    }
    if unsafe { setgroups(0, std::ptr::null()) } != 0 {
        return Err(format!(
            "failed to clear supplementary groups: {}",
            io::Error::last_os_error()
        ));
    }
    if unsafe { setgid(gid) } != 0 {
        return Err(format!(
            "failed to set target gid {gid}: {}",
            io::Error::last_os_error()
        ));
    }
    if unsafe { setuid(uid) } != 0 {
        return Err(format!(
            "failed to set target uid {uid}: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(not(unix))]
pub(crate) fn run_exec_helper(_args: ExecHelperArgs) -> ! {
    eprintln!("controlled target helper requires Unix");
    std::process::exit(127)
}

fn format_target_process_error(
    target: &ResolvedTarget,
    argv: &[String],
    cwd: &Path,
    timeout: Duration,
    err: ProcessError,
) -> String {
    let context = format!(
        "{} variant argv={argv:?} cwd=`{}`",
        target.label,
        cwd.display()
    );
    let outcome = if matches!(&err, ProcessError::Timeout) {
        FUZZER_TIMEOUT
    } else if target.kind == ExecKind::DotnetDll {
        FUZZER_DOTNET_RUNTIME_FAILURE
    } else {
        FUZZER_TARGET_SPAWN_FAILURE
    };
    let message = match err {
        ProcessError::Spawn(message) => format!("failed to run {context}: {message}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdinUnavailable => format!("stdin pipe unavailable for {context}"),
        ProcessError::StdinWrite(message) => {
            format!("failed to write stdin for {context}: {message}")
        }
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdinThreadPanic => format!("stdin writer thread panicked for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdoutUnavailable => format!("stdout pipe unavailable for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StderrUnavailable => format!("stderr pipe unavailable for {context}"),
        ProcessError::StdoutRead(message) => {
            format!("failed to read stdout for {context}: {message}")
        }
        ProcessError::StderrRead(message) => {
            format!("failed to read stderr for {context}: {message}")
        }
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdoutThreadPanic => format!("stdout reader thread panicked for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StderrThreadPanic => format!("stderr reader thread panicked for {context}"),
        ProcessError::Wait(message) => format!("failed while waiting for {context}: {message}"),
        ProcessError::Kill(message) => format!("failed to terminate {context}: {message}"),
        ProcessError::Timeout => format!("{context} timed out after {timeout:?}"),
        ProcessError::InvalidTimeout => {
            format!("timeout for {context} exceeds the platform clock range")
        }
        ProcessError::Channel { name, message } => {
            format!("{name} channel failed for {context}: {message}")
        }
    };
    format!("{}\n{message}", fuzzer_outcome_marker(outcome))
}

#[cfg(test)]
mod controlled_execution_tests {
    use super::super::comparison::fs_snapshot::snapshot_fs;
    use super::{
        canonical_environment_config, format_target_process_error, prepare_unobserved_target,
        read_exec_status, run_controlled_target, run_controlled_umask_probe,
        run_controlled_variant,
    };
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::system_state_concretizer::materialize_fixture;
    use crate::fuzz::{GeneratedCase, ResolvedPaths, ResolvedTarget, RunResult, VariantKind};
    use crate::utils::cli::ExecKind;
    use crate::utils::process::ProcessError;
    use crate::{
        FUZZER_DOTNET_RUNTIME_FAILURE, FUZZER_OUTCOME_MARKER_PREFIX, FUZZER_TARGET_SPAWN_FAILURE,
        FUZZER_TIMEOUT,
    };
    use std::fs;
    use std::io::{self, Write};
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    // A native target spawn error must carry the stable target-spawn outcome marker.
    #[test]
    fn native_target_spawn_error_has_target_spawn_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/missing/native-target"),
            label: "dut",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Spawn("not found".to_string()),
        );

        assert!(error.starts_with(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_TARGET_SPAWN_FAILURE}"
        )));
    }

    // A .NET host spawn error must carry the stable runtime outcome marker.
    #[test]
    fn dotnet_target_spawn_error_has_runtime_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::DotnetDll,
            path: PathBuf::from("/tmp/dut.dll"),
            label: "dut",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Spawn("dotnet missing".to_string()),
        );

        assert!(error.starts_with(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_DOTNET_RUNTIME_FAILURE}"
        )));
    }

    // A target process timeout must carry the stable fuzzer-timeout outcome marker.
    #[test]
    fn target_timeout_error_has_timeout_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/true"),
            label: "reference",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Timeout,
        );

        assert!(error.starts_with(&format!("{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_TIMEOUT}")));
    }

    #[cfg(target_os = "linux")]
    fn helper_pid_for_target(target: &Path) -> u32 {
        use std::os::unix::ffi::OsStrExt;

        let target = target.as_os_str().as_bytes();
        std::fs::read_dir("/proc")
            .unwrap()
            .filter_map(Result::ok)
            .filter_map(|entry| entry.file_name().to_str()?.parse::<u32>().ok())
            .find(|pid| {
                std::fs::read(format!("/proc/{pid}/cmdline"))
                    .is_ok_and(|cmdline| cmdline.split(|byte| *byte == 0).any(|arg| arg == target))
            })
            .expect("live execution helper")
    }

    #[cfg(target_os = "linux")]
    fn assert_process_reaped(pid: u32) {
        let process = PathBuf::from(format!("/proc/{pid}"));
        let deadline = std::time::Instant::now() + Duration::from_secs(1);
        while process.exists() && std::time::Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(!process.exists(), "process {pid} was not reaped");
    }

    fn run_pinned_gnu_chmod(case: &GeneratedCase, root: &Path) -> RunResult {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join("_build/coreutils/src/chmod"),
            label: "reference",
        };
        let environment = canonical_environment_config(0o022).unwrap();
        run_controlled_target(
            &target,
            &case.argv,
            &case.stdin,
            &case.cwd,
            root,
            &environment,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap()
    }

    // The separately executed probe observes the selected implementation-campaign umask.
    #[test]
    fn controlled_child_observes_selected_umask() {
        let environment = canonical_environment_config(0o027).unwrap();
        let probe =
            run_controlled_umask_probe(&environment, 0o027, PathBuf::from(".").as_path()).unwrap();

        assert_eq!(probe.observed_umask, 0o027);
    }

    // Reference and DUT roles receive the same cwd, environment, umask, stdin, streams, and argv0.
    #[cfg(unix)]
    #[test]
    fn controlled_target_roles_share_exact_child_configuration() {
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let env = canonical_environment_config(0o027).unwrap();
        let argv = vec![
            "-c".to_string(),
            "read input; printf 'cwd=%s\\nstdin=%s\\n' \"$PWD\" \"$input\"; \
             tr '\\0' '\\n' </proc/$$/environ; \
             printf 'argv0=%s umask=' \"$0\"; umask; printf 'stderr=%s\\n' \"$input\" >&2"
                .to_string(),
        ];
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("work")).unwrap();
        let run = |kind| {
            run_controlled_variant(
                kind,
                &paths,
                &argv,
                b"payload\n",
                Path::new("work"),
                root.path(),
                &env,
                0o027,
                Duration::from_secs(10),
            )
            .unwrap()
        };

        let reference = run(VariantKind::Ref);
        let dut = run(VariantKind::Dut);
        let expected = format!(
            "cwd={}\nstdin=payload\nLANG=C\nLC_ALL=C\nPATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin\nQUOTING_STYLE=literal\nTERM=dumb\nTZ=UTC0\nargv0=sh umask=0027\n",
            root.path().join("work").display()
        );
        assert_eq!(reference, dut);
        assert_eq!(reference.termination.exit_code(), Some(0));
        assert_eq!(reference.stdout, expected.as_bytes());
        assert_eq!(reference.stderr, b"stderr=payload\n");
    }

    // A READY helper must not execute its target or expose target stdout before GO.
    #[cfg(unix)]
    #[test]
    fn controlled_target_target_waits_for_go_before_target_effects() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        };
        let argv = vec![
            "-c".to_string(),
            "printf target-stdout; printf target-effect > marker".to_string(),
        ];
        let env = canonical_environment_config(0o022).unwrap();
        let prepared = prepare_unobserved_target(
            &target,
            &argv,
            Path::new("."),
            root.path(),
            &env,
            0o022,
            None,
        )
        .unwrap();

        assert!(!root.path().join("marker").exists());

        let result = prepared
            .go_and_collect(&[], Duration::from_secs(10))
            .unwrap();
        assert_eq!(result.stdout, b"target-stdout");
        assert_eq!(
            std::fs::read(root.path().join("marker")).unwrap(),
            b"target-effect"
        );
    }

    // An unprivileged helper reaches READY before a forbidden target identity fails after GO.
    #[cfg(target_os = "linux")]
    #[test]
    fn target_identity_failure_occurs_after_ready_before_target_effects() {
        unsafe extern "C" {
            fn geteuid() -> u32;
        }
        let uid = unsafe { geteuid() };
        if uid == 0 {
            return;
        }
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let prepared = prepare_unobserved_target(
            &target,
            &["-c".into(), ": > target-effect".into()],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            Some((0, 0)),
        )
        .unwrap();
        let status = fs::read_to_string(format!("/proc/{}/status", prepared.process.id())).unwrap();
        let helper_uid = status
            .lines()
            .find_map(|line| line.strip_prefix("Uid:"))
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .parse::<u32>()
            .unwrap();
        assert_eq!(helper_uid, uid);
        assert!(!root.path().join("target-effect").exists());

        let error = prepared
            .go_and_collect(&[], Duration::from_secs(10))
            .unwrap_err();

        assert!(
            error.contains("failed to clear supplementary groups"),
            "{error}"
        );
        assert!(error.contains(FUZZER_TARGET_SPAWN_FAILURE), "{error}");
        assert!(!root.path().join("target-effect").exists());
    }

    // A successful exec closes the status channel without altering target stdout or stderr.
    #[cfg(unix)]
    #[test]
    fn controlled_target_success_reports_status_eof_and_untouched_streams() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        };
        let argv = vec![
            "-c".to_string(),
            "printf 'READY GO stdout'; printf 'READY GO stderr' >&2".to_string(),
        ];
        let env = canonical_environment_config(0o022).unwrap();

        let result = run_controlled_target(
            &target,
            &argv,
            &[],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap();

        assert_eq!(result.termination.exit_code(), Some(0));
        assert_eq!(result.stdout, b"READY GO stdout");
        assert_eq!(result.stderr, b"READY GO stderr");
    }

    // An invalid target returns one contextual exec frame without leaking protocol bytes.
    #[cfg(unix)]
    #[test]
    fn controlled_target_invalid_target_returns_one_contextual_exec_error() {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("work")).unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("missing-chmod"),
            label: "reference",
        };
        let env = canonical_environment_config(0o022).unwrap();

        let error = run_controlled_target(
            &target,
            &[],
            &[],
            Path::new("work"),
            root.path(),
            &env,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap_err();

        assert_eq!(error.matches("failed to run reference variant").count(), 1);
        assert!(error.contains("cwd=`work`"));
        assert!(error.contains("stdout=[] stderr=[]"));
        assert!(!error.contains("READY"));
        assert!(!error.contains(" GO"));
    }

    // Dropping a READY helper before GO kills and reaps the blocked child.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_target_drop_before_go_kills_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-drop"),
            label: "reference",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let prepared =
            prepare_unobserved_target(&target, &[], Path::new("."), root.path(), &env, 0o022, None)
                .unwrap();
        let pid = helper_pid_for_target(&target.path);

        drop(prepared);

        assert_process_reaped(pid);
    }

    // A malformed control message fails closed and the helper is reaped.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_target_malformed_go_fails_closed_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-malformed"),
            label: "dut",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let mut prepared =
            prepare_unobserved_target(&target, &[], Path::new("."), root.path(), &env, 0o022, None)
                .unwrap();
        let pid = helper_pid_for_target(&target.path);

        prepared.go.as_mut().unwrap().write_all(b"NO").unwrap();
        prepared.go.take();
        let error = read_exec_status(&mut prepared.status, Duration::from_secs(10))
            .unwrap()
            .unwrap();
        let output = prepared
            .process
            .collect(&[], Duration::from_secs(10))
            .unwrap();

        assert_eq!(error, "malformed GO: [78, 79]");
        assert_eq!(
            super::super::comparison::process_outcome::Termination::from_status(output.status)
                .exit_code(),
            Some(127)
        );
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
        assert_process_reaped(pid);
    }

    // An EOF control message fails closed and the helper is reaped.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_target_go_eof_fails_closed_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-eof"),
            label: "dut",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let mut prepared =
            prepare_unobserved_target(&target, &[], Path::new("."), root.path(), &env, 0o022, None)
                .unwrap();
        let pid = helper_pid_for_target(&target.path);

        prepared.go.take();
        let error = read_exec_status(&mut prepared.status, Duration::from_secs(10))
            .unwrap()
            .unwrap();
        let output = prepared
            .process
            .collect(&[], Duration::from_secs(10))
            .unwrap();

        assert_eq!(error, "malformed GO: []");
        assert_eq!(
            super::super::comparison::process_outcome::Termination::from_status(output.status)
                .exit_code(),
            Some(127)
        );
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
        assert_process_reaped(pid);
    }

    // The pinned GNU chmod must process the parent operand before the inaccessible nested operand.
    #[cfg(unix)]
    #[test]
    fn pinned_gnu_chmod_restores_access_in_operand_order() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let case = scenario_case("chmod", 40).unwrap();
        let root = tempfile::tempdir().unwrap();
        materialize_fixture(root.path(), &case.fixture).unwrap();
        let parent = root.path().join("d");
        let child = parent.join("e");
        match fs::symlink_metadata(&child) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&parent, fs::Permissions::from_mode(0o700)).unwrap();
                fs::set_permissions(&child, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }
        assert_eq!(
            snapshot_fs(root.path()).unwrap().get("d").unwrap().kind,
            "inaccessible"
        );

        let result = run_pinned_gnu_chmod(&case, root.path());
        let snapshot = snapshot_fs(root.path()).unwrap();

        assert_eq!(result.termination.exit_code(), Some(0));
        assert!(result.stdout.is_empty());
        assert!(result.stderr.is_empty());
        assert_eq!(snapshot.get("d").unwrap().mode_octal, "0700");
        assert_eq!(snapshot.get("d/e").unwrap().mode_octal, "0700");
    }

    // An observed access denial must not prevent pinned GNU chmod from changing a later operand.
    #[cfg(unix)]
    #[test]
    fn pinned_gnu_chmod_continues_after_observed_inaccessible_operand() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let case = scenario_case("chmod", 41).unwrap();
        let root = tempfile::tempdir().unwrap();
        materialize_fixture(root.path(), &case.fixture).unwrap();
        let blocked = root.path().join("blocked");
        match fs::symlink_metadata(blocked.join("child")) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }
        assert_eq!(
            snapshot_fs(root.path())
                .unwrap()
                .get("blocked")
                .unwrap()
                .kind,
            "inaccessible"
        );

        let result = run_pinned_gnu_chmod(&case, root.path());
        let snapshot = snapshot_fs(root.path()).unwrap();
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();

        assert_eq!(result.termination.exit_code(), Some(1));
        assert!(result.stdout.is_empty());
        assert_eq!(snapshot.get("tree/root-file").unwrap().mode_octal, "0600");
    }
}
