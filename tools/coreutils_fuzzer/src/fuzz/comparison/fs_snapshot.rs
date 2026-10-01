use crate::fuzz::{FsNodeSnapshot, FsSnapshot, FsTimes, HostInodeKeySnapshot};
use crate::utils::paths::format_path_error;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, Read, Seek};
use std::path::Path;

#[cfg(unix)]
#[repr(C)]
struct SnapshotTimespec {
    tv_sec: i64,
    tv_nsec: i64,
}

#[cfg(unix)]
unsafe extern "C" {
    fn utimensat(
        dirfd: i32,
        pathname: *const std::os::raw::c_char,
        times: *const SnapshotTimespec,
        flags: i32,
    ) -> i32;
}

#[cfg(unix)]
pub(crate) fn restore_path_times(
    path: &Path,
    times: FsTimes,
    is_symlink: bool,
) -> Result<(), String> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    const AT_FDCWD: i32 = -100;
    const AT_SYMLINK_NOFOLLOW: i32 = 0x100;
    let metadata = if is_symlink {
        fs::symlink_metadata(path)
    } else {
        fs::metadata(path)
    }
    .map_err(|error| format_path_error("read timestamp restoration metadata", path, error))?;
    let current = times_from_metadata(&metadata);
    if current.atime_sec == times.atime_sec
        && current.atime_nsec == times.atime_nsec
        && current.mtime_sec == times.mtime_sec
        && current.mtime_nsec == times.mtime_nsec
    {
        // Even an otherwise redundant utimensat changes ctime.
        return Ok(());
    }
    let display = path.display().to_string();
    let path = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
        format!("filesystem snapshot path contains an unsupported NUL byte: `{display}`")
    })?;
    let values = [
        SnapshotTimespec {
            tv_sec: times.atime_sec,
            tv_nsec: times.atime_nsec,
        },
        SnapshotTimespec {
            tv_sec: times.mtime_sec,
            tv_nsec: times.mtime_nsec,
        },
    ];
    let flags = if is_symlink { AT_SYMLINK_NOFOLLOW } else { 0 };
    let status = unsafe { utimensat(AT_FDCWD, path.as_ptr(), values.as_ptr(), flags) };
    if status == 0 {
        Ok(())
    } else {
        Err(format!(
            "failed to restore snapshot times on `{display}`: {}",
            io::Error::last_os_error()
        ))
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[allow(deprecated)] // The convenience block-size getter is unsigned; this ABI field is signed.
fn raw_stat_metadata_from_metadata(
    metadata: &fs::Metadata,
) -> crate::utils::world_json::RawStatMetadataJson {
    use std::os::linux::fs::MetadataExt;
    let raw = metadata.as_raw_stat();
    let device_number: u64 = raw.st_rdev;
    let io_block_bytes: i64 = raw.st_blksize;
    crate::utils::world_json::RawStatMetadataJson::Known {
        device_number,
        io_block_bytes,
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
fn raw_stat_metadata_from_metadata(
    _metadata: &fs::Metadata,
) -> crate::utils::world_json::RawStatMetadataJson {
    crate::utils::world_json::RawStatMetadataJson::Unknown
}

/// Converts a checked filesystem-capture result into the string-error form
/// used by non-test callers, preserving the `FsCaptureError` display text.
fn to_string_error<T>(result: Result<T, FsCaptureError>) -> Result<T, String> {
    result.map_err(|error| error.to_string())
}

#[cfg(test)]
pub(crate) fn snapshot_fs(root: &Path) -> Result<FsSnapshot, String> {
    to_string_error(snapshot_fs_checked(root))
}

#[cfg(test)]
pub(crate) fn snapshot_fs_without_restore(root: &Path) -> Result<FsSnapshot, String> {
    to_string_error(snapshot_fs_with_observer_restore(root, false, None, false))
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FsCaptureError {
    Encoding { field: &'static str },
    Other(String),
}

impl std::fmt::Display for FsCaptureError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Encoding { field } => {
                write!(formatter, "filesystem snapshot {field} is not UTF-8")
            }
            Self::Other(message) => formatter.write_str(message),
        }
    }
}

impl From<String> for FsCaptureError {
    fn from(message: String) -> Self {
        Self::Other(message)
    }
}

#[cfg(test)]
pub(crate) fn snapshot_fs_checked(root: &Path) -> Result<FsSnapshot, FsCaptureError> {
    snapshot_fs_with_observer_restore(root, true, None, false)
}

struct SnapshotFileHandle {
    file: fs::File,
    #[cfg(unix)]
    dev: u64,
    #[cfg(unix)]
    ino: u64,
}

pub(crate) type IdentityTransitionEvidence = BTreeSet<(String, String)>;

struct IdentityHandle {
    file: fs::File,
    pre_paths: Vec<String>,
}

/// Retains readable files and object identities across one execution.
#[derive(Default)]
pub(crate) struct SnapshotObserver {
    files: BTreeMap<HostInodeKeySnapshot, SnapshotFileHandle>,
    symlinks: BTreeMap<HostInodeKeySnapshot, String>,
    identities: BTreeMap<HostInodeKeySnapshot, IdentityHandle>,
}

/// Captures initial filesystem state and retains handles for later observation.
fn snapshot_pre_checked(
    root: &Path,
    restore_observer_times: bool,
) -> Result<(FsSnapshot, SnapshotObserver), FsCaptureError> {
    let mut observer = SnapshotObserver::default();
    let snapshot =
        snapshot_fs_with_observer_restore(root, restore_observer_times, Some(&mut observer), true)?;
    Ok((snapshot, observer))
}

#[cfg(test)]
pub(crate) fn snapshot_fs_pre_unrestored(
    root: &Path,
) -> Result<(FsSnapshot, SnapshotObserver), String> {
    to_string_error(snapshot_pre_checked(root, false))
}

/// Captures prestate using the fixture's existing observer timestamp policy.
pub(crate) fn snapshot_fs_pre_with_restore(
    root: &Path,
    restore_observer_times: bool,
) -> Result<(FsSnapshot, SnapshotObserver), String> {
    to_string_error(snapshot_pre_checked(root, restore_observer_times))
}

#[cfg(test)]
pub(crate) fn snapshot_fs_pre(root: &Path) -> Result<(FsSnapshot, SnapshotObserver), String> {
    to_string_error(snapshot_fs_pre_checked(root))
}

#[cfg(test)]
pub(crate) fn snapshot_fs_pre_checked(
    root: &Path,
) -> Result<(FsSnapshot, SnapshotObserver), FsCaptureError> {
    snapshot_pre_checked(root, true)
}

pub(crate) fn snapshot_fs_post(
    root: &Path,
    observer: &mut SnapshotObserver,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), String> {
    to_string_error(snapshot_fs_post_checked(root, observer))
}

pub(crate) fn snapshot_fs_post_checked(
    root: &Path,
    observer: &mut SnapshotObserver,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), FsCaptureError> {
    // This is the terminal observation for an iteration. Avoid restoring atime here:
    // utimensat would itself advance ctime and obscure whether the utility changed it.
    snapshot_fs_post_with_restore_checked(root, observer, false)
}

fn snapshot_fs_post_with_restore_checked(
    root: &Path,
    observer: &mut SnapshotObserver,
    restore_observer_times: bool,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), FsCaptureError> {
    let snapshot =
        snapshot_fs_with_observer_restore(root, restore_observer_times, Some(observer), false)?;
    let evidence =
        identity_transition_evidence(observer, &snapshot).map_err(FsCaptureError::from)?;
    Ok((snapshot, evidence))
}

#[cfg(target_os = "linux")]
fn observe_identity(
    observer: &mut SnapshotObserver,
    path: &Path,
    relative_path: &str,
    expected_key: HostInodeKeySnapshot,
) -> Result<(), String> {
    use std::ffi::CString;
    use std::os::fd::FromRawFd;
    use std::os::raw::{c_char, c_int};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;

    if let Some(handle) = observer.identities.get_mut(&expected_key) {
        handle.pre_paths.push(relative_path.to_string());
        return Ok(());
    }

    unsafe extern "C" {
        fn open(pathname: *const c_char, flags: c_int, ...) -> c_int;
    }
    const O_NOFOLLOW: i32 = 0o400_000;
    const O_CLOEXEC: i32 = 0o2_000_000;
    const O_PATH: i32 = 0o10_000_000;
    let raw_path = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
        format!(
            "filesystem identity path contains an unsupported NUL byte: `{}`",
            path.display()
        )
    })?;
    let descriptor = unsafe { open(raw_path.as_ptr(), O_PATH | O_NOFOLLOW | O_CLOEXEC) };
    if descriptor < 0 {
        return Err(format_path_error(
            "open identity handle",
            path,
            io::Error::last_os_error(),
        ));
    }
    let file = unsafe { File::from_raw_fd(descriptor) };
    let metadata = file
        .metadata()
        .map_err(|error| format_path_error("read identity handle metadata", path, error))?;
    let actual_key = HostInodeKeySnapshot {
        device: metadata.dev(),
        inode: metadata.ino(),
    };
    if actual_key != expected_key {
        return Err(format!(
            "filesystem node changed while opening identity handle `{}`",
            path.display()
        ));
    }
    observer.identities.insert(
        expected_key,
        IdentityHandle {
            file,
            pre_paths: vec![relative_path.to_string()],
        },
    );
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn observe_identity(
    _observer: &mut SnapshotObserver,
    path: &Path,
    _relative_path: &str,
    _expected_key: HostInodeKeySnapshot,
) -> Result<(), String> {
    Err(format!(
        "filesystem identity transition observation requires Linux O_PATH for `{}`",
        path.display()
    ))
}

fn identity_transition_evidence(
    observer: &SnapshotObserver,
    post: &FsSnapshot,
) -> Result<IdentityTransitionEvidence, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let mut post_paths = BTreeMap::<HostInodeKeySnapshot, Vec<&String>>::new();
        for (path, node) in post {
            let key = node
                .host_key
                .ok_or_else(|| format!("fs.identity unsupported: post-state path `{path}`"))?;
            post_paths.entry(key).or_default().push(path);
        }

        let mut evidence = BTreeSet::new();
        for (expected_key, handle) in &observer.identities {
            let metadata = handle.file.metadata().map_err(|error| {
                format!("failed to read retained identity handle metadata: {error}")
            })?;
            let retained_key = HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            };
            if retained_key != *expected_key {
                return Err("retained filesystem identity changed unexpectedly".to_string());
            }
            if let Some(paths) = post_paths.get(&retained_key) {
                for pre_path in &handle.pre_paths {
                    for post_path in paths {
                        evidence.insert((pre_path.clone(), (*post_path).clone()));
                    }
                }
            }
        }
        Ok(evidence)
    }
    #[cfg(not(unix))]
    {
        let _ = (observer, post);
        Err("filesystem identity transition observation requires Unix metadata".to_string())
    }
}

/// Enumerates directory entries through an observer-only O_NOATIME descriptor.
#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
fn read_snapshot_directory(path: &Path) -> io::Result<Vec<std::path::PathBuf>> {
    use std::os::fd::IntoRawFd;
    use std::os::unix::{ffi::OsStrExt, fs::OpenOptionsExt};
    #[repr(C)]
    struct Dirent {
        inode: u64,
        offset: i64,
        length: u16,
        kind: u8,
        name: [std::ffi::c_char; 256],
    }
    unsafe extern "C" {
        fn fdopendir(fd: i32) -> *mut std::ffi::c_void;
        fn readdir(dir: *mut std::ffi::c_void) -> *mut Dirent;
        fn closedir(dir: *mut std::ffi::c_void) -> i32;
        fn close(fd: i32) -> i32;
        fn __errno_location() -> *mut i32;
    }
    struct Directory(*mut std::ffi::c_void);
    impl Drop for Directory {
        fn drop(&mut self) {
            unsafe {
                closedir(self.0);
            }
        }
    }
    let file = fs::OpenOptions::new()
        .read(true)
        .custom_flags(0o1_000_000 | 0o200_000)
        .open(path)?;
    let fd = file.into_raw_fd();
    let pointer = unsafe { fdopendir(fd) };
    if pointer.is_null() {
        let error = io::Error::last_os_error();
        unsafe {
            close(fd);
        }
        return Err(error);
    }
    let directory = Directory(pointer);
    let mut entries = Vec::new();
    loop {
        unsafe {
            *__errno_location() = 0;
        }
        let entry = unsafe { readdir(directory.0) };
        if entry.is_null() {
            let errno = unsafe { *__errno_location() };
            if errno != 0 {
                return Err(io::Error::from_raw_os_error(errno));
            }
            break;
        }
        let name = unsafe { std::ffi::CStr::from_ptr((*entry).name.as_ptr()) }.to_bytes();
        if name != b"." && name != b".." {
            entries.push(path.join(std::ffi::OsStr::from_bytes(name)));
        }
    }
    Ok(entries)
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
fn read_snapshot_directory(path: &Path) -> io::Result<Vec<std::path::PathBuf>> {
    fs::read_dir(path)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect()
}

fn open_snapshot_file(path: &Path) -> Result<SnapshotFileHandle, String> {
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(0o1_000_000); // O_NOATIME affects this observer handle only.
    }
    let file = options
        .open(path)
        .map_err(|error| format_path_error("read file without atime effects", path, error))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let path_metadata = fs::symlink_metadata(path)
            .map_err(|error| format_path_error("read metadata", path, error))?;
        let handle_metadata = file
            .metadata()
            .map_err(|error| format_path_error("read file metadata", path, error))?;
        if !path_metadata.is_file()
            || (path_metadata.dev(), path_metadata.ino())
                != (handle_metadata.dev(), handle_metadata.ino())
        {
            return Err(format!(
                "filesystem node changed while opening `{}`",
                path.display()
            ));
        }
        Ok(SnapshotFileHandle {
            file,
            dev: handle_metadata.dev(),
            ino: handle_metadata.ino(),
        })
    }
    #[cfg(not(unix))]
    {
        let _ = file;
        Err("filesystem snapshot observer requires Unix filesystem identity".to_string())
    }
}

fn snapshot_handle_matches(handle: &SnapshotFileHandle, metadata: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        (handle.dev, handle.ino) == (metadata.dev(), metadata.ino())
    }
    #[cfg(not(unix))]
    {
        let _ = (handle, metadata);
        false
    }
}

fn read_snapshot_handle(handle: &mut SnapshotFileHandle, path: &Path) -> Result<Vec<u8>, String> {
    handle
        .file
        .rewind()
        .map_err(|error| format_path_error("read file", path, error))?;
    let mut data = Vec::new();
    handle
        .file
        .read_to_end(&mut data)
        .map_err(|error| format_path_error("read file", path, error))?;
    Ok(data)
}

fn snapshot_fs_with_observer_restore(
    root: &Path,
    restore_observer_times: bool,
    observer: Option<&mut SnapshotObserver>,
    capture_handles: bool,
) -> Result<FsSnapshot, FsCaptureError> {
    fn utf8_field(value: &std::ffi::OsStr, field: &'static str) -> Result<String, FsCaptureError> {
        value
            .to_str()
            .map(str::to_owned)
            .ok_or(FsCaptureError::Encoding { field })
    }

    fn record_inaccessible(
        out: &mut FsSnapshot,
        rel: String,
        host_key: Option<HostInodeKeySnapshot>,
    ) {
        out.insert(
            rel,
            FsNodeSnapshot {
                raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
                kind: "inaccessible".to_string(),
                mode_octal: String::new(),
                times: FsTimes::default(),
                uid: None,
                gid: None,
                logical_size: None,
                allocated_512_blocks: None,
                preferred_io_block_bytes: None,
                target: String::new(),
                data: Vec::new(),
                host_key,
                link_count: None,
            },
        );
    }

    fn walk(
        base: &Path,
        current: &Path,
        out: &mut FsSnapshot,
        restore_observer_times: bool,
        observer: &mut Option<&mut SnapshotObserver>,
        capture_handles: bool,
    ) -> Result<(), FsCaptureError> {
        let rel = if current == base {
            ".".to_string()
        } else {
            let relative = current
                .strip_prefix(base)
                .map_err(|e| format!("failed to relativize `{}`: {e}", current.display()))?;
            utf8_field(relative.as_os_str(), "relative path")?
        };

        let metadata = match fs::symlink_metadata(current) {
            Ok(meta) => meta,
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {
                record_inaccessible(out, rel, None);
                return Ok(());
            }
            Err(e) => return Err(format_path_error("read metadata", current, e).into()),
        };
        #[cfg(unix)]
        let host_key = {
            use std::os::unix::fs::MetadataExt;
            Some(HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        };
        #[cfg(not(unix))]
        let host_key = None;
        if capture_handles {
            let key = host_key.ok_or_else(|| {
                format!(
                    "filesystem identity transition observation is unsupported for `{}`",
                    current.display()
                )
            })?;
            let observer = observer
                .as_deref_mut()
                .ok_or_else(|| "filesystem identity transition observer is missing".to_string())?;
            observe_identity(observer, current, &rel, key)?;
        }
        let file_type = metadata.file_type();

        let (kind, target, data) = if file_type.is_symlink() {
            // A pinned symlink inode has an immutable target. Reusing that target
            // avoids readlink's unavoidable atime side effect during post observation.
            let cached = host_key
                .and_then(|key| {
                    observer
                        .as_deref()
                        .and_then(|value| value.symlinks.get(&key))
                })
                .cloned();
            let target = if let Some(target) = cached {
                target
            } else {
                let target = fs::read_link(current)
                    .map_err(|error| format_path_error("read symlink", current, error))?;
                let target = utf8_field(target.as_os_str(), "symlink target")?;
                if let (Some(key), Some(observer)) = (host_key, observer.as_deref_mut()) {
                    observer.symlinks.insert(key, target.clone());
                }
                target
            };
            ("symlink", target, Vec::new())
        } else if file_type.is_dir() {
            let entries = match read_snapshot_directory(current) {
                Ok(entries) => entries,
                Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {
                    record_inaccessible(out, rel, host_key);
                    return Ok(());
                }
                Err(e) => return Err(format_path_error("read directory", current, e).into()),
            };
            let mut children = entries;
            children.sort();
            for child in children {
                walk(
                    base,
                    &child,
                    out,
                    restore_observer_times,
                    observer,
                    capture_handles,
                )?;
            }
            ("dir", String::new(), Vec::new())
        } else if file_type.is_file() {
            let data = match observer.as_deref_mut() {
                Some(observer) if capture_handles => {
                    let key = host_key.ok_or_else(|| {
                        format!(
                            "filesystem file identity is unsupported for `{}`",
                            current.display()
                        )
                    })?;
                    match observer.files.get_mut(&key) {
                        Some(handle) => read_snapshot_handle(handle, current)?,
                        None => {
                            let mut handle = open_snapshot_file(current)?;
                            let data = read_snapshot_handle(&mut handle, current)?;
                            observer.files.insert(key, handle);
                            data
                        }
                    }
                }
                Some(observer) => match host_key.and_then(|key| observer.files.get_mut(&key)) {
                    Some(handle) if snapshot_handle_matches(handle, &metadata) => {
                        read_snapshot_handle(handle, current)?
                    }
                    _ => read_snapshot_handle(&mut open_snapshot_file(current)?, current)?,
                },
                None => read_snapshot_handle(&mut open_snapshot_file(current)?, current)?,
            };
            ("file", String::new(), data)
        } else {
            return Err(format!("unsupported filesystem node `{}`", current.display()).into());
        };
        let original_times = times_from_metadata(&metadata);
        #[cfg(unix)]
        let (uid, gid, logical_size, allocated_512_blocks, preferred_io_block_bytes) = {
            use std::os::unix::fs::MetadataExt;
            (
                Some(metadata.uid()),
                Some(metadata.gid()),
                Some(metadata.size()),
                Some(metadata.blocks()),
                Some(metadata.blksize()),
            )
        };
        #[cfg(not(unix))]
        let (uid, gid, logical_size, allocated_512_blocks, preferred_io_block_bytes) =
            (None, None, None, None, None);
        #[cfg(unix)]
        let link_count = {
            use std::os::unix::fs::MetadataExt;
            Some(metadata.nlink())
        };
        #[cfg(not(unix))]
        let link_count = None;
        #[cfg(unix)]
        if restore_observer_times {
            restore_path_times(current, original_times, file_type.is_symlink())?;
        }
        out.insert(
            rel,
            FsNodeSnapshot {
                raw_stat_metadata: raw_stat_metadata_from_metadata(&metadata),
                kind: kind.to_string(),
                mode_octal: mode_octal_string_from_metadata(&metadata),
                times: original_times,
                uid,
                gid,
                logical_size,
                allocated_512_blocks,
                preferred_io_block_bytes,
                target,
                data,
                host_key,
                link_count,
            },
        );

        Ok(())
    }

    let mut snapshot = BTreeMap::new();
    let mut observer = observer;
    walk(
        root,
        root,
        &mut snapshot,
        restore_observer_times,
        &mut observer,
        capture_handles,
    )?;
    if restore_observer_times {
        // Restoring atime/mtime advances ctime. Re-observe metadata only after the
        // complete traversal so hard-link aliases all capture the same final ctime.
        for (relative_path, node) in &mut snapshot {
            if node.kind == "inaccessible" {
                continue;
            }
            let path = if relative_path == "." {
                root.to_path_buf()
            } else {
                root.join(relative_path)
            };
            let metadata = fs::symlink_metadata(&path)
                .map_err(|error| format_path_error("re-observe restored metadata", &path, error))?;
            node.times = times_from_metadata(&metadata);
        }
    }
    Ok(snapshot)
}

/// Checks whether reading a snapshot or preparing cwd changed the recorded raw metadata.
/// This guard never reads file contents, directory entries or symlink targets.
pub(crate) fn snapshot_metadata_unchanged(
    root: &Path,
    snapshot: &FsSnapshot,
) -> Result<bool, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        for (relative, node) in snapshot {
            // Unobserved nodes cannot establish exact reuse safety.
            if node.kind == "inaccessible" {
                return Ok(false);
            }
            let path = root.join(relative);
            let metadata = match fs::symlink_metadata(&path) {
                Ok(metadata) => metadata,
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::NotFound | io::ErrorKind::PermissionDenied
                    ) =>
                {
                    return Ok(false)
                }
                Err(error) => {
                    return Err(format_path_error("check snapshot metadata", &path, error))
                }
            };
            if node.times != times_from_metadata(&metadata)
                || node.host_key
                    != Some(HostInodeKeySnapshot {
                        device: metadata.dev(),
                        inode: metadata.ino(),
                    })
                || node.mode_octal != mode_octal_string_from_metadata(&metadata)
                || node.uid != Some(metadata.uid())
                || node.gid != Some(metadata.gid())
                || node.link_count != Some(metadata.nlink())
                || node.logical_size != Some(metadata.size())
                || node.allocated_512_blocks != Some(metadata.blocks())
                || node.preferred_io_block_bytes != Some(metadata.blksize())
                || node.raw_stat_metadata != raw_stat_metadata_from_metadata(&metadata)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    #[cfg(not(unix))]
    {
        let _ = (root, snapshot);
        Err("fixture reuse requires Unix metadata".into())
    }
}

pub(crate) fn times_from_metadata(metadata: &fs::Metadata) -> FsTimes {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        FsTimes {
            atime_sec: metadata.atime(),
            atime_nsec: metadata.atime_nsec(),
            mtime_sec: metadata.mtime(),
            mtime_nsec: metadata.mtime_nsec(),
            ctime_sec: metadata.ctime(),
            ctime_nsec: metadata.ctime_nsec(),
        }
    }
    #[cfg(not(unix))]
    {
        FsTimes::default()
    }
}

fn mode_octal_string_from_metadata(metadata: &fs::Metadata) -> String {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        format!("{:04o}", metadata.permissions().mode() & 0o7777)
    }
    #[cfg(not(unix))]
    {
        if metadata.is_dir() {
            "0755".to_string()
        } else {
            "0644".to_string()
        }
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
mod raw_stat_tests {
    use super::raw_stat_metadata_from_metadata;
    use crate::utils::world_json::RawStatMetadataJson;

    // Observing an unchanged file must not advance its ctime through redundant restoration.
    #[test]
    fn unchanged_timestamp_restoration_preserves_file_change_time() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("data");
        std::fs::write(&path, b"payload").unwrap();
        let before = super::times_from_metadata(&std::fs::metadata(&path).unwrap());
        std::thread::sleep(std::time::Duration::from_millis(20));
        super::restore_path_times(&path, before, false).unwrap();
        assert_eq!(
            super::times_from_metadata(&std::fs::metadata(&path).unwrap()),
            before
        );
    }

    // No-op restoration of a link must inspect the link itself rather than its target.
    #[test]
    fn unchanged_timestamp_restoration_preserves_symlink_change_time() {
        let root = tempfile::tempdir().unwrap();
        let target = root.path().join("data");
        let link = root.path().join("link");
        std::fs::write(&target, b"payload").unwrap();
        std::os::unix::fs::symlink("data", &link).unwrap();
        super::restore_path_times(
            &link,
            crate::fuzz::FsTimes {
                atime_sec: 1,
                mtime_sec: 2,
                ..Default::default()
            },
            true,
        )
        .unwrap();
        let before = super::times_from_metadata(&std::fs::symlink_metadata(&link).unwrap());
        let target_before = super::times_from_metadata(&std::fs::metadata(&target).unwrap());
        std::thread::sleep(std::time::Duration::from_millis(20));
        super::restore_path_times(&link, before, true).unwrap();
        assert_eq!(
            super::times_from_metadata(&std::fs::symlink_metadata(&link).unwrap()),
            before
        );
        assert_eq!(
            super::times_from_metadata(&std::fs::metadata(&target).unwrap()),
            target_before
        );
    }

    // A requested timestamp change still reaches the filesystem.
    #[test]
    fn changed_timestamps_are_restored() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("data");
        std::fs::write(&path, b"payload").unwrap();
        let requested = crate::fuzz::FsTimes {
            atime_sec: 1,
            atime_nsec: 123,
            mtime_sec: 2,
            mtime_nsec: 456,
            ..Default::default()
        };
        super::restore_path_times(&path, requested, false).unwrap();
        let actual = super::times_from_metadata(&std::fs::metadata(&path).unwrap());
        assert_eq!((actual.atime_sec, actual.atime_nsec), (1, 123));
        assert_eq!((actual.mtime_sec, actual.mtime_nsec), (2, 456));
    }

    // Terminal observation leaves both ordinary file and symlink raw state unchanged.
    #[test]
    fn observation_preserves_reusable_fixture_metadata() {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(root.path().join("data"), b"payload").unwrap();
        std::os::unix::fs::symlink("data", root.path().join("link")).unwrap();
        let (pre, mut observer) = super::snapshot_fs_pre_with_restore(root.path(), true).unwrap();
        let (post, _) = super::snapshot_fs_post(root.path(), &mut observer).unwrap();
        assert_eq!(pre, post);
        assert!(super::snapshot_metadata_unchanged(root.path(), &post).unwrap());
    }

    // A readlink observer side effect after capture must invalidate a proposed reuse decision.
    #[test]
    fn metadata_guard_detects_symlink_observation_side_effect() {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(root.path().join("data"), b"payload").unwrap();
        let link = root.path().join("link");
        std::os::unix::fs::symlink("data", &link).unwrap();
        super::restore_path_times(
            &link,
            crate::fuzz::FsTimes {
                atime_sec: 1,
                mtime_sec: 1,
                ..Default::default()
            },
            true,
        )
        .unwrap();
        let (pre, mut observer) = super::snapshot_fs_pre_with_restore(root.path(), true).unwrap();
        let (post, _) = super::snapshot_fs_post(root.path(), &mut observer).unwrap();
        assert_eq!(pre, post);
        std::fs::read_link(&link).unwrap();
        assert!(!super::snapshot_metadata_unchanged(root.path(), &post).unwrap());
    }

    // A real character-device stat yields Known rdev and its actual signed block-size field.
    #[test]
    #[allow(deprecated)]
    fn raw_metadata_native_device() {
        use std::os::linux::fs::MetadataExt;
        let metadata = std::fs::metadata("/dev/null").unwrap();
        let raw = metadata.as_raw_stat();
        assert_eq!(
            raw_stat_metadata_from_metadata(&metadata),
            RawStatMetadataJson::Known {
                device_number: raw.st_rdev,
                io_block_bytes: raw.st_blksize
            }
        );
        assert_ne!(raw.st_rdev, 0);
    }

    // Real filesystem capture preserves raw metadata with hardlink identity and arbitrary content bytes.
    #[test]
    fn raw_metadata_native_filesystem_capture() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("a");
        let bytes = b"raw bytes\x00\xff";
        std::fs::write(&path, bytes).unwrap();
        std::fs::hard_link(&path, directory.path().join("b")).unwrap();
        let expected = raw_stat_metadata_from_metadata(&std::fs::metadata(path).unwrap());
        assert!(matches!(expected, RawStatMetadataJson::Known { .. }));
        let snapshot = super::snapshot_fs(directory.path()).unwrap();
        assert_eq!(snapshot["a"].raw_stat_metadata, expected);
        assert_eq!(snapshot["b"].raw_stat_metadata, expected);
        assert_eq!(snapshot["a"].host_key, snapshot["b"].host_key);
        assert_eq!(snapshot["a"].data, bytes);
        let encoded = serde_json::to_value(&snapshot).unwrap();
        assert_eq!(
            encoded["a"]["raw_stat_metadata"],
            serde_json::to_value(expected).unwrap()
        );
    }

    // A controlled libc interposer can expose raw signed endpoints through the actual capture projection.
    #[test]
    fn raw_metadata_native_injection_probe() {
        let fixture = tempfile::NamedTempFile::new().unwrap();
        let path = std::env::var_os("RAW_STAT_PROBE_PATH")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| fixture.path().to_path_buf());
        let metadata = std::fs::metadata(path).unwrap();
        let value = raw_stat_metadata_from_metadata(&metadata);
        println!("RAW_STAT_JSON={}", serde_json::to_string(&value).unwrap());
        let (default_device, default_block) = match value {
            RawStatMetadataJson::Known {
                device_number,
                io_block_bytes,
            } => (device_number, io_block_bytes),
            RawStatMetadataJson::Unknown => panic!("Linux raw-stat capture returned Unknown"),
        };
        let device: u64 = std::env::var("RAW_STAT_DEVICE")
            .map(|text| text.parse().unwrap())
            .unwrap_or(default_device);
        let block: i64 = std::env::var("RAW_STAT_BLOCK")
            .map(|text| text.parse().unwrap())
            .unwrap_or(default_block);
        assert_eq!(
            value,
            RawStatMetadataJson::Known {
                device_number: device,
                io_block_bytes: block
            }
        );
    }
}

#[cfg(test)]
mod snapshot_tests {
    use super::{
        snapshot_fs, snapshot_fs_checked, snapshot_fs_post, snapshot_fs_pre,
        snapshot_fs_pre_unrestored, FsCaptureError,
    };
    use crate::fuzz::HostInodeKeySnapshot;
    use std::fs;
    use std::io;

    // An observed directory-read denial is retained as a modeled inaccessible filesystem node.
    #[cfg(unix)]
    #[test]
    fn snapshot_records_unreadable_directory_as_inaccessible() {
        use std::fs;
        use std::os::unix::fs::MetadataExt;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let blocked = root.path().join("blocked");
        fs::create_dir(&blocked).unwrap();
        let metadata = fs::symlink_metadata(&blocked).unwrap();
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o0)).unwrap();

        match fs::read_dir(&blocked) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }

        let snapshot = snapshot_fs(root.path());
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();

        let snapshot = snapshot.unwrap();
        let node = snapshot.get("blocked").unwrap();
        assert_eq!(node.kind, "inaccessible");
        assert_eq!(
            node.host_key,
            Some(HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino()
            })
        );
    }

    // A non-UTF-8 relative path must stop capture instead of entering a replacement path.
    #[cfg(unix)]
    #[test]
    fn snapshot_rejects_non_utf8_relative_path() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join(OsString::from_vec(vec![b'f', 0xff])),
            b"data",
        )
        .unwrap();

        assert_eq!(
            snapshot_fs_checked(root.path()).unwrap_err(),
            FsCaptureError::Encoding {
                field: "relative path"
            }
        );
    }

    // A non-UTF-8 symlink target must stop capture instead of recording replacement text.
    #[cfg(unix)]
    #[test]
    fn snapshot_rejects_non_utf8_symlink_target() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().unwrap();
        symlink(
            OsString::from_vec(vec![b't', 0xff]),
            root.path().join("link"),
        )
        .unwrap();

        assert_eq!(
            snapshot_fs_checked(root.path()).unwrap_err(),
            FsCaptureError::Encoding {
                field: "symlink target"
            }
        );
    }

    // A pre-opened handle must preserve exact bytes when chmod makes the same file unreadable.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_reads_mode_zero_file_through_preopened_handle() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"payload").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        let (_, mut observer) = snapshot_fs_pre_unrestored(root.path()).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let (snapshot, _) = snapshot_fs_post(root.path(), &mut observer).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert_eq!(snapshot["file"].kind, "file");
        assert_eq!(snapshot["file"].mode_octal, "0000");
        assert_eq!(snapshot["file"].data, b"payload");
    }

    // A live handle must observe same-inode truncation and rewrite rather than cached pre-state bytes.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_handle_observes_same_inode_content_mutation() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"before").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        let (_, mut observer) = snapshot_fs_pre_unrestored(root.path()).unwrap();
        fs::write(&path, b"after").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let (snapshot, _) = snapshot_fs_post(root.path(), &mut observer).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert_eq!(snapshot["file"].data, b"after");
    }

    // An open handle must not resurrect a path deleted before post-state traversal.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_does_not_resurrect_deleted_file() {
        use std::fs;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"payload").unwrap();
        let (_, mut observer) = snapshot_fs_pre_unrestored(root.path()).unwrap();
        fs::remove_file(&path).unwrap();

        let (snapshot, _) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(!snapshot.contains_key("file"));
    }

    // A regular-file rename preserves the exact pre-path to post-path object relation.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_regular_file_rename() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("before"), b"x").unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("before"), root.path().join("after")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("before".to_string(), "after".to_string())));
    }

    // Deleting and recreating equal bytes at one path does not preserve object identity.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_rejects_delete_and_recreate() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("file"), b"same").unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::remove_file(root.path().join("file")).unwrap();
        fs::write(root.path().join("file"), b"same").unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(!evidence.contains(&("file".to_string(), "file".to_string())));
    }

    // Every pre hardlink name relates to every surviving post name for its shared object.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_hardlink_aliases() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("a"), b"x").unwrap();
        fs::hard_link(root.path().join("a"), root.path().join("b")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("a"), root.path().join("c")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        for before in ["a", "b"] {
            for after in ["b", "c"] {
                assert!(evidence.contains(&(before.to_string(), after.to_string())));
            }
        }
    }

    // A no-follow handle tracks the symlink object rather than its target.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_symlink_without_following() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("target"), b"x").unwrap();
        symlink("target", root.path().join("link")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("link"), root.path().join("renamed")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("link".to_string(), "renamed".to_string())));
        assert!(!evidence.contains(&("link".to_string(), "target".to_string())));
    }

    // An O_PATH handle tracks an empty directory across a rename.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_empty_directory_rename() {
        let root = tempfile::tempdir().unwrap();
        fs::create_dir(root.path().join("before")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("before"), root.path().join("after")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("before".to_string(), "after".to_string())));
    }

    // A replacement inode must fail closed when its current path cannot be read.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_rejects_unreadable_replacement_inode() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"old").unwrap();
        let (_, mut observer) = snapshot_fs_pre_unrestored(root.path()).unwrap();
        fs::remove_file(&path).unwrap();
        fs::write(&path, b"new").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let error = snapshot_fs_post(root.path(), &mut observer).unwrap_err();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert!(error.contains("failed to read file"));
        assert!(error.contains("Permission denied"));
    }

    // A new unreadable file without a pre-opened handle must fail closed.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_rejects_unreadable_new_file() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let (_, mut observer) = snapshot_fs_pre_unrestored(root.path()).unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"new").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let error = snapshot_fs_post(root.path(), &mut observer).unwrap_err();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert!(error.contains("failed to read file"));
        assert!(error.contains("Permission denied"));
    }
}
