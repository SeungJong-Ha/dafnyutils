use super::comparison::fs_snapshot::{restore_path_times, times_from_metadata};
use super::execution::control_chmod_fixture_node;
use super::{DirSpec, FixtureBlueprint, FsTimes, HostInodeKeySnapshot};
use crate::utils::paths::format_path_error;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

pub(crate) fn reset_dir(path: &Path) -> Result<(), String> {
    if path.exists() {
        remove_dir_forcefully(path)?;
    }
    fs::create_dir_all(path).map_err(|e| format_path_error("create directory", path, e))?;
    Ok(())
}

#[cfg(test)]
pub(crate) fn prepare_iteration_dirs(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
    control_chmod_times: bool,
) -> Result<(PathBuf, PathBuf), String> {
    let (ref_dir, dut_dir) = stage_iteration_dirs(
        work_root,
        shared_root,
        iteration,
        fixture,
        control_chmod_times,
    )?;
    apply_fixture_modes(&ref_dir, fixture)?;
    apply_fixture_modes(&dut_dir, fixture)?;
    Ok((ref_dir, dut_dir))
}

/// Restores only validated saved atime/mtime inputs onto a fresh fixture clone.
pub(crate) fn restore_fixture_time_inputs(
    root: &Path,
    saved: &BTreeMap<String, FsTimes>,
) -> Result<(), String> {
    restore_selected_time_inputs(root, saved, true)
}

/// Restores known reference prestate inputs after the cloned DUT has entered cwd.
pub(crate) fn restore_observed_fixture_times(
    root: &Path,
    snapshot: &super::FsSnapshot,
) -> Result<(), String> {
    let saved = snapshot
        .iter()
        .filter(|(_, node)| node.kind != "inaccessible")
        .map(|(path, node)| (path.clone(), node.times))
        .collect();
    restore_selected_time_inputs(root, &saved, false)
}

fn restore_selected_time_inputs(
    root: &Path,
    saved: &BTreeMap<String, FsTimes>,
    require_complete: bool,
) -> Result<(), String> {
    #[cfg(unix)]
    {
        let nodes = if require_complete {
            collect_fixture_nodes(root)?
        } else {
            use std::os::unix::fs::MetadataExt;
            saved
                .keys()
                .map(|name| {
                    let relative = Path::new(name);
                    if name != "." && !is_safe_fixture_path(relative) {
                        return Err(format!("invalid saved fixture time path: {name}"));
                    }
                    let path = root.join(relative);
                    let metadata = fs::symlink_metadata(&path).map_err(|error| {
                        format_path_error("read fixture time input metadata", &path, error)
                    })?;
                    Ok((
                        relative.to_path_buf(),
                        times_from_metadata(&metadata),
                        metadata.file_type().is_symlink(),
                        HostInodeKeySnapshot {
                            device: metadata.dev(),
                            inode: metadata.ino(),
                        },
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?
        };
        let mut aliases = BTreeMap::new();
        let mut restored = Vec::new();
        for (relative, _, is_symlink, key) in nodes {
            let name = if relative.as_os_str().is_empty() {
                "."
            } else {
                relative
                    .to_str()
                    .ok_or("replay fixture path is not UTF-8")?
            };
            let times = *saved
                .get(name)
                .ok_or_else(|| format!("saved fixture time input missing at {name}"))?;
            if !(0..1_000_000_000).contains(&times.atime_nsec)
                || !(0..1_000_000_000).contains(&times.mtime_nsec)
            {
                return Err(format!("invalid saved fixture timestamp at {name}"));
            }
            let values = (
                times.atime_sec,
                times.atime_nsec,
                times.mtime_sec,
                times.mtime_nsec,
            );
            if aliases
                .insert(key, values)
                .is_some_and(|previous| previous != values)
            {
                return Err(format!(
                    "saved fixture timestamps disagree across aliases at {name}"
                ));
            }
            restored.push((relative, times, is_symlink));
        }
        if restored.len() != saved.len() {
            return Err("saved fixture time path population differs".into());
        }
        // All keys were matched to actual fixture paths before any timestamp writes.
        for (relative, times, is_symlink) in restored.into_iter().rev() {
            restore_path_times(&root.join(relative), times, is_symlink)?;
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = (root, saved, require_complete);
        Err("replay time input restoration requires Unix".into())
    }
}

pub(crate) fn stage_iteration_dirs(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
    control_chmod_times: bool,
) -> Result<(PathBuf, PathBuf), String> {
    let root_path = prepare_iteration_root(work_root, shared_root, iteration)?;
    let base_dir = root_path.join("base");
    let ref_dir = root_path.join("ref");
    let dut_dir = root_path.join("dut");

    reset_dir(&base_dir)?;
    materialize_fixture(&base_dir, fixture)?;

    #[cfg(unix)]
    {
        make_tree_owner_writable(&base_dir).map_err(|e| {
            format!(
                "failed to ensure base fixture readability `{}`: {e}",
                base_dir.display()
            )
        })?;
    }

    clone_fixture_tree(&base_dir, &ref_dir)?;
    clone_fixture_tree(&base_dir, &dut_dir)?;
    #[cfg(unix)]
    synchronize_clone_times(&ref_dir, &dut_dir)?;
    if control_chmod_times {
        control_chmod_fixture_tree(&ref_dir)?;
        control_chmod_fixture_tree(&dut_dir)?;
    }
    Ok((ref_dir, dut_dir))
}

#[cfg(unix)]
fn collect_fixture_nodes(
    root: &Path,
) -> Result<Vec<(PathBuf, FsTimes, bool, HostInodeKeySnapshot)>, String> {
    fn visit(
        root: &Path,
        current: &Path,
        nodes: &mut Vec<(PathBuf, FsTimes, bool, HostInodeKeySnapshot)>,
    ) -> Result<(), String> {
        use std::os::unix::fs::MetadataExt;

        let metadata = fs::symlink_metadata(current)
            .map_err(|error| format_path_error("read cloned fixture metadata", current, error))?;
        let file_type = metadata.file_type();
        let times = times_from_metadata(&metadata);
        let relative_path = current
            .strip_prefix(root)
            .map_err(|error| {
                format!(
                    "failed to make cloned fixture path `{}` relative to `{}`: {error}",
                    current.display(),
                    root.display()
                )
            })?
            .to_path_buf();
        nodes.push((
            relative_path,
            times,
            file_type.is_symlink(),
            HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            },
        ));

        if file_type.is_dir() {
            let mut children = fs::read_dir(current)
                .map_err(|error| {
                    format_path_error("read cloned fixture directory", current, error)
                })?
                .map(|entry| {
                    entry.map(|entry| entry.path()).map_err(|error| {
                        format_path_error("read cloned fixture directory entry", current, error)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.sort();
            for child in children {
                visit(root, &child, nodes)?;
            }
        }
        Ok(())
    }

    let mut nodes = Vec::new();
    visit(root, root, &mut nodes)?;
    Ok(nodes)
}

#[cfg(unix)]
fn synchronize_clone_times(reference: &Path, dut: &Path) -> Result<(), String> {
    let captured = collect_fixture_nodes(reference)?;
    for (relative_path, times, is_symlink, _) in captured.iter().rev() {
        restore_path_times(&reference.join(relative_path), *times, *is_symlink)?;
        restore_path_times(&dut.join(relative_path), *times, *is_symlink)?;
    }
    Ok(())
}

fn control_chmod_fixture_tree(root: &Path) -> Result<(), String> {
    control_fixture_tree(root, control_chmod_fixture_node)
}

fn control_fixture_tree(
    root: &Path,
    control_node: fn(&Path, bool) -> Result<(), String>,
) -> Result<(), String> {
    fn visit(
        path: &Path,
        control_node: fn(&Path, bool) -> Result<(), String>,
    ) -> Result<(), String> {
        let metadata = fs::symlink_metadata(path)
            .map_err(|error| format_path_error("read fixture metadata", path, error))?;
        let file_type = metadata.file_type();
        control_node(path, file_type.is_symlink())?;
        if file_type.is_dir() {
            let mut children = fs::read_dir(path)
                .map_err(|error| format_path_error("read fixture directory", path, error))?
                .map(|entry| {
                    entry.map(|entry| entry.path()).map_err(|error| {
                        format_path_error("read fixture directory entry", path, error)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.sort();
            for child in children {
                visit(&child, control_node)?;
            }
        }
        Ok(())
    }

    visit(root, control_node)
}

pub(crate) fn materialize_fixture(root: &Path, fixture: &FixtureBlueprint) -> Result<(), String> {
    validate_fixture(fixture)?;
    for dir in &fixture.directories {
        let path = root.join(&dir.relative_path);
        fs::create_dir_all(&path).map_err(|e| format_path_error("create fixture dir", &path, e))?;
    }
    for file in &fixture.files {
        let path = root.join(&file.relative_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "failed to create fixture dir `{}` for `{}`: {e}",
                    parent.display(),
                    path.display()
                )
            })?;
        }
        fs::write(&path, &file.bytes)
            .map_err(|e| format_path_error("write fixture file", &path, e))?;
    }

    for symlink_spec in &fixture.symlinks {
        let path = root.join(&symlink_spec.relative_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "failed to create fixture dir `{}` for symlink `{}`: {e}",
                    parent.display(),
                    path.display()
                )
            })?;
        }
        create_fixture_symlink(&symlink_spec.target, &path)?;
    }

    for hardlink in &fixture.hardlinks {
        let source = root.join(&hardlink.source_relative_path);
        let destination = root.join(&hardlink.relative_path);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format_path_error("create hardlink parent", parent, e))?;
        }
        fs::hard_link(&source, &destination)
            .map_err(|e| format_path_error("create fixture hardlink", &destination, e))?;
    }

    apply_fixture_modes(root, fixture)?;

    Ok(())
}

pub(crate) fn validate_fixture(fixture: &FixtureBlueprint) -> Result<(), String> {
    let mut destinations = BTreeSet::new();
    for (kind, path) in fixture
        .directories
        .iter()
        .map(|entry| ("directory", entry.relative_path.as_path()))
        .chain(
            fixture
                .files
                .iter()
                .map(|entry| ("file", entry.relative_path.as_path())),
        )
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| ("symlink", entry.relative_path.as_path())),
        )
        .chain(
            fixture
                .hardlinks
                .iter()
                .map(|entry| ("hardlink", entry.relative_path.as_path())),
        )
    {
        if !is_safe_fixture_path(path) {
            return Err(format!("invalid fixture {kind} path `{}`", path.display()));
        }
        if !destinations.insert(path) {
            return Err(format!("duplicate fixture path `{}`", path.display()));
        }
    }

    for symlink in &fixture.symlinks {
        if !symlink_target_stays_within_fixture(&symlink.relative_path, &symlink.target) {
            return Err(format!(
                "fixture symlink target escapes fixture root: `{}` -> `{}`",
                symlink.relative_path.display(),
                symlink.target.display()
            ));
        }
    }
    let sources: BTreeSet<&Path> = fixture
        .files
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .collect();
    let declared_symlink_paths: BTreeSet<&Path> = fixture
        .symlinks
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .collect();
    let non_directory_paths: BTreeSet<&Path> = fixture
        .files
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .chain(
            fixture
                .hardlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .collect();
    let symlink_paths: BTreeSet<&Path> = declared_symlink_paths
        .iter()
        .copied()
        .chain(
            fixture
                .hardlinks
                .iter()
                .filter(|hardlink| {
                    declared_symlink_paths.contains(hardlink.source_relative_path.as_path())
                })
                .map(|hardlink| hardlink.relative_path.as_path()),
        )
        .collect();

    for hardlink in &fixture.hardlinks {
        if !is_safe_fixture_path(&hardlink.source_relative_path) {
            return Err(format!(
                "invalid fixture hardlink source `{}`",
                hardlink.source_relative_path.display()
            ));
        }
        if let Some(symlink) = fixture
            .symlinks
            .iter()
            .find(|symlink| symlink.relative_path == hardlink.source_relative_path)
        {
            if !symlink_target_stays_within_fixture(&hardlink.relative_path, &symlink.target) {
                return Err(format!(
                    "fixture hardlink alias of symlink escapes fixture root: `{}` -> `{}`",
                    hardlink.relative_path.display(),
                    symlink.target.display()
                ));
            }
        }
        for path in [&hardlink.relative_path, &hardlink.source_relative_path] {
            if path
                .ancestors()
                .skip(1)
                .any(|ancestor| symlink_paths.contains(ancestor))
            {
                return Err(format!(
                    "fixture hardlink path crosses symlink `{}`",
                    path.display()
                ));
            }
        }
        if !sources.contains(hardlink.source_relative_path.as_path()) {
            return Err(format!(
                "missing or unsupported fixture hardlink source `{}`",
                hardlink.source_relative_path.display()
            ));
        }
    }

    for path in destinations {
        if path
            .ancestors()
            .skip(1)
            .any(|ancestor| declared_symlink_paths.contains(ancestor))
        {
            return Err(format!("fixture path crosses symlink `{}`", path.display()));
        }
        if path
            .ancestors()
            .skip(1)
            .any(|ancestor| non_directory_paths.contains(ancestor))
        {
            return Err(format!(
                "fixture path crosses non-directory entry `{}`",
                path.display()
            ));
        }
    }
    Ok(())
}

pub(crate) fn symlink_target_stays_within_fixture(link: &Path, target: &Path) -> bool {
    if target.as_os_str().is_empty() || target.is_absolute() {
        return false;
    }
    let mut depth = link
        .parent()
        .map_or(0, |parent| parent.components().count());
    for component in target.components() {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => return false,
        }
    }
    true
}

fn is_safe_fixture_path(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && !path.is_absolute()
        && !path.components().any(|component| {
            matches!(
                component,
                Component::CurDir
                    | Component::ParentDir
                    | Component::RootDir
                    | Component::Prefix(_)
            )
        })
}

fn prepare_iteration_root(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
) -> Result<PathBuf, String> {
    let root = if let Some(shared) = shared_root {
        shared.join(format!("iter-{iteration:06}"))
    } else {
        work_root.join(format!("iter-{iteration:06}"))
    };
    reset_dir(&root)?;
    Ok(root)
}

pub(crate) fn clone_fixture_tree(source: &Path, destination: &Path) -> Result<(), String> {
    reset_dir(destination)?;
    let status = Command::new("cp")
        .arg("-a")
        .arg(source.join("."))
        .arg(destination)
        .status()
        .map_err(|e| {
            format!(
                "failed to launch fixture clone command from `{}` to `{}`: {e}",
                source.display(),
                destination.display()
            )
        })?;
    if !status.success() {
        return Err(format!(
            "fixture clone command failed from `{}` to `{}` with status {:?}",
            source.display(),
            destination.display(),
            status.code()
        ));
    }
    Ok(())
}

pub(crate) fn apply_fixture_modes(root: &Path, fixture: &FixtureBlueprint) -> Result<(), String> {
    for file in &fixture.files {
        let path = root.join(&file.relative_path);
        apply_entry_mode(&path, file.mode, "file")?;
    }

    let mut dirs_by_depth: Vec<&DirSpec> = fixture.directories.iter().collect();
    dirs_by_depth.sort_by(|left, right| {
        right
            .relative_path
            .components()
            .count()
            .cmp(&left.relative_path.components().count())
    });
    for dir in dirs_by_depth {
        let path = root.join(&dir.relative_path);
        apply_entry_mode(&path, dir.mode, "directory")?;
    }

    Ok(())
}

pub(crate) fn set_fixture_owner(root: &Path, uid: u32, gid: u32) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::ffi::CString;
        use std::os::unix::ffi::OsStrExt;

        unsafe extern "C" {
            fn lchown(path: *const std::os::raw::c_char, owner: u32, group: u32) -> i32;
        }

        fn visit(path: &Path, uid: u32, gid: u32) -> Result<(), String> {
            let metadata = fs::symlink_metadata(path)
                .map_err(|error| format_path_error("read fixture ownership", path, error))?;
            if metadata.is_dir() {
                let mut children = fs::read_dir(path)
                    .map_err(|error| {
                        format_path_error("read fixture ownership directory", path, error)
                    })?
                    .map(|entry| {
                        entry.map(|entry| entry.path()).map_err(|error| {
                            format_path_error("read fixture ownership entry", path, error)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                children.sort();
                for child in children {
                    visit(&child, uid, gid)?;
                }
            }
            let display = path.display().to_string();
            let raw = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
                format!("fixture ownership path contains an unsupported NUL byte: `{display}`")
            })?;
            if unsafe { lchown(raw.as_ptr(), uid, gid) } != 0 {
                return Err(format!(
                    "failed to set fixture ownership `{display}` to {uid}:{gid}: {}",
                    io::Error::last_os_error()
                ));
            }
            Ok(())
        }

        visit(root, uid, gid)
    }
    #[cfg(not(unix))]
    {
        let _ = (root, uid, gid);
        Err("numeric fixture ownership requires Unix".to_string())
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::{apply_fixture_modes, materialize_fixture, stage_iteration_dirs, validate_fixture};
    use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, HardlinkSpec, SymlinkSpec};
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use std::path::PathBuf;

    // Conflicting saved alias times are rejected before restoring any fixture metadata.
    #[test]
    fn replay_time_inputs_reject_conflicting_hardlink_aliases() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("a"), b"data").unwrap();
        fs::hard_link(root.path().join("a"), root.path().join("b")).unwrap();
        let mut saved: std::collections::BTreeMap<_, _> =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs(root.path())
                .unwrap()
                .into_iter()
                .map(|(path, node)| (path, node.times))
                .collect();
        saved.get_mut("b").unwrap().mtime_sec += 1;
        let error = super::restore_fixture_time_inputs(root.path(), &saved).unwrap_err();
        assert!(error.contains("disagree across aliases"), "{error}");
    }

    // A malformed saved subsecond timestamp cannot be used as a replay fixture input.
    #[test]
    fn replay_time_inputs_reject_invalid_nanoseconds() {
        let root = tempfile::tempdir().unwrap();
        let mut saved: std::collections::BTreeMap<_, _> =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs(root.path())
                .unwrap()
                .into_iter()
                .map(|(path, node)| (path, node.times))
                .collect();
        saved.get_mut(".").unwrap().atime_nsec = 1_000_000_000;
        assert!(super::restore_fixture_time_inputs(root.path(), &saved)
            .unwrap_err()
            .contains("invalid saved fixture timestamp"));
    }

    // Replay fixture validation rejects traversal before an external sentinel can be overwritten.
    #[test]
    fn materialize_fixture_rejects_escape_before_writing() {
        let sandbox = tempfile::tempdir().unwrap();
        let fixture_root = sandbox.path().join("fixture");
        fs::create_dir(&fixture_root).unwrap();
        let sentinel = sandbox.path().join("outside");
        fs::write(&sentinel, b"unchanged").unwrap();
        let fixture = FixtureBlueprint {
            directories: Vec::new(),
            files: vec![FileSpec {
                relative_path: PathBuf::from("../outside"),
                bytes: b"overwritten".to_vec(),
                mode: 0o644,
            }],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        };

        let error = materialize_fixture(&fixture_root, &fixture).unwrap_err();

        assert!(error.contains("invalid fixture file path"));
        assert_eq!(fs::read(&sentinel).unwrap(), b"unchanged");
    }

    // A replay symlink target cannot lexically escape the isolated fixture root.
    #[test]
    fn fixture_validation_rejects_escaping_symlink_target() {
        let fixture = FixtureBlueprint {
            directories: Vec::new(),
            files: Vec::new(),
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("escape"),
                target: PathBuf::from("../outside"),
            }],
            hardlinks: Vec::new(),
        };

        let error = validate_fixture(&fixture).unwrap_err();

        assert!(error.contains("symlink target escapes fixture root"));
    }

    // Parent traversal within a nested fixture remains a valid relative symlink target.
    #[test]
    fn fixture_validation_allows_internal_parent_symlink_target() {
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("dir"),
                mode: 0o755,
            }],
            files: vec![FileSpec {
                relative_path: PathBuf::from("inside"),
                bytes: Vec::new(),
                mode: 0o644,
            }],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("dir/link"),
                target: PathBuf::from("../inside"),
            }],
            hardlinks: Vec::new(),
        };

        validate_fixture(&fixture).unwrap();
    }

    // A relative symlink hardlink alias must not resolve outside the fixture from its own path.
    #[test]
    fn fixture_validation_rejects_escaping_relative_symlink_alias() {
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("v7bn4r02"),
                mode: 0o755,
            }],
            files: Vec::new(),
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("v7bn4r02/.yb3zcp-sym"),
                target: PathBuf::from("../qlouf/eqt3ih9-o/.8v2cy-0vp.cfg"),
            }],
            hardlinks: vec![HardlinkSpec {
                relative_path: PathBuf::from("__yd2q.bin"),
                source_relative_path: PathBuf::from("v7bn4r02/.yb3zcp-sym"),
            }],
        };

        let error = validate_fixture(&fixture).unwrap_err();

        assert!(error.contains("hardlink alias of symlink escapes fixture root"));
    }

    // A valid relative symlink alias resolves from its own parent while staying in the fixture.
    #[test]
    fn materialize_fixture_preserves_internal_relative_symlink_alias() {
        let root = tempfile::tempdir().unwrap();
        let fixture = FixtureBlueprint {
            directories: vec![
                DirSpec {
                    relative_path: PathBuf::from("nested"),
                    mode: 0o755,
                },
                DirSpec {
                    relative_path: PathBuf::from("deep/nested"),
                    mode: 0o755,
                },
            ],
            files: vec![
                FileSpec {
                    relative_path: PathBuf::from("target"),
                    bytes: b"source target".to_vec(),
                    mode: 0o644,
                },
                FileSpec {
                    relative_path: PathBuf::from("deep/target"),
                    bytes: b"alias target".to_vec(),
                    mode: 0o644,
                },
            ],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("nested/link"),
                target: PathBuf::from("../target"),
            }],
            hardlinks: vec![HardlinkSpec {
                relative_path: PathBuf::from("deep/nested/alias"),
                source_relative_path: PathBuf::from("nested/link"),
            }],
        };

        materialize_fixture(root.path(), &fixture).unwrap();

        assert_eq!(
            fs::read_link(root.path().join("deep/nested/alias")).unwrap(),
            PathBuf::from("../target")
        );
        assert_eq!(
            fs::canonicalize(root.path().join("deep/nested/alias")).unwrap(),
            fs::canonicalize(root.path().join("deep/target")).unwrap()
        );
        assert_eq!(
            fs::read(root.path().join("deep/nested/alias")).unwrap(),
            b"alias target"
        );
    }

    // Searchable staging must defer the fixture's exact directory mode until explicit finalization.
    #[test]
    fn staged_iteration_dirs_are_searchable_until_exact_mode_finalization() {
        let root = tempfile::tempdir().unwrap();
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("d"),
                mode: 0o000,
            }],
            files: Vec::new(),
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        };
        let (reference, dut) = stage_iteration_dirs(root.path(), None, 0, &fixture, false).unwrap();

        for role_root in [&reference, &dut] {
            assert_eq!(
                fs::symlink_metadata(role_root.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o700,
                0o700
            );
            apply_fixture_modes(role_root, &fixture).unwrap();
            assert_eq!(
                fs::symlink_metadata(role_root.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
    }
}

fn apply_entry_mode(path: &Path, mode: u32, kind: &str) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        fs::set_permissions(path, fs::Permissions::from_mode(mode)).map_err(|e| {
            format!(
                "failed to set fixture {kind} mode {:04o} on `{}`: {e}",
                mode,
                path.display()
            )
        })?;
    }
    #[cfg(not(unix))]
    {
        let _ = (path, mode, kind);
    }
    Ok(())
}

fn create_fixture_symlink(target: &Path, path: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        symlink(target, path).map_err(|e| {
            format!(
                "failed to create fixture symlink `{}` -> `{}`: {e}",
                path.display(),
                target.display()
            )
        })?;
    }
    #[cfg(not(unix))]
    {
        let _ = (target, path);
    }
    Ok(())
}

fn remove_dir_forcefully(path: &Path) -> Result<(), String> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(first_err) => {
            #[cfg(unix)]
            {
                if first_err.kind() == io::ErrorKind::PermissionDenied {
                    make_tree_owner_writable(path).map_err(|e| {
                        format!(
                            "failed to make directory writable `{}` after permission error: {e}",
                            path.display()
                        )
                    })?;
                    fs::remove_dir_all(path).map_err(|e| {
                        format!(
                            "failed to clear directory `{}` after permission recovery: {e}",
                            path.display()
                        )
                    })?;
                    return Ok(());
                }
            }
            Err(format!(
                "failed to clear directory `{}`: {first_err}",
                path.display()
            ))
        }
    }
}

#[cfg(unix)]
fn make_tree_owner_writable(path: &Path) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    if !path.exists() {
        return Ok(());
    }

    fn visit(path: &Path) -> io::Result<()> {
        let meta = fs::symlink_metadata(path)?;
        if meta.file_type().is_symlink() {
            return Ok(());
        }

        if meta.is_dir() {
            let mut perms = meta.permissions();
            perms.set_mode(0o700);
            fs::set_permissions(path, perms)?;
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                visit(&entry.path())?;
            }
        } else {
            let mut perms = meta.permissions();
            perms.set_mode(0o600);
            fs::set_permissions(path, perms)?;
        }
        Ok(())
    }

    visit(path)
}
