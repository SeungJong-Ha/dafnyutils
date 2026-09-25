"""Controlled filesystem scenarios for host-side candidate workspace collection."""

from __future__ import annotations

import os
import shutil
import tarfile
from pathlib import Path

import pytest

import evaluation.submission.archive as archive_module
from evaluation.submission.archive import package_workspace, receive_submission
from evaluation.task.release import prepare_release, publish_release


@pytest.fixture(scope="module")
def released_workspace(tmp_path_factory: pytest.TempPathFactory):
    root = tmp_path_factory.mktemp("packaging-release")
    manifest = publish_release(("true",), root / "release")
    prepared = prepare_release(root / "release", root / "workspace")
    return manifest, prepared.workspace


def _copy_workspace(released_workspace, tmp_path: Path):
    manifest, original = released_workspace
    workspace = tmp_path / "workspace"
    shutil.copytree(original, workspace)
    return manifest, workspace


# Packaging keeps task-relative names, includes candidate files, and obeys manifest exclusions.
def test_package_workspace_with_exclusions(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    root = workspace / manifest.task_roots[0]
    (root / "helper.dfy").write_text("method Helper() {}\n", encoding="utf-8")
    (root / "bin").mkdir()
    (root / "bin/program").write_bytes(b"compiled")
    output = tmp_path / "result.tar.gz"

    assert package_workspace(workspace, manifest, output) == output
    with tarfile.open(output, "r:gz") as archive:
        names = archive.getnames()
        assert f"{manifest.task_roots[0]}/helper.dfy" in names
        assert not any("/bin" in name for name in names)
        source = archive.extractfile(f"{manifest.task_roots[0]}/helper.dfy")
        assert source is not None and source.read() == b"method Helper() {}\n"


# Links, hard links, and FIFOs are rejected rather than followed or silently skipped.
@pytest.mark.parametrize("kind", ["symlink", "directory-symlink", "hardlink", "fifo"])
def test_package_rejects_unsafe_entry(released_workspace, tmp_path: Path, kind: str) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    root = workspace / manifest.task_roots[0]
    entry = root / "unsafe"
    source = next(path for path in root.iterdir() if path.is_file())
    if kind == "symlink":
        entry.symlink_to(source)
    elif kind == "directory-symlink":
        entry.symlink_to(tmp_path, target_is_directory=True)
    elif kind == "hardlink":
        entry.hardlink_to(source)
    else:
        os.mkfifo(entry)
    output = tmp_path / "result.tar.gz"

    with pytest.raises(ValueError):
        package_workspace(workspace, manifest, output)
    assert not output.exists()
    assert not tuple(tmp_path.glob(".result.tar.gz.*.tmp"))


# A missing requested root fails the archive instead of yielding a partial result.
def test_package_rejects_missing_root(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    (workspace / manifest.task_roots[0]).rename(workspace / "missing-task-root")
    with pytest.raises(FileNotFoundError):
        package_workspace(workspace, manifest, tmp_path / "result.tar.gz")


# A symlink in a root ancestor cannot redirect collection outside the workspace.
def test_package_rejects_symlink_root_ancestor(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    (workspace / "bench/utils").rename(workspace / "bench/original")
    (workspace / "bench/utils").symlink_to(tmp_path, target_is_directory=True)
    with pytest.raises(ValueError, match="real directories"):
        package_workspace(workspace, manifest, tmp_path / "result.tar.gz")


# A linked workspace cannot redirect the packaging boundary.
def test_package_rejects_linked_workspace(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    alias = tmp_path / "alias"
    alias.symlink_to(workspace, target_is_directory=True)
    with pytest.raises(ValueError, match="real directory"):
        package_workspace(alias, manifest, tmp_path / "result.tar.gz")


# A root swapped after its descriptor is pinned cannot leak outside bytes.
def test_package_root_swap_stays_pinned(
    released_workspace, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    root = workspace / manifest.task_roots[0]
    (root / "candidate.txt").write_bytes(b"candidate")
    private = tmp_path / "private"
    private.mkdir()
    (private / "candidate.txt").write_bytes(b"private")
    original = archive_module._package_file
    swapped = False

    def swap(*args, **kwargs):
        nonlocal swapped
        if not swapped:
            root.rename(root.with_name("original"))
            root.symlink_to(private, target_is_directory=True)
            swapped = True
        return original(*args, **kwargs)

    monkeypatch.setattr(archive_module, "_package_file", swap)
    output = tmp_path / "result.tar.gz"
    package_workspace(workspace, manifest, output)
    assert swapped
    with tarfile.open(output, "r:gz") as archive:
        source = archive.extractfile(f"{manifest.task_roots[0]}/candidate.txt")
        assert source is not None and source.read() == b"candidate"


# The result archive must remain outside the workspace it captures.
def test_package_rejects_archive_inside_workspace(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    with pytest.raises(ValueError, match="outside the workspace"):
        package_workspace(workspace, manifest, workspace / "result.tar.gz")


# An unreadable file fails atomically and leaves no partial archive.
def test_package_unreadable_entry_cleans_temporary(
    released_workspace, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    root = workspace / manifest.task_roots[0]
    (root / "unreadable").write_bytes(b"content")
    real_open = archive_module.os.open

    def deny(path, flags, *args, **kwargs):
        if path == "unreadable":
            raise PermissionError("unreadable")
        return real_open(path, flags, *args, **kwargs)

    monkeypatch.setattr(archive_module.os, "open", deny)
    output = tmp_path / "result.tar.gz"
    with pytest.raises(PermissionError):
        package_workspace(workspace, manifest, output)
    assert not output.exists()
    assert not tuple(tmp_path.glob(".result.tar.gz.*.tmp"))


# Iterative collection handles directory depth beyond Python's recursion limit.
def test_package_deep_tree(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    current = workspace / manifest.task_roots[0]
    directories: list[Path] = []
    for _ in range(1050):
        current /= "d"
        current.mkdir()
        directories.append(current)
    (current / "leaf").write_bytes(b"deep")
    try:
        output = tmp_path / "result.tar.gz"
        package_workspace(workspace, manifest, output)
        with tarfile.open(output, "r:gz") as archive:
            assert archive.extractfile(f"{manifest.task_roots[0]}/" + "d/" * 1050 + "leaf")
    finally:
        (current / "leaf").unlink(missing_ok=True)
        for directory in reversed(directories):
            directory.rmdir()


# Manifest file-size limits stop packaging before an oversized result is committed.
def test_package_file_limit(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    limited = manifest.model_copy(
        update={"limits": manifest.limits.model_copy(update={"file_bytes": 1})}
    )
    output = tmp_path / "result.tar.gz"
    with pytest.raises(ValueError, match="file size limit"):
        package_workspace(workspace, limited, output)
    assert not output.exists()


# Manifest entry-count limits stop a result containing more than its root entry.
def test_package_entry_limit(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    limited = manifest.model_copy(
        update={"limits": manifest.limits.model_copy(update={"entries": 1})}
    )
    output = tmp_path / "result.tar.gz"
    with pytest.raises(ValueError, match="entry count limit"):
        package_workspace(workspace, limited, output)
    assert not output.exists()


# Host packaging produces an archive accepted by the unchanged receiver.
def test_package_then_receive_round_trip(released_workspace, tmp_path: Path) -> None:
    manifest, workspace = _copy_workspace(released_workspace, tmp_path)
    output = tmp_path / "result.tar.gz"
    package_workspace(workspace, manifest, output)
    received = receive_submission(output, manifest=manifest, run_directory=tmp_path / "received")
    assert received.files
    assert (received.workspace / manifest.task_roots[0]).is_dir()
