"""Bounded, traversal-free archive reception against a server-owned release."""

from __future__ import annotations

import gzip
import hashlib
import os
import shutil
import stat
import tarfile
import tempfile
import zlib
from contextlib import ExitStack
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

from benchmarks.task import TaskModel, validate_relative_path
from evaluation.task.release import TaskReleaseManifest

_MAX_ARCHIVE_PATH_BYTES = 4096


class SubmissionError(ValueError):
    """A candidate archive violates the public submission contract."""


class ArchiveProvenance(TaskModel):
    archive_sha256: str
    archive_bytes: int


@dataclass(frozen=True)
class ReceivedSubmission:
    archive_path: Path
    archive_sha256: str
    archive_bytes: int
    workspace: Path
    files: tuple[str, ...]


def package_workspace(workspace: Path, manifest: TaskReleaseManifest, archive: Path) -> Path:
    """Atomically collect declared task roots without following filesystem links."""
    if not stat.S_ISDIR(workspace.lstat().st_mode):
        raise ValueError("submission workspace must be a real directory")
    workspace = Path(os.path.abspath(workspace))
    if archive.absolute().is_relative_to(workspace) or archive.resolve().is_relative_to(workspace):
        raise ValueError("submission archive must be outside the workspace")
    archive.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{archive.name}.", suffix=".tmp", dir=archive.parent
    )
    temporary = Path(temporary_name)
    try:
        with ExitStack() as resources, os.fdopen(descriptor, "wb") as stream:
            workspace_fd = _open_package_directory(workspace, resources)
            roots = tuple(
                _package_root_directory(workspace_fd, root, resources)
                for root in manifest.task_roots
            )
            with tarfile.open(fileobj=stream, mode="w:gz", dereference=False) as output:
                count = 0
                total_bytes = 0
                for root, root_fd in zip(manifest.task_roots, roots, strict=True):
                    root_count, root_bytes = _package_tree(output, root_fd, root, manifest)
                    count += root_count
                    total_bytes += root_bytes
                    if count > manifest.limits.entries:
                        raise SubmissionError("archive entry count limit exceeded")
                    if total_bytes > manifest.limits.expanded_bytes:
                        raise SubmissionError("archive payload size limit exceeded")
            stream.flush()
            os.fsync(stream.fileno())
        if temporary.stat().st_size > manifest.limits.compressed_bytes:
            raise SubmissionError("compressed archive size limit exceeded")
        os.replace(temporary, archive)
    finally:
        temporary.unlink(missing_ok=True)
    return archive


def _open_package_directory(workspace: Path, resources: ExitStack) -> int:
    descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    resources.callback(os.close, descriptor)
    for part in workspace.parts[1:]:
        descriptor = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
        resources.callback(os.close, descriptor)
    return descriptor


def _package_root_directory(workspace_fd: int, relative_root: str, resources: ExitStack) -> int:
    descriptor = workspace_fd
    for part in Path(relative_root).parts:
        metadata = os.stat(part, dir_fd=descriptor, follow_symlinks=False)
        if not stat.S_ISDIR(metadata.st_mode):
            raise ValueError(f"submission root must contain only real directories: {relative_root}")
        descriptor = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
        resources.callback(os.close, descriptor)
    return descriptor


def _package_excluded(relative_path: str, manifest: TaskReleaseManifest) -> bool:
    path = PurePosixPath(relative_path)
    return any(part in manifest.excluded_names for part in path.parts) or any(
        path.is_relative_to(PurePosixPath(excluded)) for excluded in manifest.excluded_paths
    )


@dataclass
class _PackageFrame:
    path: str
    components: tuple[str, ...]
    names: list[str]
    identity: tuple[int, int]
    index: int = 0


def _package_tree(
    archive: tarfile.TarFile,
    root_fd: int,
    root: str,
    manifest: TaskReleaseManifest,
) -> tuple[int, int]:
    """Walk from a pinned root with bounded open descriptors and no recursion."""
    archive.addfile(_package_tar_info(root, os.fstat(root_fd)))
    stack = [_package_frame(root_fd, root, ())]
    count = 1
    total_bytes = 0
    while stack:
        frame = stack[-1]
        if frame.index == len(frame.names):
            stack.pop()
            continue
        name = frame.names[frame.index]
        frame.index += 1
        path = f"{frame.path}/{name}"
        validate_relative_path(path, label="submission entry")
        _validate_archive_name(path)
        if _package_excluded(path, manifest):
            continue
        parent_fd = _open_package_relative(root_fd, frame.components)
        try:
            _package_check_frame_identity(frame, os.fstat(parent_fd))
            metadata = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
            if stat.S_ISDIR(metadata.st_mode):
                child_fd = _package_open_child_directory(parent_fd, name, metadata, path)
                try:
                    archive.addfile(_package_tar_info(path, os.fstat(child_fd)))
                    stack.append(_package_frame(child_fd, path, (*frame.components, name)))
                finally:
                    os.close(child_fd)
            else:
                total_bytes += _package_file(archive, parent_fd, name, path, metadata, manifest)
            count += 1
            if count > manifest.limits.entries:
                raise SubmissionError("archive entry count limit exceeded")
            if total_bytes > manifest.limits.expanded_bytes:
                raise SubmissionError("archive payload size limit exceeded")
        finally:
            if parent_fd != root_fd:
                os.close(parent_fd)
    return count, total_bytes


def _package_frame(descriptor: int, path: str, components: tuple[str, ...]) -> _PackageFrame:
    metadata = os.fstat(descriptor)
    return _PackageFrame(
        path=path,
        components=components,
        names=sorted(os.listdir(descriptor)),
        identity=(metadata.st_dev, metadata.st_ino),
    )


def _package_check_frame_identity(frame: _PackageFrame, metadata: os.stat_result) -> None:
    if frame.identity != (metadata.st_dev, metadata.st_ino):
        raise ValueError(f"submission entry changed while packaging: {frame.path}")


def _open_package_relative(root_fd: int, components: tuple[str, ...]) -> int:
    descriptor = root_fd
    try:
        for part in components:
            next_descriptor = os.open(
                part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor
            )
            if descriptor != root_fd:
                os.close(descriptor)
            descriptor = next_descriptor
    except OSError:
        if descriptor != root_fd:
            os.close(descriptor)
        raise
    return descriptor


def _package_open_child_directory(
    parent_fd: int, name: str, metadata: os.stat_result, path: str
) -> int:
    descriptor = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent_fd)
    try:
        _package_check_identity(metadata, os.fstat(descriptor), path)
    except ValueError:
        os.close(descriptor)
        raise
    return descriptor


def _package_file(
    archive: tarfile.TarFile,
    parent_fd: int,
    name: str,
    path: str,
    metadata: os.stat_result,
    manifest: TaskReleaseManifest,
) -> int:
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
        raise ValueError(f"unsupported submission filesystem entry: {path}")
    if metadata.st_size > manifest.limits.file_bytes:
        raise SubmissionError(f"archive file size limit exceeded: {path}")
    descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent_fd)
    with os.fdopen(descriptor, "rb") as source:
        opened = os.fstat(source.fileno())
        _package_check_identity(metadata, opened, path)
        if not stat.S_ISREG(opened.st_mode) or opened.st_nlink != 1:
            raise ValueError(f"submission file changed while packaging: {path}")
        archive.addfile(_package_tar_info(path, opened), source)
    return metadata.st_size


def _package_check_identity(
    expected: os.stat_result, actual: os.stat_result, relative_path: str
) -> None:
    if (expected.st_dev, expected.st_ino) != (actual.st_dev, actual.st_ino):
        raise ValueError(f"submission entry changed while packaging: {relative_path}")


def _package_tar_info(relative_path: str, metadata: os.stat_result) -> tarfile.TarInfo:
    info = tarfile.TarInfo(relative_path)
    info.mode = stat.S_IMODE(metadata.st_mode)
    info.mtime = metadata.st_mtime
    info.uid = metadata.st_uid
    info.gid = metadata.st_gid
    if stat.S_ISDIR(metadata.st_mode):
        info.type = tarfile.DIRTYPE
    else:
        info.size = metadata.st_size
    return info


def receive_submission(
    archive: Path, *, manifest: TaskReleaseManifest, run_directory: Path
) -> ReceivedSubmission:
    """Retain the exact archive, validate all entries, and atomically expose its files."""
    run_directory.mkdir(parents=True, exist_ok=False)
    saved = run_directory / "submission.tar.gz"
    digest, byte_count = _snapshot(archive, saved, manifest.limits.compressed_bytes)
    ArchiveProvenance(archive_sha256=digest, archive_bytes=byte_count).to_json_file(
        run_directory / "archive-provenance.json"
    )
    destination = run_directory / "received"
    with tempfile.TemporaryDirectory(prefix="receive-", dir=run_directory) as staging:
        staging_root = Path(staging)
        expanded = staging_root / "submission.tar"
        _decompress(saved, expanded, manifest.limits.expanded_bytes)
        extracted = staging_root / "workspace"
        extracted.mkdir()
        files = _read_archive(expanded, extracted, manifest)
        required = {
            p
            for p in manifest.files
            if any(Path(p).is_relative_to(root) for root in manifest.task_roots)
        }
        required.update(p for task in manifest.tasks.values() for p in task.required_outputs)
        missing = required - set(files)
        if missing:
            raise SubmissionError(f"required outputs missing: {sorted(missing)}")
        extracted.rename(destination)
    return ReceivedSubmission(saved, digest, byte_count, destination, tuple(sorted(files)))


def _snapshot(source: Path, destination: Path, limit: int) -> tuple[str, int]:
    # Open without following links or blocking on FIFOs; validate the opened inode.
    try:
        descriptor = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError as exc:
        raise SubmissionError("submission must be a readable regular archive file") from exc
    digest = hashlib.sha256()
    byte_count = 0
    with os.fdopen(descriptor, "rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode):
            raise SubmissionError("submission must be a regular archive file")
        if before.st_size > limit:
            raise SubmissionError("compressed archive size limit exceeded")
        with destination.open("xb") as output:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                byte_count += len(chunk)
                if byte_count > limit:
                    raise SubmissionError("compressed archive size limit exceeded")
                digest.update(chunk)
                output.write(chunk)
        after = os.fstat(stream.fileno())
        if (before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise SubmissionError("archive changed during reception")
    destination.chmod(0o444)
    return digest.hexdigest(), byte_count


def _decompress(source: Path, destination: Path, limit: int) -> None:
    byte_count = 0
    try:
        with gzip.open(source, "rb") as stream, destination.open("xb") as output:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                byte_count += len(chunk)
                if byte_count > limit:
                    raise SubmissionError("expanded archive size limit exceeded")
                output.write(chunk)
    except (gzip.BadGzipFile, EOFError, zlib.error) as exc:
        raise SubmissionError("invalid gzip submission") from exc


def _member_path(member: tarfile.TarInfo, manifest: TaskReleaseManifest) -> str:
    # A directory trailing slash is conventional tar syntax; all other spelling is strict.
    name = member.name[:-1] if member.isdir() and member.name.endswith("/") else member.name
    _validate_archive_name(name)
    try:
        validate_relative_path(name)
    except ValueError as exc:
        raise SubmissionError(f"unsafe archive path: {member.name!r}") from exc
    path = PurePosixPath(name)
    if any(p in manifest.excluded_names for p in path.parts):
        raise SubmissionError(f"excluded archive path: {name}")
    if any(path.is_relative_to(PurePosixPath(p)) for p in manifest.excluded_paths):
        raise SubmissionError(f"excluded archive path: {name}")
    inside = any(path.is_relative_to(PurePosixPath(root)) for root in manifest.task_roots)
    ancestor = member.isdir() and any(
        PurePosixPath(root).is_relative_to(path) for root in manifest.task_roots
    )
    if not inside and not ancestor:
        raise SubmissionError(f"archive path outside task roots: {name}")
    return name


def _read_archive(source: Path, destination: Path, manifest: TaskReleaseManifest) -> dict[str, str]:
    files: dict[str, str] = {}
    seen: set[str] = set()
    total_bytes = 0
    try:
        with tarfile.open(source, "r:") as archive:
            for index, member in enumerate(archive, start=1):
                if index > manifest.limits.entries:
                    raise SubmissionError("archive entry count limit exceeded")
                if not (member.isfile() or member.isdir()) or member.issparse():
                    raise SubmissionError(f"unsupported archive entry: {member.name}")
                if member.isdir() and member.size != 0:
                    raise SubmissionError(f"directory entry carries payload: {member.name}")
                name = _member_path(member, manifest)
                if name in seen:
                    raise SubmissionError(f"duplicate archive entry: {name}")
                seen.add(name)
                if member.size < 0 or member.size > manifest.limits.file_bytes:
                    raise SubmissionError(f"archive file size limit exceeded: {name}")
                total_bytes += member.size
                if total_bytes > manifest.limits.expanded_bytes:
                    raise SubmissionError("archive payload size limit exceeded")
                digest = _extract_member(archive, member, destination / name, name, manifest)
                if digest is not None:
                    files[name] = digest

            _require_zero_padding(archive)
    except (tarfile.TarError, EOFError) as exc:
        raise SubmissionError("invalid tar submission") from exc
    return files


def _extract_member(
    archive: tarfile.TarFile,
    member: tarfile.TarInfo,
    target: Path,
    name: str,
    manifest: TaskReleaseManifest,
) -> str | None:
    if member.isdir():
        if name in manifest.files:
            raise SubmissionError(f"released file replaced by directory: {name}")
        target.mkdir(parents=True, exist_ok=True)
        return None
    stream = archive.extractfile(member)
    if stream is None:
        raise SubmissionError(f"unreadable archive file: {name}")
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        raise SubmissionError(f"archive file/directory conflict: {name}")
    with stream, target.open("xb") as output:
        shutil.copyfileobj(stream, output, length=1024 * 1024)
    target.chmod(0o644)
    digest = hashlib.sha256(target.read_bytes()).hexdigest()
    if name in manifest.fixed_files and digest != manifest.fixed_files[name]:
        raise SubmissionError(f"fixed release file changed: {name}")
    return digest


def _validate_archive_name(name: str) -> None:
    if len(name) > _MAX_ARCHIVE_PATH_BYTES:
        raise SubmissionError("archive path length limit exceeded")
    try:
        payload = name.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise SubmissionError("archive path must be valid UTF-8") from exc
    if len(payload) > _MAX_ARCHIVE_PATH_BYTES:
        raise SubmissionError("archive path length limit exceeded")


def _require_zero_padding(archive: tarfile.TarFile) -> None:
    archive.fileobj.seek(archive.offset)
    size = 0
    for chunk in iter(lambda: archive.fileobj.read(1024 * 1024), b""):
        size += len(chunk)
        if chunk.strip(b"\x00"):
            raise SubmissionError("nonzero trailing data after tar end marker")
    if size < 2 * tarfile.BLOCKSIZE:
        raise SubmissionError("truncated tar end marker")
