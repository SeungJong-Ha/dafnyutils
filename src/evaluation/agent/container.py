"""Build the benchmark-owned candidate container view."""

from __future__ import annotations

from pathlib import Path

from evaluation.agent.protocol import CandidateLayout
from evaluation.enums import MountMode
from evaluation.submission.container_mounts import (
    ContainerMount,
    ContainerWorkspacePlan,
    OracleExecutableBlock,
    add_oracle_executable_block,
)
from evaluation.task.workspace import TaskWorkspaceSpec, WorkspaceRoots
from runtime.filesystem import path_within_root, safe_relative_path

_WORKSPACE_WRITABLE_DIRS = (Path("_build"),)
_WORKSPACE_METADATA_DIRS = (Path(".agents"), Path(".git"))


def candidate_container_plan(
    *,
    roots: WorkspaceRoots,
    task_spec: TaskWorkspaceSpec,
    agent_artifact_dir: Path,
    agent_home_dir: Path,
    agent_tmp_dir: Path,
    model_workspace_dir: Path,
    launcher_root: Path,
    staged_workspace_dir: Path,
    oracle_block: OracleExecutableBlock | None = None,
    layout: CandidateLayout = CandidateLayout(),
) -> ContainerWorkspacePlan:
    """Mount public inputs read-only and requested output paths read-write."""
    run_root = roots.run_root
    reserve_agent_entry(roots.workspace_root, staged_workspace_dir, layout=layout)
    for directory in (
        agent_tmp_dir,
        agent_artifact_dir,
        agent_home_dir,
        launcher_root,
        model_workspace_dir,
    ):
        directory.mkdir(parents=True, exist_ok=True)
    for relative in (Path("tmp/dotnet-cli-home"), Path("cache/npm")):
        (model_workspace_dir / relative).mkdir(parents=True, exist_ok=True)
    project_config = task_spec.utility_dir / "dfyconfig.toml"
    mounts = [
        ContainerMount(staged_workspace_dir, layout.workspace_directory, MountMode.READ_ONLY),
        ContainerMount(
            roots.workspace_root / project_config,
            _workspace_target(project_config, layout),
            MountMode.READ_ONLY,
        ),
        ContainerMount(roots.task_root, layout.task_directory, MountMode.READ_ONLY),
        ContainerMount(model_workspace_dir, layout.scratch_directory, MountMode.READ_WRITE),
        ContainerMount(run_root, layout.run_directory, MountMode.READ_WRITE),
        ContainerMount(agent_artifact_dir, layout.artifact_directory, MountMode.READ_WRITE),
        ContainerMount(agent_home_dir, layout.home_directory, MountMode.READ_WRITE),
        ContainerMount(launcher_root, layout.bundle_directory, MountMode.READ_ONLY),
        ContainerMount(
            launcher_root / layout.launcher_filename, layout.launcher_path, MountMode.READ_ONLY
        ),
        ContainerMount(agent_tmp_dir, layout.tmp_directory, MountMode.READ_WRITE),
    ]
    mounts.extend(_editable_output_mounts(roots.workspace_root, task_spec.editable_paths, layout))
    mounts.extend(
        _read_only_workspace_mounts(roots.workspace_root, task_spec.read_only_paths, layout)
    )
    mounts.extend(_workspace_auxiliary_mounts(run_root, roots.workspace_root, layout))
    environment: dict[str, str] = {
        "HOME": layout.home_directory,
        "PWD": layout.workspace_directory,
        "TMPDIR": str(Path(layout.scratch_directory) / "tmp"),
        "DOTNET_CLI_HOME": str(Path(layout.scratch_directory) / "tmp/dotnet-cli-home"),
        "NPM_CONFIG_CACHE": str(Path(layout.scratch_directory) / "cache/npm"),
    }
    add_oracle_executable_block(mounts, environment, oracle_block)
    return ContainerWorkspacePlan(
        service="agent-workflow",
        mounts=_dedupe_mounts(tuple(mounts)),
        working_dir=layout.workspace_directory,
        environment=environment,
    )


def reserve_agent_entry(
    workspace_root: Path,
    staged_workspace_dir: Path,
    *,
    layout: CandidateLayout = CandidateLayout(),
) -> None:
    """Reserve the public workspace launcher path before bind mounts are composed."""
    reserved = (
        (layout.launcher_filename, False),
        (Path(layout.task_directory).name, True),
        (Path(layout.scratch_directory).name, True),
    )
    for name, directory in reserved:
        source = workspace_root / name
        if source.exists() or source.is_symlink():
            raise RuntimeError(f"public workspace conflicts with reserved agent entry: {name}")
        staged = staged_workspace_dir / name
        if directory:
            staged.mkdir()
        else:
            staged.touch()


def _editable_output_mounts(
    workspace_root: Path, editable_paths: tuple[Path, ...], layout: CandidateLayout
) -> tuple[ContainerMount, ...]:
    mounts: list[ContainerMount] = []
    for rel_path in editable_paths:
        _validate_workspace_relative_path(rel_path)
        source = workspace_root / rel_path
        if not path_within_root(source, workspace_root):
            raise ValueError(f"editable path escapes workspace: {rel_path}")
        if not source.exists():
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("", encoding="utf-8")
        mounts.append(
            ContainerMount(source, _workspace_target(rel_path, layout), MountMode.READ_WRITE)
        )
    return tuple(mounts)


def _read_only_workspace_mounts(
    workspace_root: Path, read_only_paths: tuple[Path, ...], layout: CandidateLayout
) -> tuple[ContainerMount, ...]:
    mounts: list[ContainerMount] = []
    for rel_path in read_only_paths:
        _validate_workspace_relative_path(rel_path)
        source = workspace_root / rel_path
        if not path_within_root(source, workspace_root):
            raise ValueError(f"read-only path escapes workspace: {rel_path}")
        if not source.is_file():
            raise FileNotFoundError(f"read-only workspace input is missing: {rel_path}")
        mounts.append(
            ContainerMount(source, _workspace_target(rel_path, layout), MountMode.READ_ONLY)
        )
    return tuple(mounts)


def _workspace_auxiliary_mounts(
    run_root: Path, workspace_root: Path, layout: CandidateLayout
) -> tuple[ContainerMount, ...]:
    for rel_path in _WORKSPACE_METADATA_DIRS:
        _ensure_workspace_directory(workspace_root, rel_path)
    writable_root = run_root / "workspace_writable"
    mounts: list[ContainerMount] = []
    for rel_path in _WORKSPACE_WRITABLE_DIRS:
        _ensure_workspace_directory(workspace_root, rel_path)
        source = writable_root / rel_path
        source.mkdir(parents=True, exist_ok=True)
        mounts.append(
            ContainerMount(source, _workspace_target(rel_path, layout), MountMode.READ_WRITE)
        )
    return tuple(mounts)


def _ensure_workspace_directory(workspace_root: Path, rel_path: Path) -> None:
    _validate_workspace_relative_path(rel_path)
    target = workspace_root / rel_path
    if not path_within_root(target, workspace_root):
        raise ValueError(f"mountpoint path escapes workspace: {rel_path}")
    target.mkdir(parents=True, exist_ok=True)


def _workspace_target(rel_path: Path, layout: CandidateLayout) -> str:
    return str(Path(layout.workspace_directory) / rel_path)


def _validate_workspace_relative_path(rel_path: Path) -> None:
    if safe_relative_path(str(rel_path)) != rel_path:
        raise ValueError(f"editable path escapes workspace: {rel_path}")


def _dedupe_mounts(mounts: tuple[ContainerMount, ...]) -> tuple[ContainerMount, ...]:
    seen: dict[str, ContainerMount] = {}
    ordered: list[ContainerMount] = []
    for mount in mounts:
        if not mount.target.startswith("/"):
            raise ValueError(f"container mount target must be absolute: {mount.target}")
        existing = seen.get(mount.target)
        if existing is not None:
            if existing != mount:
                raise ValueError(f"conflicting container mount target: {mount.target}")
            continue
        seen[mount.target] = mount
        ordered.append(mount)
    return tuple(ordered)
