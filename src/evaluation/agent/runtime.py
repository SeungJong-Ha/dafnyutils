"""Benchmark-owned candidate preparation, isolation, execution, and collection."""

from __future__ import annotations

import hashlib
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path
from typing import Generic, TypeVar

import yaml

from evaluation.agent.container import candidate_container_plan
from evaluation.agent.delivery import agent_prompt, write_agent_task
from evaluation.agent.protocol import CandidateLayout, agent_command
from evaluation.agent.report import normal_termination_detail
from evaluation.enums import MountMode
from evaluation.submission.archive import package_workspace
from evaluation.submission.container_mounts import (
    CONTAINER_ORACLE_ISOLATION_ENTRYPOINT,
    ContainerMount,
    ContainerWorkspacePlan,
    write_mount_manifest,
)
from evaluation.submission.sandbox import (
    docker_runtime_available,
    prepare_oracle_executable_block,
    seed_workspace_isolation_tools,
)
from evaluation.task.release import PreparedRelease, PreparedReleaseTask, TaskReleaseManifest
from evaluation.task.workspace import WorkspaceRoots

_LAYOUT = CandidateLayout()
_STAGING_SERVICE = "task-staging"
_AGENT_RUNTIME_ENV_KEYS = (
    "DOTNET_GCHeapHardLimit",
    "COMPlus_GCHeapHardLimit",
    "NUGET_PACKAGES",
    "RestoreSources",
    "RUSTUP_HOME",
    "CARGO_HOME",
    "CARGO_NET_OFFLINE",
)
_DOCKER_COMMAND_ENV_KEYS = (
    "PATH",
    "HOME",
    "DOCKER_CERT_PATH",
    "DOCKER_CONFIG",
    "DOCKER_CONTEXT",
    "DOCKER_HOST",
    "DOCKER_TLS_VERIFY",
    "TMPDIR",
    "XDG_RUNTIME_DIR",
)
_DOCKER_NAME_SANITIZE_RE = re.compile(r"[^a-zA-Z0-9_.-]+")
_DOCKER_PROJECT_NAME = "dafnyutils-eval"
_DOCKER_EVAL_RUN_LABEL = "dafnyutils.eval.run"
_DOCKER_EVAL_TASK_LABEL = "dafnyutils.eval.task"
_DOCKER_EVAL_TARGET_LABEL = "dafnyutils.eval.target"
_SANDBOX_CLEANUP_TIMEOUT_SEC = 120


class SandboxProfile(StrEnum):
    DEFAULT = "default"
    NESTED_USER_NAMESPACE = "nested-user-namespace"


@dataclass(frozen=True)
class AgentPreparationContext:
    run_id: str
    task_path: Path
    layout: CandidateLayout
    workspace_directory: Path
    staging_directory: Path
    agent_home_directory: Path
    model_workspace_directory: Path
    writable_workspace_paths: tuple[Path, ...]


@dataclass(frozen=True)
class AgentLaunchSpec:
    image: str
    environment: Mapping[str, str] = field(default_factory=dict)
    forwarded_secret_environment: tuple[str, ...] = ()
    sandbox_profile: SandboxProfile = SandboxProfile.DEFAULT
    notes: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.image.strip():
            raise ValueError("agent image must not be empty")
        for key in (*self.environment.keys(), *self.forwarded_secret_environment):
            if not key or "=" in key or "\x00" in key:
                raise ValueError(f"invalid environment variable name: {key!r}")


@dataclass(frozen=True)
class AgentSandboxContext:
    docker_available: bool
    workspace_dir: Path
    task_dir: Path
    run_dir: Path
    artifact_directory: Path
    compose_files: tuple[Path, ...]
    compose_project_name: str
    mount_manifest_path: Path
    agent_container_name: str
    container_cleanup_label: str
    command: str
    env: dict[str, str]
    notes: tuple[str, ...]
    bundle_directory: Path | None = None
    control_dir: Path | None = None


@dataclass(frozen=True)
class CandidateRunContext:
    run_dir: Path
    utility_name: str
    comparison_id: str
    agent_artifact_dir: Path


class CandidateTerminationError(RuntimeError):
    """The candidate environment could not be confirmed to have stopped."""


def sandbox_environment(env: Mapping[str, str]) -> dict[str, str]:
    return {key: env[key] for key in _AGENT_RUNTIME_ENV_KEYS if key in env}


def docker_command_environment(
    env: Mapping[str, str],
    *,
    forwarded_secret_environment: tuple[str, ...],
) -> dict[str, str]:
    command_env = {key: env[key] for key in _DOCKER_COMMAND_ENV_KEYS if key in env}
    command_env.update(sandbox_environment(env))
    for key in forwarded_secret_environment:
        if key in env:
            command_env[key] = env[key]
    return command_env


def prepare_agent_mount_permissions(agent_plan: ContainerWorkspacePlan) -> None:
    read_only_sources = tuple(
        mount.source.resolve() for mount in agent_plan.mounts if mount.mode == MountMode.READ_ONLY
    )
    for mount in agent_plan.mounts:
        if mount.mode == MountMode.READ_WRITE:
            _make_owner_writable_tree(mount.source, read_only_sources)


def write_compose_override(
    *,
    path: Path,
    agent_plan: ContainerWorkspacePlan,
    agent_environment: dict[str, str],
    agent_container_name: str,
    staging_container_name: str,
    staged_workspace_dir: Path,
    agent_launch: AgentLaunchSpec,
    launch_command: tuple[str, ...],
    container_labels: dict[str, str] | None = None,
) -> None:
    labels = container_labels or {}
    agent_service: dict[str, object] = {
        "container_name": agent_container_name,
        "working_dir": agent_plan.working_dir,
        "user": "agent",
        "build": {"args": {"AGENT_UID": str(os.getuid()), "AGENT_GID": str(os.getgid())}},
        "image": agent_launch.image,
        # Compose interpolates dollar signs even in YAML argument lists.
        "command": [
            CONTAINER_ORACLE_ISOLATION_ENTRYPOINT,
            *(argument.replace("$", "$$") for argument in launch_command),
        ],
        "environment": {
            **agent_environment,
            **agent_plan.environment,
            **agent_launch.environment,
            **{key: None for key in agent_launch.forwarded_secret_environment},
        },
        "labels": labels,
        "volumes": [mount.as_compose_volume() for mount in agent_plan.mounts],
    }
    if agent_launch.sandbox_profile is SandboxProfile.NESTED_USER_NAMESPACE:
        agent_service["security_opt"] = [
            "seccomp=unconfined",
            "apparmor=unconfined",
            "systempaths=unconfined",
        ]
    path.parent.mkdir(parents=True, exist_ok=True)
    staging_service: dict[str, object] = {
        "container_name": staging_container_name,
        "image": "dafnyutils-task:latest",
        "command": ["sleep", "infinity"],
        "network_mode": "none",
        "labels": labels,
        "volumes": [
            ContainerMount(
                staged_workspace_dir, _LAYOUT.workspace_directory, MountMode.READ_WRITE
            ).as_compose_volume()
        ],
    }
    path.write_text(
        _compose_yaml({"agent-workflow": agent_service, _STAGING_SERVICE: staging_service}),
        encoding="utf-8",
    )


def build_docker_compose_agent_command(
    *,
    compose_files: tuple[Path, ...],
    service: str,
    project_name: str,
    container_name: str,
    staging_container_name: str,
    workspace_dir: Path,
) -> str:
    parts = ["docker", "compose"]
    parts.extend(("-p", project_name))
    for compose_file in compose_files:
        parts.extend(("-f", str(compose_file)))
    create_staging = shlex.join((*parts, "create", "--no-build", _STAGING_SERVICE))
    copy = shlex.join(
        (
            "docker",
            "cp",
            f"{workspace_dir}/.",
            f"{staging_container_name}:{_LAYOUT.workspace_directory}/",
        )
    )
    remove_staging = shlex.join(("docker", "rm", staging_container_name))
    create = shlex.join((*parts, "create", "--no-build", service))
    start = shlex.join(("docker", "start", container_name))
    logs = shlex.join(("docker", "logs", "--follow", container_name))
    wait = shlex.join(("docker", "wait", container_name))
    # Keep errexit out of the caller's login-shell logout hooks.
    return (
        f"(set -e; {create_staging}; {copy}; {remove_staging} >/dev/null; "
        f"{create}; {start} >/dev/null; {logs}; "
        f'agent_status=$({wait}); exit "$agent_status")'
    )


def prepare_agent_sandbox_context(
    *,
    prepare_agent: Callable[[AgentPreparationContext], AgentLaunchSpec],
    record_launch: Callable[[tuple[str, ...], str], None],
    compose_file: Path,
    env: dict[str, str],
    run_context: CandidateRunContext,
    prepared_candidate: PreparedReleaseTask,
    release: PreparedRelease,
) -> AgentSandboxContext:
    if not docker_runtime_available():
        raise RuntimeError(
            "docker compose sandbox is required for agent execution, but Docker is unavailable"
        )
    control_dir = Path(
        tempfile.mkdtemp(
            prefix=f".{run_context.run_dir.name}-control-",
            dir=run_context.run_dir.parent,
        )
    )
    try:
        return _prepare_agent_sandbox_context(
            prepare_agent=prepare_agent,
            record_launch=record_launch,
            compose_file=compose_file,
            env=env,
            run_context=run_context,
            prepared_candidate=prepared_candidate,
            release=release,
            control_dir=control_dir,
        )
    except BaseException:
        shutil.rmtree(control_dir, ignore_errors=True)
        raise


def _prepare_agent_sandbox_context(
    *,
    prepare_agent: Callable[[AgentPreparationContext], AgentLaunchSpec],
    record_launch: Callable[[tuple[str, ...], str], None],
    compose_file: Path,
    env: dict[str, str],
    run_context: CandidateRunContext,
    prepared_candidate: PreparedReleaseTask,
    release: PreparedRelease,
    control_dir: Path,
) -> AgentSandboxContext:
    run_dir = run_context.run_dir
    utility_name = run_context.utility_name
    task_spec = prepared_candidate.workspace_spec
    sandbox_root = run_dir / "sandbox"
    roots = WorkspaceRoots(
        sandbox_root=sandbox_root,
        workspace_root=prepared_candidate.workspace,
        task_root=sandbox_root / "task",
        run_root=sandbox_root / "run",
        oracle_target_root=prepared_candidate.workspace,
        candidate_output_root=sandbox_root / "run/candidate_outputs",
    )
    seed_workspace_isolation_tools(roots.run_root)
    agent_home = control_dir / "agent_home"
    agent_home.mkdir(mode=0o700)
    agent_tmp = control_dir / "agent_tmp"
    agent_tmp.mkdir(mode=0o700)
    staged_workspace = control_dir / "public_workspace"
    staged_workspace.mkdir(mode=0o755)
    launcher_root = control_dir / "agent_runtime"
    launcher_root.mkdir(parents=True, exist_ok=True)
    agent_artifact_dir = run_context.agent_artifact_dir
    agent_artifact_dir.mkdir(parents=True, exist_ok=True)
    oracle_block = prepare_oracle_executable_block(
        control_dir=control_dir,
        task_domain=prepared_candidate.configuration.task_domain,
        utility_name=utility_name,
    )
    task_payload = write_agent_task(prepared_candidate, release.manifest, roots.task_root)
    prompt = agent_prompt(task_payload)
    launch_command = agent_command(prompt)
    agent_plan = candidate_container_plan(
        roots=roots,
        task_spec=task_spec,
        agent_artifact_dir=agent_artifact_dir,
        agent_home_dir=agent_home,
        agent_tmp_dir=agent_tmp,
        model_workspace_dir=control_dir / "model_workspace",
        launcher_root=launcher_root,
        staged_workspace_dir=staged_workspace,
        oracle_block=oracle_block,
    )
    agent_launch = prepare_agent(
        AgentPreparationContext(
            run_id=run_dir.name,
            task_path=roots.task_root / _LAYOUT.task_filename,
            layout=_LAYOUT,
            workspace_directory=roots.workspace_root,
            staging_directory=launcher_root,
            agent_home_directory=agent_home,
            model_workspace_directory=control_dir / "model_workspace",
            writable_workspace_paths=task_spec.editable_paths,
        )
    )
    launcher = launcher_root / _LAYOUT.launcher_filename
    if launcher.is_symlink() or not launcher.is_file() or not os.access(launcher, os.X_OK):
        raise RuntimeError("agent adapter must stage an executable regular file named agent")
    command_env = docker_command_environment(
        env,
        forwarded_secret_environment=agent_launch.forwarded_secret_environment,
    )
    mount_manifest_path = roots.run_root / "container_mounts.json"
    write_mount_manifest(mount_manifest_path, (agent_plan,))
    prepare_agent_mount_permissions(agent_plan)
    compose_override = control_dir / "docker-compose.override.yml"
    compose_files = (compose_file, compose_override)
    cleanup_label = sandbox_container_cleanup_label(
        run_dir=run_dir,
        workflow_id=run_context.comparison_id,
        utility_name=utility_name,
    )
    project_name = (
        f"{_DOCKER_PROJECT_NAME}-{hashlib.sha256(str(run_dir.resolve()).encode()).hexdigest()[:12]}"
    )
    agent_container_name = f"{cleanup_label}-agent"
    staging_container_name = f"{cleanup_label}-staging"
    write_compose_override(
        path=compose_override,
        agent_plan=agent_plan,
        agent_environment=sandbox_environment(env),
        agent_container_name=agent_container_name,
        staging_container_name=staging_container_name,
        staged_workspace_dir=staged_workspace,
        agent_launch=agent_launch,
        launch_command=launch_command,
        container_labels={
            _DOCKER_EVAL_RUN_LABEL: cleanup_label,
            _DOCKER_EVAL_TASK_LABEL: _docker_name_component(
                run_context.comparison_id, fallback="default-workflow"
            ),
            _DOCKER_EVAL_TARGET_LABEL: _docker_name_component(utility_name),
        },
    )
    record_launch(launch_command, prompt)
    notes = [
        "sandbox mode fixed to docker compose workspace isolation",
        "verified public workspace is copied into a stopped staging container before agent start",
        "agent workflow runs end-to-end in one agent container",
        "candidate launch follows the benchmark agent protocol",
        "host packages result.tar.gz only after normal agent exit and confirmed termination",
        "editable workspace paths are run-local mounts; "
        "task inputs and launcher code are read-only mounts",
        "the benchmark creates its own evaluator from the archive and public release",
    ]
    if oracle_block is not None:
        notes.append(f"agent containers block the task oracle executable at {oracle_block.target}")
    notes.extend(agent_launch.notes)
    return AgentSandboxContext(
        docker_available=True,
        workspace_dir=roots.workspace_root,
        task_dir=roots.task_root,
        run_dir=roots.run_root,
        artifact_directory=agent_artifact_dir,
        compose_files=compose_files,
        compose_project_name=project_name,
        mount_manifest_path=mount_manifest_path,
        agent_container_name=agent_container_name,
        container_cleanup_label=cleanup_label,
        command=build_docker_compose_agent_command(
            compose_files=compose_files,
            service="agent-workflow",
            project_name=project_name,
            container_name=agent_container_name,
            staging_container_name=staging_container_name,
            workspace_dir=roots.workspace_root,
        ),
        env=command_env,
        notes=tuple(notes),
        control_dir=control_dir,
        bundle_directory=launcher_root,
    )


def stop_agent_sandbox_containers(
    container_cleanup_label: str,
    env: dict[str, str],
) -> None:
    """Close candidate execution even when diagnostic sandbox files are retained."""
    command = [
        "docker",
        "ps",
        "-q",
        "--filter",
        f"label={_DOCKER_EVAL_RUN_LABEL}={container_cleanup_label}",
    ]
    try:
        active = subprocess.run(
            command,
            cwd=None,
            env=env,
            capture_output=True,
            text=True,
            check=True,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
        container_ids = active.stdout.split()
        if not container_ids:
            return
        subprocess.run(
            ["docker", "stop", *container_ids],
            cwd=None,
            env=env,
            capture_output=True,
            text=True,
            check=True,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
        remaining = subprocess.run(
            command,
            cwd=None,
            env=env,
            capture_output=True,
            text=True,
            check=True,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise CandidateTerminationError("cannot confirm candidate environment termination") from exc
    if remaining.stdout.strip():
        raise CandidateTerminationError("candidate containers remain active before evaluation")


def cleanup_agent_sandbox_context(context: AgentSandboxContext) -> None:
    cleanup_agent_sandbox_containers(context.container_cleanup_label, context.env)


def cleanup_sandbox_control_files(context: AgentSandboxContext) -> None:
    if context.control_dir is not None:
        shutil.rmtree(context.control_dir, ignore_errors=True)


def cleanup_agent_sandbox_containers(
    container_cleanup_label: str,
    env: dict[str, str] | None = None,
) -> None:
    label_filter = f"label={_DOCKER_EVAL_RUN_LABEL}={container_cleanup_label}"
    command_env = os.environ if env is None else env
    try:
        listed = subprocess.run(
            ["docker", "ps", "-aq", "--filter", label_filter],
            cwd=None,
            env=command_env,
            capture_output=True,
            text=True,
            check=False,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        print(f"[warn] failed to clean up Docker sandbox: {exc}", file=sys.stderr)
        return
    if listed.returncode != 0:
        stderr = listed.stderr.strip()
        detail = f": {stderr}" if stderr else ""
        print(
            f"[warn] Docker sandbox cleanup list exited {listed.returncode}{detail}",
            file=sys.stderr,
        )
        return
    container_ids = listed.stdout.split()
    if not container_ids:
        return
    try:
        removed = subprocess.run(
            ["docker", "rm", "-f", *container_ids],
            cwd=None,
            env=command_env,
            capture_output=True,
            text=True,
            check=False,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        print(f"[warn] failed to clean up Docker sandbox: {exc}", file=sys.stderr)
        return
    if removed.returncode != 0:
        stderr = removed.stderr.strip()
        detail = f": {stderr}" if stderr else ""
        print(
            f"[warn] Docker sandbox cleanup remove exited {removed.returncode}{detail}",
            file=sys.stderr,
        )
        return
    try:
        remaining = subprocess.run(
            ["docker", "ps", "-aq", "--filter", label_filter],
            cwd=None,
            env=command_env,
            capture_output=True,
            text=True,
            check=False,
            timeout=_SANDBOX_CLEANUP_TIMEOUT_SEC,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        print(f"[warn] failed to verify Docker sandbox cleanup: {exc}", file=sys.stderr)
        return
    if remaining.returncode != 0 or remaining.stdout.split():
        stderr = remaining.stderr.strip()
        detail = f": {stderr}" if stderr else ""
        print(
            f"[warn] Docker sandbox cleanup did not remove all labeled containers{detail}",
            file=sys.stderr,
        )


def sandbox_container_cleanup_label(*, run_dir: Path, workflow_id: str, utility_name: str) -> str:
    task_name = _docker_name_component(workflow_id, fallback="default-workflow")
    target_name = _docker_name_component(utility_name)
    digest = hashlib.sha256(str(run_dir.resolve()).encode("utf-8")).hexdigest()[:12]
    return f"{task_name}-{target_name}-{digest}"


def _docker_name_component(raw: str, *, fallback: str = "unknown") -> str:
    sanitized = _DOCKER_NAME_SANITIZE_RE.sub("-", raw).strip("-._").lower()
    return sanitized or fallback


def _make_owner_writable_tree(path: Path, read_only_roots: tuple[Path, ...]) -> None:
    if (
        not path.exists()
        or path.is_symlink()
        or _path_within_any_root(path.resolve(), read_only_roots)
    ):
        return
    _make_owner_writable(path)
    if not path.is_dir():
        return
    for root, dirs, files in os.walk(path, topdown=True):
        root_path = Path(root)
        dirs[:] = [
            name
            for name in dirs
            if not _path_within_any_root((root_path / name).resolve(), read_only_roots)
        ]
        _make_owner_writable(root_path)
        for name in dirs:
            _make_owner_writable(root_path / name)
        for name in files:
            child = root_path / name
            if not _path_within_any_root(child.resolve(), read_only_roots):
                _make_owner_writable(child)


def _make_owner_writable(path: Path) -> None:
    if path.is_symlink():
        return
    mode = stat.S_IMODE(path.stat(follow_symlinks=False).st_mode)
    path.chmod(mode | stat.S_IRUSR | stat.S_IWUSR | (stat.S_IXUSR if path.is_dir() else 0))


def _path_within_any_root(path: Path, roots: tuple[Path, ...]) -> bool:
    return any(path == root or root in path.parents for root in roots)


def _compose_yaml(services: dict[str, dict[str, object]]) -> str:
    return yaml.safe_dump({"services": services}, sort_keys=False)


T = TypeVar("T")


@dataclass(frozen=True)
class CandidateExecution(Generic[T]):
    payload: T
    execution_present: bool
    exit_code: int | None
    timed_out: bool
    protocol_error: str | None


@dataclass(frozen=True)
class CandidateLifecycleOutcome(Generic[T]):
    context: AgentSandboxContext | None
    execution: CandidateExecution[T] | None
    failure_reason: str | None
    termination_detail: str | None
    agent_failed: bool


def run_candidate_lifecycle(
    *,
    prepare: Callable[[], AgentSandboxContext],
    execute: Callable[[AgentSandboxContext], CandidateExecution[T]],
    manifest: TaskReleaseManifest,
    archive_path: Path,
) -> CandidateLifecycleOutcome[T]:
    """Collect an archive only after a normal run and confirmed container shutdown."""
    try:
        context = prepare()
    except RuntimeError as exc:
        return CandidateLifecycleOutcome(None, None, str(exc), None, True)

    execution: CandidateExecution[T] | None = None
    termination_error: str | None = None
    try:
        execution = execute(context)
    finally:
        try:
            stop_agent_sandbox_containers(context.container_cleanup_label, context.env)
        except CandidateTerminationError as exc:
            termination_error = str(exc)
        finally:
            try:
                cleanup_agent_sandbox_context(context)
            finally:
                cleanup_sandbox_control_files(context)

    if termination_error is not None:
        return CandidateLifecycleOutcome(context, execution, termination_error, None, True)
    detail = normal_termination_detail(
        execution_present=execution.execution_present if execution else False,
        exit_code=execution.exit_code if execution else None,
        timed_out=execution.timed_out if execution else False,
        protocol_error=execution.protocol_error if execution else None,
    )
    if detail is not None:
        return CandidateLifecycleOutcome(
            context, execution, f"agent did not terminate normally: {detail}", detail, True
        )
    try:
        package_workspace(Path(os.path.realpath(context.workspace_dir)), manifest, archive_path)
    except (ValueError, OSError, tarfile.TarError) as exc:
        return CandidateLifecycleOutcome(
            context, execution, f"host submission packaging failed: {exc}", None, False
        )
    return CandidateLifecycleOutcome(context, execution, None, None, False)
