"""Candidate lifecycle barriers with controlled execution and archive collection."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest
import yaml

from evaluation.agent import runtime
from evaluation.agent.runtime import (
    AgentLaunchSpec,
    AgentSandboxContext,
    CandidateExecution,
    CandidateTerminationError,
    SandboxProfile,
    build_docker_compose_agent_command,
    run_candidate_lifecycle,
    write_compose_override,
)
from evaluation.submission.container_mounts import ContainerWorkspacePlan


def _context(tmp_path: Path) -> AgentSandboxContext:
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    return AgentSandboxContext(
        docker_available=False,
        workspace_dir=workspace,
        task_dir=tmp_path / "task",
        run_dir=tmp_path / "run",
        artifact_directory=tmp_path / "artifacts",
        compose_files=(),
        compose_project_name="controlled",
        mount_manifest_path=tmp_path / "mounts.json",
        agent_container_name="controlled-agent",
        container_cleanup_label="controlled",
        command="true",
        env={},
        notes=(),
    )


def _execution(
    *,
    exit_code: int | None = 0,
    timed_out: bool = False,
    protocol_error: str | None = None,
    execution_present: bool = True,
) -> CandidateExecution[str]:
    return CandidateExecution("observed", execution_present, exit_code, timed_out, protocol_error)


def _controlled_boundaries(monkeypatch: pytest.MonkeyPatch, events: list[str]) -> None:
    monkeypatch.setattr(
        runtime, "stop_agent_sandbox_containers", lambda label, env: events.append("stop")
    )
    monkeypatch.setattr(
        runtime, "cleanup_agent_sandbox_context", lambda context: events.append("remove")
    )
    monkeypatch.setattr(
        runtime, "cleanup_sandbox_control_files", lambda context: events.append("control")
    )
    monkeypatch.setattr(
        runtime, "package_workspace", lambda workspace, manifest, archive: events.append("archive")
    )


# A normal candidate is archived only after confirmed shutdown and cleanup.
def test_normal_run_orders_archive_after_shutdown(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _context(tmp_path)
    outcome = run_candidate_lifecycle(
        prepare=lambda: events.append("prepare") or context,
        execute=lambda prepared: events.append("execute") or _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert events == ["prepare", "execute", "stop", "remove", "control", "archive"]
    assert outcome.failure_reason is None
    assert not outcome.agent_failed


# A preparation failure does not execute or package a candidate.
def test_preparation_failure_preserves_reason(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_prepare() -> AgentSandboxContext:
        raise RuntimeError("controlled setup failure")

    outcome = run_candidate_lifecycle(
        prepare=fail_prepare,
        execute=lambda context: events.append("execute") or _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "controlled setup failure"
    assert outcome.agent_failed
    assert events == []


# A nonzero candidate exit blocks collection while still closing its environment.
def test_nonzero_exit_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(exit_code=7),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "agent did not terminate normally: exit code 7"
    assert outcome.agent_failed
    assert events == ["stop", "remove", "control"]


# A timed-out candidate blocks collection even if the command reports a zero exit.
def test_timeout_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(timed_out=True),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason is not None and "timed out" in outcome.failure_reason
    assert events == ["stop", "remove", "control"]


# An invalid candidate report blocks collection after a successful process exit.
def test_protocol_error_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(protocol_error="agent protocol error: bad report"),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == (
        "agent did not terminate normally: agent protocol error: bad report"
    )
    assert events == ["stop", "remove", "control"]


# An absent command retains the established missing-command failure detail.
def test_missing_execution_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(exit_code=None, execution_present=False),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "agent did not terminate normally: agent command was not run"
    assert events == ["stop", "remove", "control"]


# An unconfirmed shutdown blocks archive collection and still removes control files.
def test_unconfirmed_shutdown_blocks_archive(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_stop(label: str, env: dict[str, str]) -> None:
        events.append("stop")
        raise CandidateTerminationError("cannot confirm candidate environment termination")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", fail_stop)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "cannot confirm candidate environment termination"
    assert outcome.agent_failed
    assert events == ["stop", "remove", "control"]


# A host packaging failure blocks evaluation without reclassifying the agent run.
def test_packaging_failure_is_separate_from_agent_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_package(workspace: Path, manifest: object, archive: Path) -> None:
        events.append("archive")
        raise ValueError("invalid candidate path")

    monkeypatch.setattr(runtime, "package_workspace", fail_package)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "host submission packaging failed: invalid candidate path"
    assert not outcome.agent_failed
    assert events == ["stop", "remove", "control", "archive"]


# An execution exception still closes the candidate before propagating the bug.
def test_execution_exception_cleans_up(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_execute(context: AgentSandboxContext) -> CandidateExecution[str]:
        raise AssertionError("observer failed")

    with pytest.raises(AssertionError, match="observer failed"):
        run_candidate_lifecycle(
            prepare=lambda: _context(tmp_path),
            execute=fail_execute,
            manifest=object(),
            archive_path=tmp_path / "result.tar.gz",
        )
    assert events == ["stop", "remove", "control"]


# Active candidate containers are stopped and rechecked before archive access.
def test_stop_confirms_no_labeled_container_remains(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[list[str]] = []
    responses = iter(("candidate-id\n", "", ""))

    def fake_run(command: list[str], **kwargs):
        calls.append(command)
        return SimpleNamespace(stdout=next(responses), returncode=0)

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    runtime.stop_agent_sandbox_containers("controlled", {})
    assert calls[1] == ["docker", "stop", "candidate-id"]
    assert calls[2] == calls[0]


# A candidate still active after Docker stop produces a termination barrier failure.
def test_stop_rejects_remaining_container(monkeypatch: pytest.MonkeyPatch) -> None:
    responses = iter(("candidate-id\n", "", "candidate-id\n"))
    monkeypatch.setattr(
        runtime.subprocess,
        "run",
        lambda *args, **kwargs: SimpleNamespace(stdout=next(responses), returncode=0),
    )
    with pytest.raises(CandidateTerminationError, match="remain active"):
        runtime.stop_agent_sandbox_containers("controlled", {})


# Label-scoped cleanup must verify that only the worker's containers were removed.
def test_label_scoped_cleanup_rechecks_after_removing_worker_containers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[list[str]] = []

    def fake_run(argv: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        calls.append(argv)
        if argv[:3] == ["docker", "ps", "-aq"]:
            stdout = "worker-agent\nworker-evaluator\n" if len(calls) == 1 else ""
            return subprocess.CompletedProcess(argv, 0, stdout=stdout, stderr="")
        if argv[:3] == ["docker", "rm", "-f"]:
            return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")
        raise AssertionError(f"unexpected Docker command: {argv}")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)

    runtime.cleanup_agent_sandbox_containers("worker-label")

    assert calls == [
        ["docker", "ps", "-aq", "--filter", "label=dafnyutils.eval.run=worker-label"],
        ["docker", "rm", "-f", "worker-agent", "worker-evaluator"],
        ["docker", "ps", "-aq", "--filter", "label=dafnyutils.eval.run=worker-label"],
    ]


def _fake_docker_command(
    tmp_path: Path,
    *,
    fail_copy: bool,
    agent_exit_code: int = 7,
    failing_exit_hook: bool = False,
) -> subprocess.CompletedProcess[str]:
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    docker = fake_bin / "docker"
    docker.write_text(
        """#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$DOCKER_CALLS"
if [ "$1" = cp ] && [ "$FAIL_COPY" = 1 ]; then exit 17; fi
if [ "$1" = logs ]; then printf 'agent output\\n'; fi
if [ "$1" = wait ]; then printf '%s\\n' "$AGENT_EXIT_CODE"; fi
""",
        encoding="utf-8",
    )
    docker.chmod(0o755)
    command = build_docker_compose_agent_command(
        compose_files=(tmp_path / "compose.yaml",),
        service="agent-workflow",
        project_name="run-123",
        container_name="run-123-agent",
        staging_container_name="run-123-staging",
        workspace_dir=tmp_path / "workspace",
    )
    if failing_exit_hook:
        command = "trap 'false' EXIT; " + command
    return subprocess.run(
        ["bash", "-c", command],
        cwd=tmp_path,
        env={
            **os.environ,
            "PATH": f"{fake_bin}:{os.environ['PATH']}",
            "DOCKER_CALLS": str(tmp_path / "docker-calls"),
            "FAIL_COPY": "1" if fail_copy else "0",
            "AGENT_EXIT_CODE": str(agent_exit_code),
        },
        capture_output=True,
        text=True,
        check=False,
    )


# A generic launch spec renders its command, mounts, user, and permitted environment.
def test_launch_spec_renders_agent_service(tmp_path: Path) -> None:
    agent_plan = ContainerWorkspacePlan(
        service="agent-workflow",
        mounts=(),
        working_dir="/workspace",
        environment={},
    )
    output = tmp_path / "compose.yaml"
    write_compose_override(
        path=output,
        agent_plan=agent_plan,
        agent_environment={},
        agent_container_name="agent-test",
        staging_container_name="agent-test-staging",
        staged_workspace_dir=tmp_path / "public_workspace",
        agent_launch=AgentLaunchSpec(
            image="cosyn-evaluation:test",
            forwarded_secret_environment=("CODEX_API_KEY",),
            sandbox_profile=SandboxProfile.NESTED_USER_NAMESPACE,
        ),
        launch_command=(
            "./agent",
            "exec",
            "--prompt=Implement the task. Preserve 'quotes', $variables and\nnewlines.",
        ),
    )

    payload = yaml.safe_load(output.read_text(encoding="utf-8"))
    agent = payload["services"]["agent-workflow"]
    staging = payload["services"]["task-staging"]
    assert staging["image"] == "dafnyutils-task:latest"
    assert staging["volumes"][0]["read_only"] is False
    assert agent["image"] == "cosyn-evaluation:test"
    assert agent["user"] == "agent"
    assert agent["build"]["args"] == {
        "AGENT_UID": str(os.getuid()),
        "AGENT_GID": str(os.getgid()),
    }
    assert agent["working_dir"] == "/workspace"
    assert agent["command"][-3:] == [
        "./agent",
        "exec",
        "--prompt=Implement the task. Preserve 'quotes', $$variables and\nnewlines.",
    ]
    assert agent["security_opt"] == [
        "seccomp=unconfined",
        "apparmor=unconfined",
        "systempaths=unconfined",
    ]
    assert agent["environment"]["CODEX_API_KEY"] is None


# A copied public workspace reaches the agent only after create and preserves its exit code.
def test_agent_container_starts_after_copy_and_reports_exit_code(tmp_path: Path) -> None:
    result = _fake_docker_command(tmp_path, fail_copy=False)

    assert result.returncode == 7
    assert "agent output" in result.stdout
    calls = (tmp_path / "docker-calls").read_text(encoding="utf-8").splitlines()
    assert " create --no-build task-staging" in calls[0]
    assert "/workspace/. run-123-staging:/workspace/" in calls[1]
    assert calls[2] == "rm run-123-staging"
    assert " create --no-build agent-workflow" in calls[3]
    assert calls[4:] == [
        "start run-123-agent",
        "logs --follow run-123-agent",
        "wait run-123-agent",
    ]


# A failing caller-shell cleanup cannot turn normal candidate completion into failure.
def test_normal_agent_exit_survives_failing_shell_exit_hook(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=0, failing_exit_hook=True
    )

    assert result.returncode == 0
    assert "agent output" in result.stdout


# A failing caller-shell cleanup cannot replace the candidate's nonzero exit code.
def test_failed_agent_exit_survives_failing_shell_exit_hook(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=7, failing_exit_hook=True
    )

    assert result.returncode == 7
    assert "agent output" in result.stdout


# A failed public file copy stops before the candidate process starts.
def test_agent_container_never_starts_after_failed_copy(tmp_path: Path) -> None:
    result = _fake_docker_command(tmp_path, fail_copy=True)

    assert result.returncode == 17
    calls = (tmp_path / "docker-calls").read_text(encoding="utf-8").splitlines()
    assert len(calls) == 2
    assert calls[1].startswith("cp ")
