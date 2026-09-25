"""Benchmark agent wire, delivery, report, and candidate isolation contracts."""

from __future__ import annotations

import hashlib
import json
import shutil
from dataclasses import replace
from pathlib import Path

import pytest
from pydantic import ValidationError

from evaluation.agent.container import candidate_container_plan
from evaluation.agent.delivery import agent_prompt, write_agent_task
from evaluation.agent.protocol import (
    AgentArtifact,
    AgentArtifactKind,
    AgentProtocolPayloadError,
    AgentReport,
    AgentResultSchemaVersion,
    AgentRunStatus,
    AgentTaskPayload,
    CandidateLayout,
    PromptConsumptionRecord,
    TurnUsage,
    agent_command,
)
from evaluation.agent.report import normal_termination_detail, validate_agent_report
from evaluation.enums import MountMode
from evaluation.task.release import prepare_release, publish_release
from evaluation.task.workspace import WorkspaceRoots


@pytest.fixture(scope="module")
def public_release(tmp_path_factory: pytest.TempPathFactory):
    root = tmp_path_factory.mktemp("agent-public-release")
    manifest = publish_release(("true",), root / "release")
    prepared = prepare_release(root / "release", root / "workspace")
    return manifest, prepared.tasks["true"]


def _report(task: AgentTaskPayload, resource_ids: tuple[str, ...]) -> AgentReport:
    return AgentReport(
        schema_version=AgentResultSchemaVersion.V6,
        run_id="run-1",
        comparison_id="direct",
        task_id=task.task_id,
        agent_id="codex",
        backend_id="codex",
        status=AgentRunStatus.COMPLETED,
        exit_code=0,
        message=None,
        duration_ms=1,
        prompt_consumption=PromptConsumptionRecord(
            resource_ids=resource_ids,
            public_rule_ids=tuple(rule.rule_id for rule in task.public_rules),
            public_check_ids=tuple(check.check_id for check in task.public_checks),
        ),
        token_usage=None,
        turn_usage=TurnUsage(used_turns=1, max_turns=4),
        artifacts=(),
    )


def _validate(report: AgentReport, task: AgentTaskPayload, tmp_path: Path) -> str | None:
    return validate_agent_report(
        report=report,
        task=task,
        expected_identity={
            "run_id": "run-1",
            "comparison_id": "direct",
            "task_id": task.task_id,
            "agent_id": "codex",
            "backend_id": "codex",
        },
        exit_code=0,
        timed_out=False,
        workspace_dir=tmp_path / "workspace",
        run_dir=tmp_path,
        artifact_directory=tmp_path / "agent_artifacts",
    )


# Delivery preserves the fixed release bytes and projects the complete public contract.
def test_delivery_preserves_release(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    original = prepared.input_layout.task_path.read_bytes()
    payload = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    assert prepared.input_layout.task_path.read_bytes() == original
    assert hashlib.sha256(original).hexdigest() == manifest.fixed_files["tasks/true/task.json"]
    assert AgentTaskPayload.from_json_file(tmp_path / "agent-task/task.json") == payload
    assert (tmp_path / "agent-task/task.md").is_file()
    for resource in payload.resources:
        assert (tmp_path / "agent-task" / resource.path).read_bytes() == (
            prepared.workspace / resource.path
        ).read_bytes()
    assert payload.submission is not None
    assert payload.submission.roots == manifest.task_roots
    assert payload.submission.excluded_names == manifest.excluded_names
    assert payload.submission.excluded_paths == manifest.excluded_paths
    released = manifest.tasks["true"].profile.model_dump(mode="json", exclude={"schema_version"})
    actual = json.loads((tmp_path / "agent-task/task.json").read_text(encoding="utf-8"))
    assert {
        key: value for key, value in actual.items() if key not in {"schema_version", "submission"}
    } == released


# Agent task delivery cannot replace the published task directory.
def test_delivery_rejects_public_directory(public_release) -> None:
    manifest, prepared = public_release
    with pytest.raises(ValueError, match="separate"):
        write_agent_task(prepared, manifest, prepared.input_layout.task_dir)


# Delivery rejects a public resource replaced by a symlink before reading it.
def test_delivery_rejects_linked_resource(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    workspace = tmp_path / "workspace"
    shutil.copytree(prepared.workspace, workspace)
    linked = replace(prepared, workspace=workspace)
    resource_path = Path(manifest.tasks["true"].profile.resources[0].path)
    source = workspace / resource_path
    source.unlink()
    source.symlink_to(tmp_path / "outside")
    with pytest.raises(OSError):
        write_agent_task(linked, manifest, tmp_path / "agent-task")
    assert not (tmp_path / "agent-task").exists()


# The launcher command uses the benchmark's candidate layout and a nonempty prompt.
def test_agent_command_layout(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    payload = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    layout = CandidateLayout()
    prompt = agent_prompt(payload, layout)
    assert agent_command(prompt, layout) == ("./agent", "exec", f"--prompt={prompt}")
    assert layout.task_path == "/workspace/task/task.json"
    assert layout.task_markdown_path == "/workspace/task/task.md"
    assert layout.result_path == "/run/agent-result.json"


# An invalid agent task schema is rejected when the payload is read.
def test_agent_task_rejects_schema(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    payload = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    malformed = payload.model_dump(mode="json")
    malformed["schema_version"] = "benchmark.agent-task.v1"
    with pytest.raises(ValidationError):
        AgentTaskPayload.model_validate(malformed)


# Agent task resource paths cannot escape the delivered task directory.
def test_agent_task_rejects_resource_traversal(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    payload = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    malformed = payload.model_dump(mode="json")
    malformed["resources"][0]["path"] = "../private"
    with pytest.raises(ValidationError):
        AgentTaskPayload.model_validate_json(json.dumps(malformed))


# A blank launcher prompt cannot form a valid agent command.
def test_agent_command_rejects_blank_prompt() -> None:
    with pytest.raises(ValueError, match="nonempty"):
        agent_command("   ")


# A malformed result file reports a protocol parsing error at the file boundary.
def test_agent_report_rejects_invalid_json(tmp_path: Path) -> None:
    path = tmp_path / "agent-result.json"
    path.write_text("{", encoding="utf-8")
    with pytest.raises(AgentProtocolPayloadError, match="invalid JSON syntax"):
        AgentReport.from_json_file(path)


# Benchmark identity labels remain opaque to allow independent harnesses.
def test_agent_report_accepts_opaque_identity(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    opaque = report.model_copy(update={"agent_id": "solver-a", "backend_id": "provider-b"})
    assert AgentReport.model_validate_json(opaque.model_dump_json()) == opaque


# Completion accounts for every public resource, including support resources.
def test_completed_report_records_all_resources(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    assert _validate(report, task, tmp_path) is None


# A successful process cannot hide an omitted public resource in its consumption record.
def test_completed_report_rejects_partial_consumption(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, ())
    assert _validate(report, task, tmp_path) == (
        "agent result does not record complete public task consumption"
    )


# A failed report may record no consumption or the complete contract, never a subset.
def test_failed_report_rejects_partial_consumption(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    assert len(task.resources) > 1
    report = _report(task, (task.resources[0].resource_id,))
    report = report.model_copy(
        update={"status": AgentRunStatus.FAILED, "exit_code": 1, "message": "failed"}
    )
    assert (
        _validate(report, task, tmp_path) == "agent result records partial public task consumption"
    )


# An invalid-task report cannot claim it consumed a public resource.
def test_invalid_task_rejects_consumption(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    report = report.model_copy(
        update={"status": AgentRunStatus.INVALID_TASK, "exit_code": 1, "message": "invalid"}
    )
    assert _validate(report, task, tmp_path) == (
        "invalid-task agent result records public task consumption"
    )


# A report's declared identity must match the invocation labels passed by the root.
def test_report_rejects_identity_mismatch(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    changed = report.model_copy(update={"comparison_id": "other"})
    assert _validate(changed, task, tmp_path) == "agent protocol identity mismatch: comparison_id"


# The report exit code must match the observed container exit status.
def test_report_rejects_exit_mismatch(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    error = validate_agent_report(
        report=report,
        task=task,
        expected_identity={
            "run_id": "run-1",
            "comparison_id": "direct",
            "task_id": task.task_id,
            "agent_id": "codex",
            "backend_id": "codex",
        },
        exit_code=7,
        timed_out=False,
        workspace_dir=tmp_path / "workspace",
        run_dir=tmp_path,
        artifact_directory=tmp_path / "agent_artifacts",
    )
    assert error == "agent result exit_code does not match container exit status: 0 != 7"


# Artifact digest checking rejects a changed candidate file.
def test_report_rejects_artifact_digest_mismatch(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / "result.txt").write_text("changed", encoding="utf-8")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    report = report.model_copy(
        update={
            "artifacts": (
                AgentArtifact(
                    artifact_id="result",
                    kind=AgentArtifactKind.WORKSPACE_OUTPUT,
                    path="result.txt",
                    sha256="0" * 64,
                ),
            )
        }
    )
    assert _validate(report, task, tmp_path) == "agent result artifact digest mismatch: result.txt"


# A report artifact must exist in its declared root.
def test_report_rejects_missing_artifact(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    report = report.model_copy(
        update={
            "artifacts": (
                AgentArtifact(
                    artifact_id="missing",
                    kind=AgentArtifactKind.WORKSPACE_OUTPUT,
                    path="missing.txt",
                ),
            )
        }
    )
    assert _validate(report, task, tmp_path) == "agent result artifact is missing: missing.txt"


# A linked artifact cannot redirect the report reader outside the declared root.
def test_report_rejects_linked_artifact(public_release, tmp_path: Path) -> None:
    manifest, prepared = public_release
    task = write_agent_task(prepared, manifest, tmp_path / "agent-task")
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / "linked.txt").symlink_to(tmp_path / "outside")
    report = _report(task, tuple(resource.resource_id for resource in task.resources))
    report = report.model_copy(
        update={
            "artifacts": (
                AgentArtifact(
                    artifact_id="linked", kind=AgentArtifactKind.WORKSPACE_OUTPUT, path="linked.txt"
                ),
            )
        }
    )
    assert _validate(report, task, tmp_path) == (
        "agent result artifact escapes its declared root: linked.txt"
    )


# Candidate mounts expose writable outputs and read-only public task and bundle paths.
def test_candidate_container_plan(public_release, tmp_path: Path) -> None:
    _, prepared = public_release
    staged = tmp_path / "staged"
    staged.mkdir()
    task = tmp_path / "task"
    task.mkdir()
    roots = WorkspaceRoots(
        sandbox_root=tmp_path,
        workspace_root=prepared.workspace,
        task_root=task,
        run_root=tmp_path / "run",
        oracle_target_root=prepared.workspace,
        candidate_output_root=tmp_path / "run/candidate_outputs",
    )
    plan = candidate_container_plan(
        roots=roots,
        task_spec=prepared.workspace_spec,
        agent_artifact_dir=tmp_path / "run/agent_artifacts",
        agent_home_dir=tmp_path / "home",
        agent_tmp_dir=tmp_path / "tmp",
        model_workspace_dir=tmp_path / "model-workspace",
        launcher_root=tmp_path / "bundle",
        staged_workspace_dir=staged,
    )
    mounts = {mount.target: mount for mount in plan.mounts}
    assert mounts["/workspace/task"].mode is MountMode.READ_ONLY
    assert mounts["/workspace/.agent"].mode is MountMode.READ_WRITE
    assert mounts["/run/repo_agent"].mode is MountMode.READ_ONLY
    assert mounts["/workspace/agent"].mode is MountMode.READ_ONLY
    for path in prepared.workspace_spec.editable_paths:
        assert mounts[f"/workspace/{path}"].mode is MountMode.READ_WRITE
    assert (staged / "agent").is_file()
    assert (staged / "task").is_dir()
    assert (staged / ".agent").is_dir()
    assert (tmp_path / "model-workspace/tmp/dotnet-cli-home").is_dir()
    assert (tmp_path / "model-workspace/cache/npm").is_dir()
    assert plan.environment == {
        "HOME": "/run/agent_home",
        "PWD": "/workspace",
        "TMPDIR": "/workspace/.agent/tmp",
        "DOTNET_CLI_HOME": "/workspace/.agent/tmp/dotnet-cli-home",
        "NPM_CONFIG_CACHE": "/workspace/.agent/cache/npm",
    }


# Normal termination errors preserve the run report's established messages.
def test_normal_termination_detail() -> None:
    assert (
        normal_termination_detail(
            execution_present=False, exit_code=None, timed_out=False, protocol_error=None
        )
        == "agent command was not run"
    )
