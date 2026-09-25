"""Validate benchmark-owned fields of an agent report and its artifacts."""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from pathlib import Path

from evaluation.agent.protocol import (
    AgentArtifactKind,
    AgentReport,
    AgentRunStatus,
    AgentTaskPayload,
)


def validate_agent_report(
    *,
    report: AgentReport,
    task: AgentTaskPayload,
    expected_identity: Mapping[str, str],
    exit_code: int | None,
    timed_out: bool,
    workspace_dir: Path,
    run_dir: Path,
    artifact_directory: Path,
) -> str | None:
    """Return the first protocol error, preserving the existing public messages."""
    identity_fields = ("run_id", "comparison_id", "task_id", "agent_id", "backend_id")
    mismatches = [
        name for name in identity_fields if getattr(report, name) != expected_identity[name]
    ]
    if mismatches:
        return "agent protocol identity mismatch: " + ", ".join(mismatches)
    expected = (
        frozenset(resource.resource_id for resource in task.resources),
        frozenset(rule.rule_id for rule in task.public_rules),
        frozenset(check.check_id for check in task.public_checks),
    )
    actual = (
        frozenset(report.prompt_consumption.resource_ids),
        frozenset(report.prompt_consumption.public_rule_ids),
        frozenset(report.prompt_consumption.public_check_ids),
    )
    empty = (frozenset(), frozenset(), frozenset())
    if report.status is AgentRunStatus.COMPLETED and actual != expected:
        return "agent result does not record complete public task consumption"
    if report.status in {
        AgentRunStatus.FAILED,
        AgentRunStatus.TIMED_OUT,
        AgentRunStatus.TURN_BUDGET_EXHAUSTED,
    } and actual not in {empty, expected}:
        return "agent result records partial public task consumption"
    if report.status is AgentRunStatus.INVALID_TASK and actual != empty:
        return "invalid-task agent result records public task consumption"
    if not timed_out and report.exit_code != exit_code:
        return (
            "agent result exit_code does not match container exit status: "
            f"{report.exit_code} != {exit_code}"
        )
    return _validate_result_artifacts(report, workspace_dir, run_dir, artifact_directory)


def _validate_result_artifacts(
    report: AgentReport, workspace_dir: Path, run_dir: Path, artifact_directory: Path
) -> str | None:
    for artifact in report.artifacts:
        relative = Path(artifact.path)
        if artifact.kind is AgentArtifactKind.WORKSPACE_OUTPUT:
            root = workspace_dir
        elif relative.parts and relative.parts[0] == "agent_artifacts":
            root = artifact_directory.parent
        else:
            root = run_dir
        path = root / relative
        if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
            return f"agent result artifact escapes its declared root: {artifact.path}"
        if not path.is_file():
            return f"agent result artifact is missing: {artifact.path}"
        if artifact.sha256 is not None:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if digest != artifact.sha256:
                return f"agent result artifact digest mismatch: {artifact.path}"
    return None


def normal_termination_detail(
    *, execution_present: bool, exit_code: int | None, timed_out: bool, protocol_error: str | None
) -> str | None:
    """Explain why a candidate invocation cannot be accepted as a normal exit."""
    if not execution_present:
        return "agent command was not run"
    if timed_out:
        return "timed out"
    if exit_code is None or exit_code != 0:
        return f"exit code {exit_code}"
    return protocol_error
