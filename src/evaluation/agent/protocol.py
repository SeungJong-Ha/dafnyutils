"""Benchmark-owned agent task/result wire and candidate layout."""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Self, TypeVar

from pydantic import Field, StrictInt, StrictStr, ValidationError, field_validator, model_validator

from benchmarks.task import (
    TaskModel,
    _TaskDefinition,
    is_path_within,
    require_unique,
    validate_id,
    validate_relative_path,
)

ProtocolValue = TypeVar("ProtocolValue", bound=TaskModel)


class AgentProtocolVersion(StrEnum):
    V1 = "benchmark.agent-protocol.v1"


class AgentTaskSchemaVersion(StrEnum):
    V2 = "benchmark.agent-task.v2"


class AgentResultSchemaVersion(StrEnum):
    V6 = "benchmark.agent-result.v6"


class AgentRunStatus(StrEnum):
    COMPLETED = "completed"
    FAILED = "failed"
    TIMED_OUT = "timed-out"
    TURN_BUDGET_EXHAUSTED = "turn-budget-exhausted"
    INVALID_TASK = "invalid-task"


class AgentArtifactKind(StrEnum):
    WORKSPACE_OUTPUT = "workspace-output"
    LOG = "log"
    REPORT = "report"
    SUBMISSION = "submission"


class AgentProtocolPayloadError(ValueError):
    """An agent task or result could not be read or parsed."""


def _read_protocol_file(cls: type[ProtocolValue], path: Path) -> ProtocolValue:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AgentProtocolPayloadError(f"failed to read protocol payload: {path}") from exc
    try:
        return cls.model_validate_json(raw)
    except ValidationError as exc:
        errors = exc.errors(include_input=False, include_url=False)
        details = "; ".join(
            f"{'.'.join(str(part) for part in error['loc']) or '<root>'}: "
            f"{error['msg']} [{error['type']}]"
            for error in errors
        )
        kind = (
            "invalid JSON syntax"
            if any(error["type"] == "json_invalid" for error in errors)
            else "invalid protocol payload"
        )
        raise AgentProtocolPayloadError(f"{kind}: {path}: {details}") from None


@dataclass(frozen=True)
class CandidateLayout:
    """Benchmark-owned absolute paths visible to a candidate container."""

    workspace_directory: str = "/workspace"
    task_directory: str = "/workspace/task"
    scratch_directory: str = "/workspace/.agent"
    run_directory: str = "/run"
    artifact_directory: str = "/run/agent_artifacts"
    bundle_directory: str = "/run/repo_agent"
    home_directory: str = "/run/agent_home"
    tmp_directory: str = "/tmp"
    task_filename: str = "task.json"
    task_markdown_filename: str = "task.md"
    result_filename: str = "agent-result.json"
    launcher_filename: str = "agent"

    @property
    def task_path(self) -> str:
        return str(Path(self.task_directory) / self.task_filename)

    @property
    def task_markdown_path(self) -> str:
        return str(Path(self.task_directory) / self.task_markdown_filename)

    @property
    def result_path(self) -> str:
        return str(Path(self.run_directory) / self.result_filename)

    @property
    def launcher_path(self) -> str:
        return str(Path(self.workspace_directory) / self.launcher_filename)


def agent_command(prompt: str, layout: CandidateLayout = CandidateLayout()) -> tuple[str, ...]:
    if not prompt.strip() or "\x00" in prompt:
        raise ValueError("agent prompt must be nonempty and NUL-free")
    return (f"./{layout.launcher_filename}", "exec", f"--prompt={prompt}")


class SubmissionPolicy(TaskModel):
    roots: tuple[StrictStr, ...]
    excluded_names: tuple[StrictStr, ...] = ()
    excluded_paths: tuple[StrictStr, ...] = ()

    @field_validator("roots", "excluded_paths")
    @classmethod
    def _paths(cls, value: tuple[str, ...]) -> tuple[str, ...]:
        return require_unique(
            tuple(validate_relative_path(path, label="submission path") for path in value),
            label="submission paths",
        )

    @field_validator("excluded_names")
    @classmethod
    def _names(cls, value: tuple[str, ...]) -> tuple[str, ...]:
        for name in value:
            validate_relative_path(name, label="excluded name")
            if "/" in name:
                raise ValueError("excluded names must be single path components")
        return require_unique(value, label="excluded names")

    @model_validator(mode="after")
    def _roots(self) -> Self:
        if not self.roots:
            raise ValueError("submission roots must not be empty")
        if any(
            is_path_within(left, right)
            for left in self.roots
            for right in self.roots
            if left != right
        ):
            raise ValueError("submission roots must not overlap")
        if any(
            any(part in self.excluded_names for part in Path(root).parts)
            or any(is_path_within(root, excluded) for excluded in self.excluded_paths)
            for root in self.roots
        ):
            raise ValueError("submission roots must not be excluded")
        return self


class AgentTaskPayload(_TaskDefinition):
    schema_version: AgentTaskSchemaVersion = Field()
    submission: SubmissionPolicy | None = None

    @classmethod
    def from_json_file(cls, path: Path) -> Self:
        return _read_protocol_file(cls, path)

    @model_validator(mode="after")
    def _submission_outputs(self) -> Self:
        if self.submission is None:
            return self
        for output in self.workspace.required_outputs:
            if not any(is_path_within(output.path, root) for root in self.submission.roots):
                raise ValueError("required output must be within a submission root")
            if any(
                part in self.submission.excluded_names for part in Path(output.path).parts
            ) or any(
                is_path_within(output.path, excluded) for excluded in self.submission.excluded_paths
            ):
                raise ValueError("required output must not be excluded from submission")
        return self


class PromptConsumptionRecord(TaskModel):
    resource_ids: tuple[StrictStr, ...]
    public_rule_ids: tuple[StrictStr, ...]
    public_check_ids: tuple[StrictStr, ...]

    @field_validator("resource_ids", "public_rule_ids", "public_check_ids")
    @classmethod
    def _ids(cls, value: tuple[str, ...], info: object) -> tuple[str, ...]:
        name = getattr(info, "field_name", "identifiers")
        for item in value:
            validate_id(item, label=name)
        return require_unique(value, label=name)


class TokenUsage(TaskModel):
    input_tokens: StrictInt
    output_tokens: StrictInt
    cached_input_tokens: StrictInt | None = None

    @field_validator("input_tokens", "output_tokens", "cached_input_tokens")
    @classmethod
    def _nonnegative(cls, value: int | None) -> int | None:
        if value is not None and value < 0:
            raise ValueError("token counts must be nonnegative")
        return value


class TurnUsage(TaskModel):
    used_turns: StrictInt
    max_turns: StrictInt

    @model_validator(mode="after")
    def _usage(self) -> Self:
        if self.max_turns <= 0:
            raise ValueError("max_turns must be positive")
        if self.used_turns < 0 or self.used_turns > self.max_turns:
            raise ValueError("used_turns must be between zero and max_turns")
        return self


class AgentArtifact(TaskModel):
    artifact_id: StrictStr
    kind: AgentArtifactKind
    path: StrictStr
    sha256: StrictStr | None = None

    @field_validator("artifact_id")
    @classmethod
    def _id(cls, value: str) -> str:
        return validate_id(value, label="artifact_id")

    @field_validator("path")
    @classmethod
    def _path(cls, value: str) -> str:
        return validate_relative_path(value, label="artifact path")

    @field_validator("sha256")
    @classmethod
    def _digest(cls, value: str | None) -> str | None:
        if value is not None and re.fullmatch(r"[0-9a-f]{64}", value) is None:
            raise ValueError("sha256 must be a lowercase SHA-256 digest")
        return value


class AgentReport(TaskModel):
    schema_version: AgentResultSchemaVersion
    run_id: StrictStr
    comparison_id: StrictStr
    task_id: StrictStr
    agent_id: StrictStr
    backend_id: StrictStr
    status: AgentRunStatus
    exit_code: StrictInt
    message: StrictStr | None
    duration_ms: StrictInt
    prompt_consumption: PromptConsumptionRecord
    token_usage: TokenUsage | None
    turn_usage: TurnUsage
    artifacts: tuple[AgentArtifact, ...]

    @classmethod
    def from_json_file(cls, path: Path) -> Self:
        return _read_protocol_file(cls, path)

    @field_validator("run_id", "comparison_id", "task_id", "agent_id", "backend_id")
    @classmethod
    def _ids(cls, value: str, info: object) -> str:
        return validate_id(value, label=getattr(info, "field_name", "identifier"))

    @field_validator("duration_ms")
    @classmethod
    def _duration(cls, value: int) -> int:
        if value < 0:
            raise ValueError("duration_ms must be nonnegative")
        return value

    @model_validator(mode="after")
    def _result(self) -> Self:
        if self.status is AgentRunStatus.COMPLETED and self.exit_code != 0:
            raise ValueError("completed results must use exit_code 0")
        if self.status is not AgentRunStatus.COMPLETED and self.exit_code == 0:
            raise ValueError("non-completed results must use a nonzero exit_code")
        if self.status is not AgentRunStatus.COMPLETED and (
            self.message is None or not self.message.strip()
        ):
            raise ValueError("non-completed results must explain the failure")
        if (
            self.status is AgentRunStatus.TURN_BUDGET_EXHAUSTED
            and self.turn_usage.used_turns != self.turn_usage.max_turns
        ):
            raise ValueError("turn-budget-exhausted results must use the full turn budget")
        require_unique(tuple(item.artifact_id for item in self.artifacts), label="artifact_ids")
        return self
