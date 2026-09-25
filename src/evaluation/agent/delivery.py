"""Write a benchmark agent task without changing the released public task."""

from __future__ import annotations

import hashlib
import json
import os
import shlex
import stat
import tempfile
from pathlib import Path

from evaluation.agent.protocol import AgentTaskPayload, AgentTaskSchemaVersion, CandidateLayout
from evaluation.task.release import PreparedReleaseTask, TaskReleaseManifest


def write_agent_task(
    prepared: PreparedReleaseTask, manifest: TaskReleaseManifest, directory: Path
) -> AgentTaskPayload:
    """Project the validated public profile into a private agent delivery directory."""
    released = manifest.tasks[prepared.task_id]
    payload = AgentTaskPayload.model_validate_json(
        json.dumps(
            {
                **released.profile.model_dump(mode="json", exclude={"schema_version"}),
                "schema_version": AgentTaskSchemaVersion.V2,
                "submission": {
                    "roots": manifest.task_roots,
                    "excluded_names": manifest.excluded_names,
                    "excluded_paths": manifest.excluded_paths,
                },
            }
        )
    )
    public_workspace = prepared.workspace.resolve()
    if directory.absolute().is_relative_to(public_workspace) or directory.resolve().is_relative_to(
        public_workspace
    ):
        raise ValueError("agent delivery directory must be separate from the public task")
    directory.parent.mkdir(parents=True, exist_ok=True)
    if directory.exists() or directory.is_symlink():
        raise FileExistsError(directory)
    with tempfile.TemporaryDirectory(prefix=f".{directory.name}-", dir=directory.parent) as temp:
        staged = Path(temp) / directory.name
        staged.mkdir()
        payload.to_json_file(staged / CandidateLayout().task_filename)
        (staged / CandidateLayout().task_markdown_filename).write_text(
            _task_markdown(payload), encoding="utf-8"
        )
        for resource in payload.resources:
            if resource.path not in manifest.files:
                raise ValueError(
                    f"agent task resource is not in the public release: {resource.path}"
                )
            relative = Path(resource.path)
            if relative.parts[0] in {"task.json", "task.md"}:
                raise ValueError(
                    f"task resource conflicts with reserved task file: {resource.path}"
                )
            target = staged / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            _copy_public_resource(
                prepared.workspace, resource.path, target, manifest.files[resource.path]
            )
        staged.rename(directory)
    return payload


def agent_prompt(payload: AgentTaskPayload, layout: CandidateLayout = CandidateLayout()) -> str:
    return (
        f"Complete {payload.title} ({payload.task_id}) according to the public task contract "
        f"in {layout.task_markdown_path} and structured contract in {layout.task_path}. "
        "Implement the required outputs and satisfy its public rules and checks."
    )


def _copy_public_resource(workspace: Path, path: str, target: Path, expected_digest: str) -> None:
    if workspace.is_symlink():
        raise ValueError("public task workspace must not be a symlink")
    directory_fd = os.open(workspace, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        parts = Path(path).parts
        for part in parts[:-1]:
            next_fd = os.open(
                part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd
            )
            os.close(directory_fd)
            directory_fd = next_fd
        file_fd = os.open(
            parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory_fd
        )
        with os.fdopen(file_fd, "rb") as source, target.open("xb") as output:
            metadata = os.fstat(source.fileno())
            if not stat.S_ISREG(metadata.st_mode):
                raise ValueError(f"public task resource is not a regular file: {path}")
            digest = hashlib.sha256()
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(chunk)
                output.write(chunk)
            if digest.hexdigest() != expected_digest:
                raise ValueError(f"public task resource integrity mismatch: {path}")
            target.chmod(stat.S_IMODE(metadata.st_mode))
    finally:
        os.close(directory_fd)


def _task_markdown(payload: AgentTaskPayload) -> str:
    lines = [
        f"# {payload.title}",
        "",
        f"Task ID: `{payload.task_id}`",
        "",
        "The structured contract is `task.json` in this directory. "
        "Public resource paths below are relative to this directory.",
        "",
        "Model-visible data files are limited to `/workspace`. This task directory "
        "(`/workspace/task`) is read-only. Write final required outputs at their "
        "declared paths relative to `/workspace`. Use `/workspace/.agent` for scratch "
        "files. Private runner configuration and logs are outside the model's file "
        "view. Installed system tools may be executed.",
        "",
        "## Public resources",
        "",
    ]
    lines.extend(f"- `{resource.path}` — {resource.description}" for resource in payload.resources)
    lines.extend(["", "## Required outputs", ""])
    lines.extend(
        f"- `{output.path}` ({output.kind.value}, {output.role})"
        for output in payload.workspace.required_outputs
    )
    lines.extend(["", "## Public rules", ""])
    lines.extend(f"- {rule.title}: {rule.description}" for rule in payload.public_rules)
    lines.extend(["", "## Public checks", ""])
    lines.extend(
        f"- {check.title}: `{shlex.join(check.argv)}`"
        + (f" (from `{check.working_directory}`)" if check.working_directory else "")
        for check in payload.public_checks
    )
    lines.extend(
        [
            "",
            "Use the editable workspace paths declared in `task.json` to implement the outputs.",
            "",
        ]
    )
    return "\n".join(lines)
