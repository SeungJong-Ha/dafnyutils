# Benchmark agent protocol v1

Dafnyutils defines the task delivered to an agent, the report received from it,
candidate filesystem layout, container lifecycle, host-side workspace collection,
and acceptance rules.
`AgentProtocolVersion.V1` identifies this contract. The JSON payload versions are
`benchmark.agent-task.v2` and `benchmark.agent-result.v6`. Any incompatible wire
change must bump the corresponding version and update conformance tests in the
integration repository and Cosyn.

`evaluation.agent.protocol.AgentTaskPayload` contains the validated public task
profile plus `submission`, the task roots and archive exclusions from the public
release manifest. The released `tasks/<task-id>/task.json` is a fixed file; agent
delivery writes a separate payload and a public `task.md` guide to
`/workspace/task`, and copies only manifest-declared public resources beneath it.
Each copy is read without following links and checked against the manifest hash.
Delivery never rewrites the release. The `submission` field tells the receiver
which workspace roots to collect. Agents do not package an archive.

`evaluation.agent.protocol.AgentReport` is the `benchmark.agent-result.v6` JSON
contract. It records run, comparison, task, agent and backend identity labels;
status, exit code, timing and turn/token usage; public resource/rule/check
consumption; and optional artifacts. Identity labels are opaque strings to the
benchmark. The `submission` artifact kind remains readable for historical
reports, but new agents do not emit it. Cosyn defines the separate invocation
wire and validates invocation-specific consistency.

The default `CandidateLayout` mounts a public workspace at `/workspace`, the
agent task at `/workspace/task` read-only and model scratch at
`/workspace/.agent` writable. Temporary and tool cache paths used by model-side
commands live under that scratch directory. The launcher is `/workspace/agent`; the agent runs from
`/workspace` using `./agent exec --prompt=<prompt>`. Candidate editable paths
are writable bind mounts. Public task and fixed inputs are read-only mounts.
The private run directory, artifact directory, runtime bundle, home and temporary
directory remain outside the model's permitted file view, while the harness may
execute tools from them. The evaluator's oracle executable is blocked by the candidate
mount plan. Dafnyutils owns container staging, Compose rendering, candidate
termination and cleanup. The integration supplies image/provider configuration,
the conforming launcher and command observation callbacks. Dafnyutils imports
neither a harness nor the integration package.

The benchmark lifecycle owns the sequence from preparation through execution,
confirmed container termination and host collection. A preparation failure,
timeout, nonzero exit, invalid report or unconfirmed termination prevents
collection. Diagnostic retention never retains running candidate containers.
After normal agent exit and confirmed container termination, this lifecycle calls
`evaluation.submission.archive.package_workspace(workspace, manifest, archive)`.
It packages declared roots without following links, rejects hard links and
special entries, excludes names and paths declared in the manifest, and commits
the archive atomically. Traversal is iterative. The unchanged
`receive_submission` validates archive limits, released fixed-file hashes and
required outputs before evaluator checks. A missing required output therefore
causes a receiver error, `required outputs missing`, even if the agent report
said `completed`.

The integration consumes the lifecycle result to report failures and pass the
archive to `evaluate_submission`; it does not implement a separate termination or
collection gate. Batch cancellation can call the same label-scoped cleanup helper.
This ownership change preserves protocol v1, task v2, report v6 and archive policy.

The Python entry point is `evaluation.agent.runtime.run_candidate_lifecycle`.
Its `prepare` callback returns an `AgentSandboxContext`; integrations use
`prepare_agent_sandbox_context` to construct it from a verified release, a base
Compose file, `CandidateRunContext`, environment and harness preparation callback.
The latter receives `AgentPreparationContext` and returns `AgentLaunchSpec` with
the selected image, environment and sandbox profile. A launch-record callback
observes the benchmark-generated argv and prompt before any container starts.

The `execute` callback receives the prepared context and returns
`CandidateExecution[T]`: execution presence, exit code, timeout, protocol error and
an opaque integration payload. Integrations may record logs, events and harness
consistency checks there. The lifecycle always attempts candidate shutdown and
cleanup after execution, including exceptions. It returns
`CandidateLifecycleOutcome[T]` with the context, execution, failure reason and
structured `agent_failed` status, so callers do not classify failures by parsing
messages. Host packaging failure is distinguishable from agent execution failure.
Unexpected execution exceptions propagate after cleanup; they do not collect an
archive. The caller supplies `manifest` and a host-only `archive_path`.

The integration repository composes this protocol with a harness such as Cosyn.
Neither Dafnyutils nor Cosyn imports the other. Local checks use controlled
filesystems and fake providers; a passing local check is not a paid experiment
or a Dafny proof result.
