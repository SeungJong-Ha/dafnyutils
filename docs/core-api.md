# Use the trusted core API

Use `bench/core` to describe and perform a utility's IO under explicit library contracts. A utility proof establishes behavior under those contracts; it does not prove libc, gnulib, or the C/C# adapters correct.

## Contents

- [Setup and module map](#setup-and-module-map)
- [Copy stdin with explicit error results](#copy-stdin-with-explicit-error-results)
- [Entry and CLI contract](#entry-and-cli-contract)
- [Values and observations](#values-and-observations)
- [Streams](#streams)
- [Diagnostics and process context](#diagnostics-and-process-context)
- [Paths and metadata](#paths-and-metadata)
- [Filesystem effects](#filesystem-effects)
- [Timestamps](#timestamps)
- [Directory iteration](#directory-iteration)
- [CLI and pure helpers](#cli-and-pure-helpers)
- [Trust limits and API changes](#trust-limits-and-api-changes)

## Setup and module map

Use the [setup guide](../README.md#setup). There is no separate core package. Run examples from `/workspace/dafnyutils` with `dafny-benchmark` on `PATH`.

| Source | Responsibility |
| --- | --- |
| [World.dfy](../bench/core/World.dfy) | `BenchWorld`: bytes, paths, results, filesystem values and typed library observations |
| [IOContract.dfy](../bench/core/IOContract.dfy) | Named API postconditions and mathematical IO relations |
| [IO.dfy](../bench/core/IO.dfy) | `BenchIO.IO`: public effect boundary, ghost observations, process handle and exit |
| [BenchmarkItem.dfy](../bench/core/BenchmarkItem.dfy) | Shared parse/decode/run shell |
| [CliTypes.dfy](../bench/core/CliTypes.dfy), [CliModel.dfy](../bench/core/CliModel.dfy), [CliExtern.dfy](../bench/core/CliExtern.dfy) | CLI vocabulary, parser semantics and executable wrappers |
| [Utf8.dfy](../bench/core/Utf8.dfy), [Functional.dfy](../bench/core/Functional.dfy) | Text encoding, sequence functions and reusable proof helpers |
| [SecurityModel.dfy](../bench/core/SecurityModel.dfy) | Modeled credentials and filesystem access relations |
| [IOExtern.cs](../bench/core/IOExtern.cs), [IOStartup.c](../bench/core/IOStartup.c), [TouchTimeParser.c](../bench/core/TouchTimeParser.c) | Maintainer-owned native/managed runtime and pinned date parser |

The five `World*Proof.dfy` modules own lookup, insertion, removal, rename and filesystem update lemmas. Include the required proof file and import its module explicitly; for example, use `WorldFileSystemProof.FsSetPathIsInodeFsUpdateNode`. `BenchWorld` does not import those proofs.

`Std.*` is disabled in benchmark projects. Reuse `BenchFunctional` for maps,
filters, scans and folds, or write a verified task-local helper. Evaluated
candidates may use only the support files included by their generated task;
having a file in this checkout does not grant access to it.

## Copy stdin with explicit error results

The checked-in [StreamCopy client](../tools/fixtures/contributor/StreamCopy.dfy)
copies the consumed input prefix and returns both errors so a caller can choose
the right exit policy. Its implementation is shown below; the checked-in file
uses a relative include path so it also works in other checkout locations.

```dafny
include "/workspace/dafnyutils/bench/core/IO.dfy"

module StreamCopy {
  import BenchIO
  import BW = BenchWorld

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures readErr == 0 && writeErr == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin())
  {
    var data;
    data, readErr := io.ReadStdin(BW.ReturnError);
    var committed;
    committed, writeErr := io.WriteStdout(data, BW.ReturnError);
  }

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var readErr, writeErr := CopyInput(BenchIO.Process());
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }
}
```

`old(io.stdout())` is needed here because stdout changes. Other state is preserved by the frame; do not restate its invariance as extra equalities. `Process()` returns the existing handle. Ghost observers describe state for proofs and cannot be used as executable reads.

```sh
# Expected duration: Estimated 1–10 sec for this small client after tool installation.
# Success criteria: Exit 0 and zero verification errors.
dafny-benchmark verify --standard-libraries:false tools/fixtures/contributor/StreamCopy.dfy
```

This verifies only the client contract. It does not compile/link the native adapter,
establish GNU `cat` parity, or implement GNU error messages. Expected summary:

```text
Dafny program verifier finished with 4 verified, 0 errors
```

For a complete program using these calls, follow the
[small IO example](../README.md#example-test-and-verify-a-small-program). It adds a specification for partial
results, the exit policy, a separate proof, an executable build and error tests.

## Entry and CLI contract

Assemble a utility with `BenchItem.BenchmarkItemTwostate<CmdRaw>`. Its hooks provide `Name`, `Schema`, `ParseConfig`, `Decode`, `FormatParseError`, `PlanParsed`, `PlanParseFailure`, `PlanArgv` and `RunCore`.

`BenchItem.RunMain(item, argv, io)` selects a plan, calls `RunCore` for `CliRun(raw)`, and emits the planned bytes and exit status for `CliEarlyExit`. The utility's `RunCore` directly ensures `Spec(raw, io, exit)`. A proof of a helper summary is insufficient by itself. Test early-exit behavior too: for example, `true` and `false` preserve the original argument count when recognizing help/version.

Keep fixed diagnostic text in Spec. The utility selects the error, operand, quoting style, message order and exit code. Trusted errno/quoting primitives supply transformations, not the whole utility's diagnostic policy.

## Values and observations

Import `BenchWorld` from [World.dfy](../bench/core/World.dfy) for `Path = string`,
`Bytes = RawBytes = seq<RawByte>`, `Result<T> = Ok(v) | Err(e)`, `IOError`,
`FileStatus`, `FileTimes`, `TimestampUpdate`, `SyncTarget`, `SyncMode` and
`SpecialNodeKind`. `RawByte` permits all values 0–255. Text argv and paths use
the prepared Unicode-scalar, non-NUL domain; arbitrary POSIX byte paths are
not represented by this interface.

`BenchIO.Process(): IO` returns the existing process handle.
`BenchIO.Exit(code: int)` is the separate static process-exit hook.
`IO.Init` has an unsatisfiable precondition for verified callers; do not construct
fresh IO to reset observations. `io.Footprint()` exposes its complete immutable
set of regions for broad frames; prefer the smallest relevant regions.

Every observer below is ghost and reads the correspondingly named `*Region`.
The backing values are hidden by the default export.

| Observers | Values exposed |
| --- | --- |
| `fs()` | Abstract inode filesystem and alias relationships |
| `stdin()`, `stdout()`, `stderr()` | Remaining input and accumulated output bytes |
| `cwd()`, `env()`, `props()` | Working directory, environment, modeled process properties |
| `credentials()`, `security()`, `umask()` | Process identity and filesystem security context |
| `dirHandles()` | Logical directory iteration state |
| `now()`, `stdoutTimestamp()` | Modeled current seconds and stdout timestamp state |
| `trustedTimeParses()` | Results indexed by typed date/timestamp requests |
| `trustedStreams()` | Results indexed by typed read/write requests |
| `trustedFilesystem()` | Results indexed by typed filesystem requests |

A `modifies` entry below names an IO region, not arbitrary access to its
representation. `none` means no modeled heap mutation; it does not imply that a
native read has no physical effect such as host access-time bookkeeping.
Specs use `reads` and IO methods use `modifies` to express invariance.

## Streams

The stream methods expose partial progress and errno:

| Call shape | Result / observable relation |
| --- | --- |
| `ReadFile(path, FromStart)` → `(data: Bytes, err: int, stage: FileReadStage)` | Successfully read prefix; zero errno means the whole modeled file was read. Native open/read/close failures are reported through errno and stage. A Linux EISDIR error (21) identifies a modeled directory. |
| `ReadFile(path, AfterSeekEnd)` → `(data: Bytes, err: int, stage: FileReadStage)` | For a modeled directory, attempt `lseek(fd, 0, SEEK_END)` before native `read` and report its errno with the failed operation stage. This mode requires `ModeledReadFileResultFields(fs(), path) == Err(IsDirectory)`; it preserves filesystem state. |
| `ReadStdin(ReturnError)` → `(data: Bytes, err: int)` | `data + remaining == previous stdin`; zero errno means no remaining input. |
| `WriteStdout(data, ReturnError)` → `(committed: nat, err: int)` | Append exactly `data[..committed]`; zero errno guarantees all requested bytes were committed. |
| `WriteStderr(data, ReturnError)` → `(committed: nat, err: int)` | Same prefix/errno relation for stderr. |

A nonzero read errno can accompany the complete data (for example a close
failure). Callers must inspect errno even when the returned length looks right.
An empty write can report a nonzero errno with zero bytes committed when its
standard descriptor is unavailable. The committed count alone does not prove
success.
`ReadSucceeded` means zero errno; failures report `OpenFailed`, `ReadFailed`, or
`CloseFailed`. `FileReadResultFromOutcome(data, err)` converts an ordinary file
read to `Result<Bytes>` for all-or-nothing consumers: it keeps data only on zero
errno, classifies errno 21 as `IsDirectory` and 13 as `PermissionDenied`, and
uses `NoSuchFile` for other errors. `ObservedReadFileResultFields` applies the
same projection to a request-bound stream observation. The modeled file helper
validates the read prefix and path domain; it does not claim that every regular
file read succeeds.
Classification uses the read errno directly. The removed whole-file wrapper
queried `IsDirectory` after a failed read; for example, a read-permission failure
on a regular file whose metadata query succeeded fell back to `NoSuchFile`.
The current projection reports `PermissionDenied` for that EACCES outcome.
Read outcomes are tied to the typed request, including the current file or stdin
state. Write requests include the previous output and requested bytes. These
observations are logical library results, not raw syscall traces.

`StreamErrorPolicy` selects how stdin and standard-output methods handle a
positive errno. `ReturnError` returns the partial result and errno. With
`ThrowOnError`, a positive errno raises `IOException`; a normal return therefore
means stdin was fully consumed or all requested output was committed. Dafny
callers that discard write results still bind both outputs, for example
`var _, _ := io.WriteStdout(data, ThrowOnError)`. The native adapter writes
through the standard file descriptors; the former `AppendStdout` adapter also
flushed its .NET stream after writing. Descriptor writes are unbuffered at this
boundary, and the old flush call is no longer used.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `ReadFile` | `ReadFileSpec` | `none` |
| `ReadStdin` | `ReadStdinSpec` | `stdinRegion` |
| `WriteStdout` | `WriteStdoutSpec` | `stdoutRegion` |
| `WriteStderr` | `WriteStderrSpec` | `stderrRegion` |

## Diagnostics and process context

`GetCLocaleErrnoText(err)` returns libc text; `QuoteafPath(path)` returns
filename-quoting bytes. `QuoteArgument(value: Bytes)` returns C-locale
gnulib `quote_mem` argument quoting, with C escapes and single outer quotes.
Use `Utf8Semantics.Encode` for a text argument; raw input bytes need no encoding.
Unlike null-terminated `quote`, this operation retains embedded NUL as an escape;
a utility matching a C-string call must pass exactly the C-string prefix.
The abstract result values live in `IOContract`; the existing
`BenchIO.CLocaleErrnoTextResult`, `BenchIO.QuoteafPathResult` and
`BenchIO.QuoteArgumentResult` names forward to them. Utilities own message
selection, fixed text, operand order and exit policy.

`ParseTimestamp` / `ParseDate` return `(ok, sec, nsec)` under
`TrustedTimeParseResultFields`. The runtime calls pinned gnulib through
`TouchTimeParser.c` in the C locale and UTC0 environment. The utility proof relies
on this library contract; it does not verify the parser implementation.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `GetCLocaleErrnoText` | `GetCLocaleErrnoTextSpec` | `none` |
| `QuoteafPath` | `QuoteafPathSpec` | `none` |
| `QuoteArgument` | `QuoteArgumentSpec` | `none` |
| `GetCwd` | `GetCwdSpec` | `none` |
| `GetEnv` | `GetEnvSpec` | `none` |
| `GetEnvironment` | `ValidEnvironment`; `GetEnvironmentSpec` | `none` |
| `GetLoginName` | `GetLoginNameSpec` | `none` |
| `GetUmask` | `GetUmaskSpec` | `none` |
| `Now` | `NowSpec` | `none` |
| `ParseTimestamp` | `ParseTimestampSpec` | `none` |
| `ParseDate` | `ParseDateSpec` | `none` |

## Paths and metadata

Queries returning `(ok, ..., err)` require callers to branch on `ok` and retain
the specified error behavior. `FileStatus` includes inode identity, link count,
kind, mode, ownership, size/storage and times. Identity is meaningful for aliases.
`IsDirectory` requires a successful result for modeled paths and still reports
native errors for paths outside that modeled domain.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `ReadLink` | `ReadLinkSpec` | `none` |
| `PathExists` | `PathExistsSpec` | `none` |
| `GetFileMode` | `GetFileModeSpec` | `none` |
| `GetFileStatus` | `GetFileStatusSpec` | `none` |
| `IsDirectory` | `IsDirectorySpec` | `none` |
| `IsSymlink` | `IsSymlinkSpec` | `none` |
| `ResolvePathIdentity` | `ResolvePathIdentitySpec` | `none` |
| `GetFileTimes` | `GetFileTimesSpec` | `none` |

## Filesystem effects

Most methods return `(ok: bool, err: int)` and modify `fsRegion`.
The newer basic effects select a complete result using
`TrustedFilesystemEffectContractFields` and a typed request. The result includes
the complete post-filesystem, including partial effects on failure. These trusted
observations are not proofs of native filesystem refinement. `Sync` observes a
result while preserving the abstract filesystem.

`DeletePath` retains the older derived contract; `UnlinkPath` uses the typed
trusted unlink result. The methods are not interchangeable error models.
Recursive traversal, parent creation, overwrite policy and utility diagnostics
remain utility work. An available API does not mean that maintainers have approved
device privileges or every filesystem configuration.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `CreateFile` | `CreateFileSpec` | `fsRegion` |
| `WriteFile` | `WriteFileSpec` | `fsRegion` |
| `AppendFile` | `AppendFileSpec` | `fsRegion` |
| `CreateSymlink` | `CreateSymlinkSpec`; an empty destination returns native ENOENT (2) | `fsRegion` |
| `DeletePath` | `DeletePathSpec` | `fsRegion` |
| `CreateDirectory` | `CreateDirectorySpec` | `fsRegion` |
| `RemoveDirectory` | `RemoveDirectorySpec` | `fsRegion` |
| `CreateHardLink` | `CreateHardLinkSpec` | `fsRegion` |
| `UnlinkPath` | `UnlinkPathSpec` | `fsRegion` |
| `TruncateFile` | `TruncateFileSpec` | `fsRegion` |
| `CreateSpecialNode` | `CreateSpecialNodeSpec` | `fsRegion` |
| `Sync` | `SyncSpec` | `none` |
| `SetFileMode` | `SetFileModeSpec` | `fsRegion` |
| `RenamePath` | `RenamePathSpec` | `fsRegion` |

## Timestamps

`TimestampUpdate` is `Current`, `Keep` or `Exact(sec, nsec)`.
File updates modify `fsRegion`; stdout-target updates modify
`stdoutTimestampRegion`. Access/modification-only helpers select `Keep` for the
other timestamp. Current time comes from the modeled `now()` observation.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `SetFileTimesNow` | `SetFileTimesNowSpec` | `fsRegion` |
| `SetFileAccessTimeNow` | `SetFileAccessTimeNowSpec` | `fsRegion` |
| `SetFileModificationTimeNow` | `SetFileModificationTimeNowSpec` | `fsRegion` |
| `SetFileTimes` | `SetFileTimesSpec` | `fsRegion` |
| `SetStdoutTimesNow` | `SetStdoutTimesNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutAccessTimeNow` | `SetStdoutAccessTimeNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutModificationTimeNow` | `SetStdoutModificationTimeNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutTimes` | `SetStdoutTimesSpec` | `stdoutTimestampRegion` |

## Directory iteration

`OpenDir(path, includeDots)` returns `(ok, handle, err)`. `ReadDir(handle)`
returns `(hasMore, name, kind, err)` and advances the logical handle;
`CloseDir(handle)` removes it. Treat the handle as opaque. These calls do not
supply recursive traversal or a utility's ordering and filtering policy.

`BenchWorld.DirectoryEntryKind` distinguishes regular files,
directories, symlinks, FIFOs, block devices, character devices and sockets.
`UnknownDirentKind` explicitly means that the entry type is unavailable; it
must not be treated as a regular file or guessed from its name. EOF and invalid
handle results also return this unknown kind.

For utilities whose observable behavior depends on the positions of `.` and
`..`, use `OpenDir(path, true)`. The handle retains dots in its directory stream
and logical inventory; `OpenDir(path, false)` omits them. `ReadDir` infers the
mode from the handle and returns entries in the native stream order. Dots carry semantic directory
kind from their authenticated special identity, without a metadata lookup.
Non-dot entries retain the exact known or unknown native kind.

After a successful open, `GetOpenDirectoryStatus(handle)` returns
`(ok, status, err)` for that opened directory. This provides identity for cycle
detection without requiring a separate child-path status before the open.
Success consumes exactly the next ordered status observation at the handle's
resolved path, with follow enabled, and advances the status cursor by one.
Failure returns a positive errno without consuming a status observation. A
failed open and a failed opened-directory status are distinct outcomes; callers
choose the corresponding diagnostic. The status call leaves the directory
handle available for iteration or close.

| Method | Contract / relation | Modified region |
| --- | --- | --- |
| `OpenDir` | `OpenDirSpec` | `dirHandlesRegion` |
| `ReadDir` | `ReadDirSpec` | `dirHandlesRegion` |
| `GetOpenDirectoryStatus` | `GetOpenDirectoryStatusSpec` | `statusObservationsRegion` |
| `CloseDir` | `CloseDirSpec` | `dirHandlesRegion` |

## CLI and pure helpers

| Module | Main public surface | Use |
| --- | --- | --- |
| `CliTypes` | `OptionDecl`, `CliSchema`, `ParseConfig`, `ParsedArgs`, `ParseError`, `CliPlan`, `PriorHelpVersionRequest` | Declarative option schema, structured parse results and run/early-exit plans |
| `CliModel` | `ParseValue(argv, schema, cfg)` | Shared parser semantics; configuration controls order, bundling and abbreviations |
| `CliExtern` | `Cli.Parse`, `Cli.ParsePortable` | Executable wrappers with the `ParseValue` result contract |
| `BenchItem` | `BenchmarkItemTwostate<CmdRaw>`, `RunMain` | Shared plan/decode/run shell; exact hooks in [the runner contract](#entry-and-cli-contract) |
| `Utf8Semantics` | `Encode`, `EncodeChar`, `EncodeFrom`, `ValidExternalText`, `UnicodeScalar`, `EncodeConcat`, `EncodeLength` | Text conversion and encoding proof helpers |
| `BenchFunctional` | `Map`, `MapIdx`, `Enumerate`, `Gather`, `Filter`, `FilterIdx`, `FilterIndices`, `SelectedIndices`, `CountTrue` | Sequence selection/transformation |
| `BenchFunctional` | `ScanLeft`, `ScanRight`, `ScanLeftIdx`, `ScanRightIdx`, `FoldLeft`, `FoldRight`, `FoldLeftIdx`, `FoldRightIdx` | Prefix/suffix state and folds |
| `BenchFunctional` | `FoldLeftInvariantStep`, `FoldLeftIdxInvariantStep`, `FoldRightIdxInvariantStep`, `FoldLeftInvariant`, `FoldLeftIdxInvariant`, `FoldRightIdxInvariant`, `MapCongruence` | Proof reuse; inspect function preconditions and read frames in [Functional.dfy](../bench/core/Functional.dfy) |


## Trust limits and API changes

Treat the exact `IO.dfy` declarations and `IOContract.dfy` predicates as authoritative. The summaries above cannot strengthen a precondition, frame or result relation.

- Stream contracts constrain the consumed/committed prefix and errno. `FileReadStage` distinguishes successful file reads from open, read and close failures; the contracts do not expose individual syscalls or provide incremental stdin reads.
- The `ReadFile(path, AfterSeekEnd)` directory mode and `AppendFile` bind their outcomes to native observations. `AppendFile` preserves an existing regular file on empty input, appends exact bytes to its referent on success, and frames unrelated inodes; host-specific mode and timestamp effects remain within the native boundary.
- `TrustedFilesystemEffectContractFields` binds the typed request, pre-filesystem and complete supplied result. By itself it does not impose POSIX insertion/removal laws. Do not replace this binding with just `ok <==> err == 0` or choose a different resulting state to make the proof pass.
- Environment enumeration permits more than one order for the same map. Ghost credentials are not executable UID/GID or name-service queries.
- `TruncateFile` does not create a missing file. Path-targeted `Sync` lacks GNU's write-only-open retry and separate failure phases.
- There is no public arbitrary process execution, user/group lookup, terminal control, random-source or volume-capacity API. The `remaining_preparation` column of [TODOLIST.csv](../TODOLIST.csv) records the blocker for each candidate that still needs model work.

Directory creation has an additional contract. For example, a successful request
to create `parent/new` must leave a fresh empty directory at the resolved path.
A failed request must retain the supplied filesystem result; it does not promise
to restore the old filesystem.

| `CreateDirectorySpec` result | What the contract says |
| --- | --- |
| Success | `DirectoryCreationEffectFields` requires one new directory entry and a fresh empty directory. Existing inode records are preserved except parent metadata and symlink access times. |
| Parent after success | Identity, ownership, kind, mode and extension fields stay the same. Timestamps, link count and storage may change. |
| Existing symlinks after success | Only access times may change; the model does not record which links were traversed. |
| Failure | The request and returned filesystem remain linked. Rollback and exact errno selection are not guaranteed. |
| Both results | The request retains its mode, umask and time values. This contract does not establish exact permission, ownership, timestamp or link-count laws. |

`FileSystem` still requires valid inode structure. Parent symlinks and dot
components use the existing resolver; trailing slashes are accepted without
following a terminal symlink. Concurrent external changes are outside this model.

The ghost type `DirectoryValidFilesystemObservations` restricts
`IO.trustedFilesystem()` to observations consistent with the successful-directory
rule. It has at least one valid value because failure observations are allowed.
This is a proof model, not a runtime checker. Native `mkdir` remains trusted;
the contracts of other operations are unchanged.

Maintainers own shared contracts and runtime adapters. Report a missing operation with its GNU scenario, inputs, errors, effects and proposed observation. Contributors must not modify immutable support, add unchecked externs, reset IO observations, or weaken a contract to pass verification.

Evaluation owns GNU execution, runtime adapters, comparison and trusted tests. Differential replay reproduces observed evidence; it does not prove an observation satisfies a Dafny specification. Exact-specification replay adapters are not a current contribution gate. See [the full workflow](../CONTRIBUTING.md#validate-and-submit) for current checks and human review.
