# Use the trusted core API

`bench/core` provides IO APIs and their contracts for utilities. A utility proof
holds only under these contracts; libc, gnulib and the C/C# adapters are trusted,
not verified.

## Contents

- [Index](#index)
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

## Index

| Source | Responsibility |
| --- | --- |
| [World.dfy](../bench/core/World.dfy) | Mathematical model of the system |
| [Errno.dfy](../bench/core/Errno.dfy) | Linux errno constants for contracts, utilities and native adapters |
| [IOContract.dfy](../bench/core/IOContract.dfy) | Specification of IO APIs |
| [IO.dfy](../bench/core/IO.dfy) | IO APIs for making effect (e.g., read, write on files ) on the system |
| [BenchmarkItem.dfy](../bench/core/BenchmarkItem.dfy) | Benchmark item trait |
| [CliTypes.dfy](../bench/core/CliTypes.dfy), [CliModel.dfy](../bench/core/CliModel.dfy), [CliExtern.dfy](../bench/core/CliExtern.dfy) | CLI helpers for making utility cli parsers. |
| [Utf8.dfy](../bench/core/Utf8.dfy), [StringEscaping.dfy](../bench/core/StringEscaping.dfy) | String-related utilities |
| [Functional.dfy](../bench/core/Functional.dfy) | Higher-order functions for functional-style programming |

## Copy stdin with explicit error results

[StreamCopy](../tools/fixtures/contributor/StreamCopy.dfy) copies the stdin bytes
it read, even after a read error, and returns both errors so the caller picks the
exit status. The checked-in file uses a relative `include`.

```dafny
include "/workspace/dafnyutils/bench/core/IO.dfy"

module StreamCopy {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures readErr == 0 && writeErr == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin())
  {
    var read := io.ReadStdin(BW.ReturnError);
    var data := C.ReadResultData(read);
    readErr := C.ResultErrno(read);
    var write := io.WriteStdout(data, BW.ReturnError);
    writeErr := C.ResultErrno(write);
  }

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var readErr, writeErr := CopyInput(BenchIO.Process());
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }
}
```

`old(io.stdout())` is needed because stdout changes. The frame covers all other
state; do not restate it.

```sh
# Expected duration: Estimated 1–10 sec for this small client after tool installation.
# Success criteria: Exit 0 and zero verification errors.
dafny-benchmark verify --standard-libraries:false tools/fixtures/contributor/StreamCopy.dfy
```

This checks only the client contract, not the native build, GNU `cat` parity or
error messages. Expected output:

```text
Dafny program verifier finished with 4 verified, 0 errors
```

For a complete program with a partial-result spec, exit policy, proof, build and
error tests, see the
[small IO example](../README.md#example-test-and-verify-a-small-program).

## Entry and CLI contract

A utility is a `BenchItem.BenchmarkItemTwostate<CmdRaw>` with hooks `Name`,
`Schema`, `ParseConfig`, `Decode`, `FormatParseError`, `PlanParsed`,
`PlanParseFailure`, `PlanArgv` and `RunCore`. `BenchItem.RunMain(item, argv, io)`
runs `RunCore` for `CliRun(raw)`, or writes the planned output and exit status
for `CliEarlyExit`.

- `RunCore` must ensure `Spec(raw, io, exit)` directly; a proof about a helper
  is not enough.
- Test early exits too. Example: `true` and `false` keep the original argument
  count when detecting help/version.
- Keep fixed diagnostic text in Spec. The utility chooses the error, operand,
  quoting style, message order and exit code; trusted errno and quoting calls
  only transform values.
- Note that we don't verify CLI parsing itself. In the formal specification,
  we assume that input arguments are well-formed.

## Values and observations

`IOResult<T>` is `Results.Result<T, IOError>`, i.e. `Ok(v) | Err(e)` from
[Result.dfy](../bench/core/Result.dfy). It supports `Map`, `Bind` and Dafny's
`:-` error propagation.

- `BenchIO.Process()`: the process's `IO` handle.
- `BenchIO.Exit(code)`: exits the process.
- `IO.Init` cannot be called from verified code. Never create a new `IO` to
  reset observations.
- `io.Footprint()`: all regions, for broad frames. Prefer the smallest regions.

Observers are ghost (proof-only), each reads its same-named getter function (e.g., `fs()` reads `fsRegion`).
Direct access to `*Region` field is not allowed.

| Observer | Value |
| --- | --- |
| `fs()` | Inode filesystem, including aliases |
| `stdin()`, `stdout()`, `stderr()` | Unread input; output written so far |
| `cwd()`, `env()`, `props()` | Working directory, environment, process properties |
| `credentials()`, `security()`, `umask()` | Process identity and filesystem security context |
| `dirHandles()` | Directory iteration state |
| `now()`, `stdoutTimestamp()` | Current seconds; stdout timestamp state |
| `statusObservations()`, `statusCursor()` | File-status observations and the next position (`statusObservationsRegion`) |
| `trustedTimeParses()` | Result per date/timestamp parse request |
| `trustedStreams()` | Result per read/write request |
| `trustedFilesystem()` | Result per filesystem request |

In the tables below, "Modifies" names an IO region. `none` means no modeled
change; a native read may still update host access times. Specs use `reads` and
methods use `modifies` to state what stays unchanged.

## Streams

Stream methods return `IOResult<T>`.

| Policy | On failure |
| --- | --- |
| `ReturnError` | Returns `Err` |
| `ThrowOnError` | Only for non-recoverable errors. Raises `IOException`; a normal return is always `Ok` |

Use `var data :- assert io.ReadStdin(ThrowOnError)`, or
`var _ := io.WriteStdout(data, ThrowOnError)` to ignore a write result. Writes to
standard descriptors are unbuffered.

| Function | Return |
| --- | --- |
| `ReadFile(path)` → `IOResult<Bytes>` | `Ok`: the byte stream of whole file. `Err(ReadFailure(errno, message, partial, readStage))`: errno, message, bytes read, failed stage. |
| `ReadStdin(ReturnError)` → `IOResult<Bytes>` | `StreamFailure` holds the bytes read; bytes read + remaining input = old stdin. |
| `WriteStdout(data, ReturnError)` → `IOResult<WriteReceipt>` | Appends exactly the committed prefix; `StreamFailure` holds the count. |
| `WriteStderr(data, ReturnError)` → `IOResult<WriteReceipt>` | Same, for stderr. |

Full data does not mean success: a read can fail at close after returning all
bytes, and an empty write can fail with nothing committed.

- `ResultErrno`, `ReadResultData`, `ReadResultStage`, `WriteResultCommitted`
  (`IOContract`): get the errno, bytes, stage or committed count from a result.
- `FileReadResultFromOutcome`, `ObservedReadFileResultFields`: build a read
  result from a native outcome or a stream observation. Utility code uses
  `ReadFile`'s result directly.

Each utility decides what to do with partial data; `cat` prints the bytes read
before the error. Read diagnostics come from the errno and failed stage, not a
later metadata lookup.

| Method | Contract | Modifies |
| --- | --- | --- |
| `ReadFile` | `ReadFileSpec` | `none` |
| `ReadStdin` | `ReadStdinSpec` | `stdinRegion` |
| `WriteStdout` | `WriteStdoutSpec` | `stdoutRegion` |
| `WriteStderr` | `WriteStderrSpec` | `stderrRegion` |

## Diagnostics and process context

- `GetCLocaleErrnoText(err)`: libc error text.
- `QuoteafPath(path)`: quoted file name bytes.
- `QuoteArgument(value: Bytes)`: gnulib `quote_mem` quoting (C locale, C escapes,
  single quotes). Encode text with `Utf8Semantics.Encode`; raw input bytes need
  no encoding. An embedded NUL is
  escaped, so to match a C-string `quote` call, pass only the bytes before it.
- `ParseTimestamp`, `ParseDate`: `IOResult<ParsedInstant>` under
  `TrustedTimeParseResultFields`, from pinned gnulib via `TouchTimeParser.c`
  (C locale, `TZ=UTC0`). The parser is trusted, not verified.
- The result values are defined in `IOContract`; `BenchIO.CLocaleErrnoTextResult`,
  `BenchIO.QuoteafPathResult` and `BenchIO.QuoteArgumentResult` forward to them.

| Method | Contract | Modifies |
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

| Method | Returns | Contract | Modifies |
| --- | --- | --- | --- |
| `ReadLink` | `IOResult<Path>` | `ReadLinkSpec` | `none` |
| `PathExists` | `IOResult<Unit>` | `PathExistsSpec` | `none` |
| `GetFileMode` | `IOResult<bv32>` | `GetFileModeSpec` | `none` |
| `GetFileStatus` | `IOResult<FileStatus>` | `GetFileStatusSpec` | `statusObservationsRegion` |
| `IsDirectory` | `IOResult<bool>` | `IsDirectorySpec` | `none` |
| `IsSymlink` | `IOResult<bool>` | `IsSymlinkSpec` | `none` |
| `ResolvePathIdentity` | `IOResult<Path>` | `ResolvePathIdentitySpec` | `none` |
| `GetFileTimes` | `IOResult<FileTimeStatus>` | `GetFileTimesSpec` | `none` |

- On failure, `Err` holds the errno and message; there is no metadata.
- `FileStatus`: inode identity, link count, kind, mode, owner, size/storage and
  times. Identity tells aliases apart.
- `GetFileStatus` consumes the next status observation and advances the cursor,
  even on failure.
- `IsDirectory` must succeed on paths the model resolves; other paths get the
  native error.

## Filesystem effects

- `WriteFile`, `AppendFile`: `IOResult<WriteReceipt>`. `WriteFailure` holds the
  errno, message, committed count and `FileWriteStage` (see
  [Write failures](#write-failures)).
- All other calls: `IOResult<Unit>`. All except `Sync` modify `fsRegion`.
- `CreateDirectory`, `RemoveDirectory`, `CreateHardLink`, `UnlinkPath`,
  `TruncateFile` and `CreateSpecialNode` take their whole result, including the
  filesystem after the call (also on failure), from a trusted observation
  (`TrustedFilesystemEffectContractFields`). This does not prove that the native
  filesystem matches the model.
- `Sync` takes a trusted result and does not change the modeled filesystem.
- `CreateHardLink` passes empty paths to native `link`, which picks the errno.
  A path with NUL fails with `EINVAL`.
- `DeletePath` computes its result from the model; `UnlinkPath` uses the trusted
  result. Their error models differ; do not swap them.
- Recursion, parent creation, overwrite policy and diagnostics are up to the
  utility. An available API does not mean device privileges or every filesystem
  setup are approved.

| Method | Contract | Modifies |
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

`TimestampUpdate` is `Current`, `Keep` or `Exact(sec, nsec)`. Setters return
`IOResult<Unit>`. File setters modify `fsRegion`; stdout setters modify
`stdoutTimestampRegion`. Access-only and modification-only setters `Keep` the
other time. The current time is the modeled `now()`.

| Method | Contract | Modifies |
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

- `OpenDir(path, includeDots)` → `IOResult<int>`, an opaque handle.
- `ReadDir(handle)` → `IOResult<DirectoryRead>`: `DirectoryItem(name, kind)`,
  `DirectoryEnd` at EOF, or `Err` (e.g., an invalid handle). It advances the
  handle and returns entries in native order.
- `CloseDir(handle)` closes the handle.
- Recursion, ordering and filtering are up to the utility.

Entry kinds (`BenchWorld.DirectoryEntryKind`): regular file, directory, symlink,
FIFO, block device, character device, socket, or `UnknownDirentKind`. Never treat
an unknown kind as a regular file or guess it from the name.

`OpenDir(path, true)` keeps `.` and `..`; use it when their position matters.
`false` omits them; `ReadDir` follows the handle's mode. Dots get
`DirectoryDirentKind` without a metadata lookup;
other entries keep their native kind, known or unknown.

`GetOpenDirectoryStatus(handle)` → `IOResult<FileStatus>` of the open directory,
for cycle detection without a separate status call before the open.

- Success consumes the next status observation for the handle's resolved path
  (following symlinks) and advances the cursor by one.
- Failure returns a positive errno and consumes nothing.
- A failed status differs from a failed open; use the matching diagnostic.
- The handle stays open.

| Method | Contract | Modifies |
| --- | --- | --- |
| `OpenDir` | `OpenDirSpec` | `dirHandlesRegion` |
| `ReadDir` | `ReadDirSpec` | `dirHandlesRegion` |
| `GetOpenDirectoryStatus` | `GetOpenDirectoryStatusSpec` | `statusObservationsRegion` |
| `CloseDir` | `CloseDirSpec` | `dirHandlesRegion` |

## CLI and pure helpers

| Module | Main names | Use |
| --- | --- | --- |
| `CliTypes` | `OptionDecl`, `CliSchema`, `ParseConfig`, `ParsedArgs`, `ParseError`, `CliPlan`, `PriorHelpVersionRequest` | Option schema, parse results, run/early-exit plans |
| `CliModel` | `ParseValue(argv, schema, cfg)` | Shared parser; the config sets order, bundling and abbreviations |
| `CliExtern` | `Cli.Parse`, `Cli.ParsePortable` | Executable wrappers with the `ParseValue` result contract |
| `BenchItem` | `BenchmarkItemTwostate<CmdRaw>`, `RunMain` | Shared plan/decode/run shell; hooks in [Entry and CLI contract](#entry-and-cli-contract) |
| `Utf8Semantics` | `Encode`, `EncodeChar`, `EncodeFrom`, `ValidExternalText`, `UnicodeScalar`, `EncodeConcat`, `EncodeLength` | Text encoding and its proof helpers |
| `BenchFunctional` | `Map`, `MapIdx`, `Enumerate`, `Gather`, `Filter`, `FilterIdx`, `FilterIndices`, `SelectedIndices`, `CountTrue` | Select and transform sequences |
| `BenchFunctional` | `ScanLeft`, `ScanRight`, `ScanLeftIdx`, `ScanRightIdx`, `FoldLeft`, `FoldRight`, `FoldLeftIdx`, `FoldRightIdx` | Prefix/suffix state and folds |
| `BenchFunctional` | `FoldLeftInvariantStep`, `FoldLeftIdxInvariantStep`, `FoldRightIdxInvariantStep`, `FoldLeftInvariant`, `FoldLeftIdxInvariant`, `FoldRightIdxInvariant`, `MapCongruence` | Reusable proofs; check preconditions and read frames in [Functional.dfy](../bench/core/Functional.dfy) |

## Trust limits and API changes

`IO.dfy` and `IOContract.dfy` are authoritative; this page cannot strengthen
them.

- Stream contracts fix only the consumed or committed prefix and the errno. They
  describe library results, not syscalls. `FileReadStage` is success, or an
  open, read or close failure. There are no incremental stdin reads.
- `AppendFile` results come from native observations. `AppendFile` keeps the
  file on empty input, appends exactly the bytes to the file (or symlink target)
  on success, and leaves other inodes alone; mode and timestamp effects are
  host-specific.
- `GetEnvironment` may list the same map in different orders.
- Ghost credentials are not real UID/GID or name-service lookups.
- `GetFileTimes` and `GetFileStatus` report `ENAMETOOLONG` as `ENOENT`;
  `GetFileMode` does not.
- `TruncateFile` does not create a missing file. Path `Sync` lacks GNU's
  write-only-open retry and separate failure phases.
- There is no API for running processes, user/group lookup, terminal control,
  random data, disk capacity or seeking within a file. The `remaining_preparation` column of
  [TODOLIST.csv](../TODOLIST.csv) lists what each candidate still needs.

### Filesystem validation

Every trusted filesystem result satisfies `ValidFilesystemObservation`:

- errno is never negative, and the call succeeds exactly when errno is 0;
- no success that the model rules out;
- failure errnos and effects stay within per-operation limits;
- successful directory creation and file writes have the expected effect.

`TrustedFilesystemEffectContractFields` links the request, the prior filesystem
and the result, and requires this check. Keep that link and the check when you
use these contracts. Other success
effects come from each operation's own predicate. The check is proved
satisfiable and never replaces a native errno. The native filesystem is still
trusted.

### Directory creation

Example: creating `parent/new` successfully leaves a fresh empty directory at the
resolved path.

| `CreateDirectorySpec` result | Guarantee |
| --- | --- |
| Success | One new entry: a fresh empty directory (`DirectoryCreationEffectFields`). Other inodes unchanged, except parent metadata and symlink access times. |
| Parent after success | Identity, owner, kind, mode and extension fields unchanged; times, link count and storage may change. |
| Symlinks after success | Only access times may change; traversed links are not tracked. |
| Failure | The request and the returned filesystem stay linked. Namespace and inodes unchanged, except symlink access times. Errno is the modeled cause or a listed host fault. |
| Both | Mode, umask and time come from the request. No exact permission, owner, time or link-count rules. |

`FileSystem` requires a valid inode structure. Parent symlinks and `.`/`..` use
the normal resolver; trailing slashes are accepted without following a final
symlink. Concurrent outside changes are not modeled.

### Error order

- `HardLinkFailureErrnosFields`: a NUL in either path gives only `EINVAL`.
  Otherwise the source is resolved before the empty-target check, so `source/`
  with an empty target excludes `ENOENT` when the source lookup gives `ENOTDIR`.
- `RenameFailureErrnosFields` checks for NUL, then for an empty source or target,
  before resolving either path.
- `unlink` and `rmdir` reject a final symlink with a trailing slash.
- Native fault sets also allow storage, allocation, access-control and
  filesystem-limit errors that the model does not track.

### Write failures

| `FileWriteStage` | Committed | Filesystem after |
| --- | --- | --- |
| `WriteOpenFailed` | 0 | Unchanged, except symlink access times |
| `WriteFailed` | Fewer than requested | `WriteFile`: the file may be created or truncated and holds exactly the committed prefix. `AppendFile`: old contents + committed prefix. |
| `WriteCloseFailed` | All | Same as `WriteFailed` |

Files created by a failed write still follow the creation mode and owner rules.
`CreateFile` can fail at close after creating its empty file.

### Contributor and maintainer rules

- Maintainers own shared contracts and adapters. To request a missing operation,
  give its GNU scenario, inputs, errors, effects and proposed observation.
- Do not modify immutable support, add unchecked externs, reset IO observations,
  or weaken a contract to pass verification.
- Evaluation owns GNU execution, adapters, comparison and trusted tests.
  Differential replay reproduces observed behavior; it does not prove a Dafny
  spec. Exact-spec replay is not required for contributions. See
  [the full workflow](../CONTRIBUTING.md#validate-and-submit).
