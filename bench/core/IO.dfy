include "World.dfy"
include "IOContract.dfy"
include "SecurityModel.dfy"

module BenchIO {
  import Result = Results
  import opened BenchWorld
  import C = IOContract
  import Sec = SecurityModel

  // Public trusted-library API: observers, immutable footprints and operations.
  // See ../../docs/core-api.md for the module map, contracts and frames.
  export
    provides Result
    reveals IO, FsRegion, PropsRegion, CwdRegion, EnvRegion, StdinRegion, StdoutRegion, StderrRegion, DirHandlesRegion, NowRegion, CredentialsRegion, TrustedTimeParsesRegion, TrustedStreamsRegion, TrustedFilesystemRegion, StdoutTimestampRegion, StatusObservationsRegion
    provides Process, IO.Init
    reveals IO.Footprint
    reveals SecurityRegion, UmaskRegion
    provides BenchWorld, C, Sec, Exit
    reveals CLocaleErrnoTextResult, QuoteafPathResult, QuoteArgumentResult
    provides IO.securityRegion, IO.security
    provides IO.umaskRegion, IO.umask
    provides IO.fsRegion, IO.fs
    provides IO.propsRegion, IO.props
    provides IO.cwdRegion, IO.cwd
    provides IO.envRegion, IO.env
    provides IO.stdinRegion, IO.stdin
    provides IO.stdoutRegion, IO.stdout
    provides IO.stderrRegion, IO.stderr
    provides IO.dirHandlesRegion, IO.dirHandles
    provides IO.nowRegion, IO.now
    provides IO.trustedTimeParsesRegion, IO.trustedTimeParses
    provides IO.trustedStreamsRegion, IO.trustedStreams
    provides IO.trustedFilesystemRegion, IO.trustedFilesystem
    provides IO.stdoutTimestampRegion, IO.stdoutTimestamp
    provides IO.statusObservationsRegion, IO.statusObservations, IO.statusCursor
    provides IO.credentialsRegion, IO.credentials
    provides IO.ReadFile, IO.ReadLink, IO.ReadStdin
    provides IO.WriteStdout, IO.WriteStderr
    provides IO.GetCLocaleErrnoText, IO.QuoteafPath, IO.QuoteArgument
    provides IO.GetCwd, IO.GetEnv, IO.GetEnvironment, IO.GetLoginName, IO.Now
    provides IO.ParseTimestamp, IO.ParseDate
    provides IO.PathExists, IO.CreateFile, IO.WriteFile, IO.AppendFile, IO.CreateSymlink, IO.DeletePath
    provides IO.CreateDirectory, IO.RemoveDirectory, IO.CreateHardLink, IO.UnlinkPath
    provides IO.TruncateFile, IO.CreateSpecialNode, IO.Sync
    provides IO.SetFileTimesNow, IO.SetFileAccessTimeNow, IO.SetFileModificationTimeNow
    provides IO.GetFileTimes, IO.SetFileTimes
    provides IO.SetStdoutTimesNow, IO.SetStdoutAccessTimeNow, IO.SetStdoutModificationTimeNow
    provides IO.SetStdoutTimes
    provides IO.GetFileMode, IO.GetFileStatus, IO.GetOpenDirectoryStatus, IO.SetFileMode, IO.GetUmask
    provides IO.OpenDir, IO.ResolvePathIdentity
    provides IO.ReadDir, IO.CloseDir
    provides IO.IsDirectory, IO.IsSymlink, IO.RenamePath

  class SecurityRegion {
    ghost var value: Sec.FilesystemSecurityContext

    ghost constructor Init(initial: Sec.FilesystemSecurityContext)
      ensures value == initial
    {
      value := initial;
    }
  }

  class UmaskRegion {
    ghost var value: bv32

    ghost constructor Init(initial: bv32)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class FsRegion {
    ghost var value: FileSystem

    ghost constructor Init(initial: FileSystem)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class PropsRegion {
    ghost var value: map<string, string>

    ghost constructor Init(initial: map<string, string>)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class CwdRegion {
    ghost var value: Path

    ghost constructor Init(initial: Path)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class EnvRegion {
    ghost var value: C.Environment

    ghost constructor Init(initial: C.Environment)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StdinRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StdoutRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StderrRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class DirHandlesRegion {
    ghost var value: map<int, DirHandleState>

    ghost constructor Init(initial: map<int, DirHandleState>)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class NowRegion {
    ghost var value: int

    ghost constructor Init(initial: int)
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedTimeParsesRegion {
    ghost var value: map<TimeParseRequest, ParsedTimeResult>

    ghost constructor Init(initial: map<TimeParseRequest, ParsedTimeResult>)
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedStreamsRegion {
    ghost var value: (TrustedStreamRequest) -> TrustedStreamResult

    ghost constructor Init(
      initial: (TrustedStreamRequest) -> TrustedStreamResult
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedFilesystemRegion {
    ghost var value: C.ValidFilesystemObservations

    ghost constructor Init(
      initial: C.ValidFilesystemObservations
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class StdoutTimestampRegion {
    ghost var value: StdoutTimestampState

    ghost constructor Init(initial: StdoutTimestampState)
      ensures value == initial
    {
      value := initial;
    }
  }

  class StatusObservationsRegion {
    ghost const observations: StatusTimeObservations
    ghost var cursor: nat

    ghost constructor Init(initial: StatusTimeObservations, first: nat)
      ensures observations == initial && cursor == first
    {
      observations := initial;
      cursor := first;
    }
  }

  // The representation and its named constructor are not exported.
  class CredentialsRegion {
    ghost var value: ProcessCredentials

    ghost constructor Init(initial: ProcessCredentials)
      ensures value == initial
    {
      value := initial;
    }
  }

  // Exits the process with the given status code.
  method {:extern "BenchIOExtern", "Exit"} Exit(code: int)

  // Trusted libc/gnulib-compatible diagnostic results. These names forward to
  // abstract IOContract values, so clients prove message composition without
  // implementing library lookup tables or quoting loops.
  ghost function CLocaleErrnoTextResult(err: int): string { C.CLocaleErrnoTextResult(err) }

  ghost function QuoteafPathResult(path: Path): Bytes { C.QuoteafPathResult(path) }

  ghost function QuoteArgumentResult(value: Bytes): Bytes { C.QuoteArgumentResult(value) }

  // The host provides one pre-existing process handle. This pure accessor
  // promises identity only, never fresh regions or mutable world invariants.
  const {:extern "BenchIOExtern", "ProcessHandle"} ProcessHandle: IO

  function Process(): IO {
    ProcessHandle
  }

  class {:termination false} IO {
    ghost const fsRegion: FsRegion
    ghost const propsRegion: PropsRegion
    ghost const cwdRegion: CwdRegion
    ghost const envRegion: EnvRegion
    ghost const stdinRegion: StdinRegion
    ghost const stdoutRegion: StdoutRegion
    ghost const stderrRegion: StderrRegion
    ghost const dirHandlesRegion: DirHandlesRegion
    ghost const nowRegion: NowRegion
    ghost const trustedTimeParsesRegion: TrustedTimeParsesRegion
    ghost const trustedStreamsRegion: TrustedStreamsRegion
    ghost const trustedFilesystemRegion: TrustedFilesystemRegion
    ghost const stdoutTimestampRegion: StdoutTimestampRegion
    ghost const statusObservationsRegion: StatusObservationsRegion
    ghost const credentialsRegion: CredentialsRegion
    ghost const securityRegion: SecurityRegion
    ghost const umaskRegion: UmaskRegion

    // Dafny's revealed-class export requires a constructor for these fields.
    // No consistent verified client can call it. The native singleton allocates
    // its C# object directly; it never invokes this ghost-state initializer.
    constructor Init()
      requires false
    {
      ghost var initialFileSystem: FileSystem :| true;
      fsRegion := new FsRegion.Init(initialFileSystem);
      ghost var initialPropsRegion: map<string, string> :| true;
      propsRegion := new PropsRegion.Init(initialPropsRegion);
      ghost var initialCwdRegion: Path :| true;
      cwdRegion := new CwdRegion.Init(initialCwdRegion);
      ghost var initialEnvRegion: C.Environment :| true;
      envRegion := new EnvRegion.Init(initialEnvRegion);
      ghost var initialStdinRegion: Bytes :| true;
      stdinRegion := new StdinRegion.Init(initialStdinRegion);
      ghost var initialStdoutRegion: Bytes :| true;
      stdoutRegion := new StdoutRegion.Init(initialStdoutRegion);
      ghost var initialStderrRegion: Bytes :| true;
      stderrRegion := new StderrRegion.Init(initialStderrRegion);
      ghost var initialDirHandlesRegion: map<int, DirHandleState> :| true;
      dirHandlesRegion := new DirHandlesRegion.Init(initialDirHandlesRegion);
      ghost var initialNowRegion: int :| true;
      nowRegion := new NowRegion.Init(initialNowRegion);
      ghost var initialTrustedTimeParses: map<TimeParseRequest, ParsedTimeResult> :| true;
      trustedTimeParsesRegion := new TrustedTimeParsesRegion.Init(initialTrustedTimeParses);
      ghost var initialTrustedStreams:
                (TrustedStreamRequest) -> TrustedStreamResult :| true;
      trustedStreamsRegion := new TrustedStreamsRegion.Init(initialTrustedStreams);
      ghost var initialTrustedFilesystem:
                C.ValidFilesystemObservations :| true;
      trustedFilesystemRegion := new TrustedFilesystemRegion.Init(initialTrustedFilesystem);
      ghost var initialStdoutTimestamp: StdoutTimestampState :| true;
      stdoutTimestampRegion := new StdoutTimestampRegion.Init(initialStdoutTimestamp);
      ghost var initialStatusObservations: StatusTimeObservations :| true;
      statusObservationsRegion := new StatusObservationsRegion.Init(initialStatusObservations, 0);
      ghost var initialCredentialsRegion: ProcessCredentials :| true;
      credentialsRegion := new CredentialsRegion.Init(initialCredentialsRegion);
      ghost var initialSecurityRegion: Sec.FilesystemSecurityContext :| true;
      securityRegion := new SecurityRegion.Init(initialSecurityRegion);
      umaskRegion := new UmaskRegion.Init(C.GetUmaskResultFields(initialPropsRegion));
    }

    // Stable aggregate for predicates that formerly read the entire IO object.
    ghost function Footprint(): set<object>
    {
      { fsRegion, propsRegion, cwdRegion, envRegion, stdinRegion, stdoutRegion, stderrRegion, dirHandlesRegion, nowRegion, trustedTimeParsesRegion, trustedStreamsRegion, trustedFilesystemRegion, stdoutTimestampRegion, statusObservationsRegion, credentialsRegion, securityRegion, umaskRegion }
    }

    ghost function security(): Sec.FilesystemSecurityContext
      reads securityRegion
    {
      securityRegion.value
    }

    ghost function umask(): bv32
      reads umaskRegion
    {
      umaskRegion.value
    }

    ghost function fs(): FileSystem
      reads fsRegion
    {
      fsRegion.value
    }

    ghost function props(): map<string, string>
      reads propsRegion
    {
      propsRegion.value
    }

    ghost function cwd(): Path
      reads cwdRegion
    {
      cwdRegion.value
    }

    ghost function env(): C.Environment
      reads envRegion
    {
      envRegion.value
    }

    ghost function stdin(): Bytes
      reads stdinRegion
    {
      stdinRegion.value
    }

    ghost function stdout(): Bytes
      reads stdoutRegion
    {
      stdoutRegion.value
    }

    ghost function stderr(): Bytes
      reads stderrRegion
    {
      stderrRegion.value
    }

    ghost function dirHandles(): map<int, DirHandleState>
      reads dirHandlesRegion
    {
      dirHandlesRegion.value
    }

    ghost function now(): int
      reads nowRegion
    {
      nowRegion.value
    }

    ghost function trustedTimeParses(): map<TimeParseRequest, ParsedTimeResult>
      reads trustedTimeParsesRegion
    {
      trustedTimeParsesRegion.value
    }

    ghost function trustedStreams():
      (TrustedStreamRequest) -> TrustedStreamResult
      reads trustedStreamsRegion
    {
      trustedStreamsRegion.value
    }

    ghost function trustedFilesystem():
      C.ValidFilesystemObservations
      reads trustedFilesystemRegion
    {
      trustedFilesystemRegion.value
    }

    ghost function stdoutTimestamp(): StdoutTimestampState
      reads stdoutTimestampRegion
    {
      stdoutTimestampRegion.value
    }

    ghost function statusObservations(): StatusTimeObservations
    {
      statusObservationsRegion.observations
    }

    ghost function statusCursor(): nat
      reads statusObservationsRegion
    {
      statusObservationsRegion.cursor
    }

    ghost function credentials(): ProcessCredentials
      reads credentialsRegion
    {
      credentialsRegion.value
    }

    // Reads a file and returns the committed prefix, errno and terminal stage.
    method {:extern "NativeReadFile"} {:axiom} NativeReadFile(path: Path)
      returns (data: Bytes, err: int, stage: BenchWorld.FileReadStage)
      ensures C.ReadFileSpec(
                old(fs()), old(trustedStreams()), path, data, err, stage)

    method ReadFile(path: Path) returns (result: IOResult<Bytes>)
      ensures C.ReadFileSpec(
                old(fs()), old(trustedStreams()), path, C.ReadResultData(result), C.ResultErrno(result), C.ReadResultStage(result))
      ensures result == C.ObservedReadFileResultFields(old(fs()), old(trustedStreams()), path)
    {
      var data, err, stage := NativeReadFile(path);
      if err == 0 {
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(ReadFailure(err, message, data, stage));
      }
    }

    // Reads the raw target of the symbolic link at the given path.
    method {:extern "ReadLink"} {:axiom} ReadLink(path: Path) returns (r: IOResult<Path>)
      ensures C.ReadLinkSpec(old(fs()), path, r)

    // Reads stdin to EOF or an error; ThrowOnError raises on a failed read.
    method {:extern "NativeReadStdin"} {:axiom} NativeReadStdin(policy: BenchWorld.StreamErrorPolicy)
      returns (data: Bytes, err: int)
      modifies stdinRegion
      ensures C.ReadStdinSpec(old(stdin()), old(trustedStreams()), stdin(), policy, data, err)

    method ReadStdin(policy: BenchWorld.StreamErrorPolicy) returns (result: IOResult<Bytes>)
      modifies stdinRegion
      ensures C.ReadStdinSpec(old(stdin()), old(trustedStreams()), stdin(), policy, C.ReadResultData(result), C.ResultErrno(result))
      ensures policy == ThrowOnError ==> result.Ok?
    {
      var data, err := NativeReadStdin(policy);
      if err == 0 {
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, data, |data|));
      }
    }

    // Writes stdout and reports committed bytes; ThrowOnError raises on failure.
    method {:extern "NativeWriteStdout"} {:axiom} NativeWriteStdout(b: Bytes, policy: BenchWorld.StreamErrorPolicy)
      returns (committed: nat, err: int)
      modifies stdoutRegion
      ensures C.WriteStdoutSpec(old(stdout()), old(trustedStreams()), stdout(), b, policy, committed, err)

    method WriteStdout(b: Bytes, policy: BenchWorld.StreamErrorPolicy) returns (result: IOResult<WriteReceipt>)
      modifies stdoutRegion
      ensures C.WriteStdoutSpec(old(stdout()), old(trustedStreams()), stdout(), b, policy, C.WriteResultCommitted(result), C.ResultErrno(result))
      ensures policy == ThrowOnError ==> result.Ok?
    {
      var committed, err := NativeWriteStdout(b, policy);
      if err == 0 {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, [], committed));
      }
    }

    // Writes stderr and reports committed bytes; ThrowOnError raises on failure.
    method {:extern "NativeWriteStderr"} {:axiom} NativeWriteStderr(b: Bytes, policy: BenchWorld.StreamErrorPolicy)
      returns (committed: nat, err: int)
      modifies stderrRegion
      ensures C.WriteStderrSpec(old(stderr()), old(trustedStreams()), stderr(), b, policy, committed, err)

    method WriteStderr(b: Bytes, policy: BenchWorld.StreamErrorPolicy) returns (result: IOResult<WriteReceipt>)
      modifies stderrRegion
      ensures C.WriteStderrSpec(old(stderr()), old(trustedStreams()), stderr(), b, policy, C.WriteResultCommitted(result), C.ResultErrno(result))
      ensures policy == ThrowOnError ==> result.Ok?
    {
      var committed, err := NativeWriteStderr(b, policy);
      if err == 0 {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, [], committed));
      }
    }

    // Returns libc's diagnostic text under the benchmark's C locale.
    method {:extern "GetCLocaleErrnoText"} {:axiom} GetCLocaleErrnoText(err: int)
      returns (text: string)
      ensures C.GetCLocaleErrnoTextSpec(err, text)

    // Returns gnulib quoteaf-compatible bytes for a public text path.
    method {:extern "QuoteafPath"} {:axiom} QuoteafPath(path: Path)
      returns (quoted: Bytes)
      ensures C.QuoteafPathSpec(path, quoted)

    // C-locale gnulib quote_mem style, retaining the full raw-byte argument.
    method {:extern "QuoteArgument"} {:axiom} QuoteArgument(value: Bytes)
      returns (quoted: Bytes)
      ensures C.QuoteArgumentSpec(value, quoted)

    // Returns the current working directory.
    method {:extern "GetCwd"} {:axiom} GetCwd() returns (cwd: Path)
      ensures C.GetCwdSpec(old(this.cwd()), cwd)

    // Looks up an environment variable by name.
    method {:extern "GetEnv"} {:axiom} GetEnv(key: string) returns (r: IOResult<string>)
      ensures C.GetEnvSpec(old(env()), key, r)

    // Returns the current environment as KEY=VALUE entries.
    method {:extern "GetEnvironment"} {:axiom} GetEnvironment() returns (entries: seq<string>)
      requires C.ValidEnvironment(env())
      ensures C.GetEnvironmentSpec(old(env()), entries)

    // Looks up the login user name.
    method {:extern "GetLoginName"} {:axiom} GetLoginName() returns (r: IOResult<string>)
      ensures C.GetLoginNameSpec(old(props()), r)

    // Returns the current time as an integer timestamp.
    method {:extern "Now"} {:axiom} Now() returns (t: int)
      ensures C.NowSpec(old(now()), t)

    // Parses a touch -t timestamp relative to a reference time.
    method {:extern "NativeParseTimestamp"} {:axiom} NativeParseTimestamp(timestamp: string, nowSec: int, nowNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseTimestampSpec(old(trustedTimeParses()), timestamp, nowSec, nowNsec, ok, sec, nsec)

    method ParseTimestamp(timestamp: string, nowSec: int, nowNsec: int) returns (result: IOResult<ParsedInstant>)
      ensures C.ParseTimestampSpec(old(trustedTimeParses()), timestamp, nowSec, nowNsec, result.Ok?, C.ParsedResultValue(result).sec, C.ParsedResultValue(result).nsec)
    {
      var ok, sec, nsec := NativeParseTimestamp(timestamp, nowSec, nowNsec);
      if ok {
        result := Result.Ok(ParsedInstant(sec, nsec));
      } else {
        result := Result.Err(TimeParseFailure("invalid time", sec, nsec));
      }
    }

    // Parses a touch -d date string relative to a reference time.
    method {:extern "NativeParseDate"} {:axiom} NativeParseDate(date: string, refSec: int, refNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseDateSpec(old(trustedTimeParses()), date, refSec, refNsec, ok, sec, nsec)

    method ParseDate(date: string, refSec: int, refNsec: int) returns (result: IOResult<ParsedInstant>)
      ensures C.ParseDateSpec(old(trustedTimeParses()), date, refSec, refNsec, result.Ok?, C.ParsedResultValue(result).sec, C.ParsedResultValue(result).nsec)
    {
      var ok, sec, nsec := NativeParseDate(date, refSec, refNsec);
      if ok {
        result := Result.Ok(ParsedInstant(sec, nsec));
      } else {
        result := Result.Err(TimeParseFailure("invalid time", sec, nsec));
      }
    }

    // Checks whether a path exists, optionally following symlinks.
    method {:extern "NativePathExists"} {:axiom} NativePathExists(path: Path, followSymlink: bool) returns (found: bool, err: int)
      ensures C.PathExistsSpec(old(fs()), old(trustedFilesystem()), path, followSymlink, found, err)

    method PathExists(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      ensures C.PathExistsSpec(old(fs()), old(trustedFilesystem()), path, followSymlink, result.Ok?, C.ResultErrno(result))
    {
      var found, err := NativePathExists(path, followSymlink);
      if found {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to create an empty file at the given path.
    method {:extern "NativeCreateFile"} {:axiom} NativeCreateFile(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method CreateFile(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeCreateFile(path);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to write bytes to a regular file, creating or truncating it.
    method {:extern "NativeWriteFile"} {:axiom} NativeWriteFile(path: Path, data: Bytes)
      returns (ok: bool, err: int, committed: nat, stage: FileWriteStage)
      modifies fsRegion
      ensures C.WriteFileSpec(
                old(fs()),
                old(props()),
                old(now()),
                old(credentials()),
                old(trustedFilesystem()),
                fs(),
                path,
                data,
                ok,
                err,
                committed,
                stage
              )

    method WriteFile(path: Path, data: Bytes) returns (result: IOResult<WriteReceipt>)
      modifies fsRegion
      ensures C.WriteFileSpec(
                old(fs()),
                old(props()),
                old(now()),
                old(credentials()),
                old(trustedFilesystem()),
                fs(),
                path,
                data,
                result.Ok?,
                C.ResultErrno(result),
                C.WriteResultCommitted(result),
                C.WriteResultStage(result)
              )
    {
      var ok, err, committed, stage := NativeWriteFile(path, data);
      if ok {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(WriteFailure(err, message, committed, stage));
      }
    }

    // Opens for append and writes without reading or truncating the referent.
    method {:extern "NativeAppendFile"} {:axiom} NativeAppendFile(path: Path, data: Bytes)
      returns (ok: bool, err: int, committed: nat, stage: FileWriteStage)
      modifies fsRegion
      ensures C.AppendFileSpec(
                old(fs()), old(props()), old(now()), old(credentials()),
                old(trustedFilesystem()), fs(), path, data, ok, err, committed, stage
              )

    method AppendFile(path: Path, data: Bytes) returns (result: IOResult<WriteReceipt>)
      modifies fsRegion
      ensures C.AppendFileSpec(
                old(fs()), old(props()), old(now()), old(credentials()),
                old(trustedFilesystem()), fs(), path, data, result.Ok?, C.ResultErrno(result), C.WriteResultCommitted(result), C.WriteResultStage(result)
              )
    {
      var ok, err, committed, stage := NativeAppendFile(path, data);
      if ok {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(WriteFailure(err, message, committed, stage));
      }
    }

    // Attempts to create a symbolic link at path with the given raw target.
    method {:extern "NativeCreateSymlink"} {:axiom} NativeCreateSymlink(path: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateSymlinkSpec(old(fs()), old(now()), old(credentials()), fs(), path, target, ok, err)

    method CreateSymlink(path: Path, target: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateSymlinkSpec(old(fs()), old(now()), old(credentials()), fs(), path, target, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeCreateSymlink(path, target);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to delete a non-directory filesystem entry without following a terminal symlink.
    method {:extern "NativeDeletePath"} {:axiom} NativeDeletePath(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.DeletePathSpec(old(fs()), old(now()), fs(), path, ok, err)

    method DeletePath(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.DeletePathSpec(old(fs()), old(now()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeDeletePath(path);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates one directory. Recursive parent creation remains utility-owned.
    method {:extern "NativeCreateDirectory"} {:axiom} NativeCreateDirectory(path: Path, mode: bv32)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateDirectorySpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                old(umask()),
                fs(),
                path,
                mode,
                ok,
                err
              )

    method CreateDirectory(path: Path, mode: bv32) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateDirectorySpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                old(umask()),
                fs(),
                path,
                mode,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeCreateDirectory(path, mode);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Removes one empty directory without following a terminal symlink.
    method {:extern "NativeRemoveDirectory"} {:axiom} NativeRemoveDirectory(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RemoveDirectorySpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method RemoveDirectory(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.RemoveDirectorySpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeRemoveDirectory(path);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates a hard-link alias for an existing filesystem object.
    method {:extern "NativeCreateHardLink"} {:axiom} NativeCreateHardLink(source: Path, target: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateHardLinkSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                source,
                target,
                ok,
                err
              )

    method CreateHardLink(source: Path, target: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateHardLinkSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                source,
                target,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeCreateHardLink(source, target);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Performs exact libc unlink behavior without the legacy derived-success rule.
    method {:extern "NativeUnlinkPath"} {:axiom} NativeUnlinkPath(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.UnlinkPathSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method UnlinkPath(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.UnlinkPathSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeUnlinkPath(path);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Resizes one regular file, preserving the observed post-filesystem on failure.
    method {:extern "NativeTruncateFile"} {:axiom} NativeTruncateFile(path: Path, size: nat)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.TruncateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, size, ok, err)

    method TruncateFile(path: Path, size: nat) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.TruncateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, size, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeTruncateFile(path, size);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates one FIFO, block device, or character device node.
    method {:extern "NativeCreateSpecialNode"} {:axiom} NativeCreateSpecialNode(
      path: Path,
      kind: SpecialNodeKind,
      mode: bv32,
      major: nat,
      minor: nat
    ) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateSpecialNodeSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                old(umask()),
                fs(),
                path,
                kind,
                mode,
                major,
                minor,
                ok,
                err
              )

    method CreateSpecialNode(
      path: Path,
      kind: SpecialNodeKind,
      mode: bv32,
      major: nat,
      minor: nat
    ) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateSpecialNodeSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                old(umask()),
                fs(),
                path,
                kind,
                mode,
                major,
                minor,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeCreateSpecialNode(path, kind, mode, major, minor);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Requests global, file, data-only, or containing-filesystem synchronization.
    method {:extern "NativeSync"} {:axiom} NativeSync(target: SyncTarget, mode: SyncMode)
      returns (ok: bool, err: int)
      ensures C.SyncSpec(old(fs()), old(trustedFilesystem()), target, mode, ok, err)

    method Sync(target: SyncTarget, mode: SyncMode) returns (result: IOResult<Unit>)
      ensures C.SyncSpec(old(fs()), old(trustedFilesystem()), target, mode, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSync(target, mode);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update a file timestamp to the current time.
    method {:extern "NativeSetFileTimesNow"} {:axiom} NativeSetFileTimesNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileTimesNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                ok,
                err
              )

    method SetFileTimesNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileTimesNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileTimesNow(path, followSymlink);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the access timestamp to the current time.
    method {:extern "NativeSetFileAccessTimeNow"} {:axiom} NativeSetFileAccessTimeNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileAccessTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                ok,
                err
              )

    method SetFileAccessTimeNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileAccessTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileAccessTimeNow(path, followSymlink);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the modification timestamp to the current time.
    method {:extern "NativeSetFileModificationTimeNow"} {:axiom} NativeSetFileModificationTimeNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileModificationTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                ok,
                err
              )

    method SetFileModificationTimeNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileModificationTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileModificationTimeNow(path, followSymlink);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the access and modification timestamps for a file.
    method {:extern "NativeGetFileTimes"} {:axiom} NativeGetFileTimes(path: Path, followSymlink: bool)
      returns (
        ok: bool,
        atimeSec: int, atimeNsec: int,
        mtimeSec: int, mtimeNsec: int,
        isDir: bool, isSymlink: bool,
        device: int, inode: int, linkCount: int,
        err: int
      )
      ensures C.GetFileTimesSpec(
                old(fs()),
                old(trustedFilesystem()),
                path,
                followSymlink,
                ok,
                atimeSec,
                atimeNsec,
                mtimeSec,
                mtimeNsec,
                isDir,
                isSymlink,
                device,
                inode,
                linkCount,
                err
              )

    method GetFileTimes(path: Path, followSymlink: bool) returns (result: IOResult<FileTimeStatus>)
      ensures C.GetFileTimesSpec(
                old(fs()),
                old(trustedFilesystem()),
                path,
                followSymlink,
                result.Ok?,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeSec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeNsec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeSec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeNsec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isDir,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isSymlink,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).device,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).inode,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).linkCount,
                C.ResultErrno(result)
              )
    {
      var ok, atimeSec, atimeNsec, mtimeSec, mtimeNsec, isDir, isSymlink, device, inode, linkCount, err := NativeGetFileTimes(path, followSymlink);
      if ok {
        result := Result.Ok(FileTimeStatus(atimeSec, atimeNsec, mtimeSec, mtimeNsec, isDir, isSymlink, device, inode, linkCount));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update a file timestamp to explicit access and modification times.
    method {:extern "NativeSetFileTimes"} {:axiom} NativeSetFileTimes(
      path: Path,
      followSymlink: bool,
      atimeSec: int,
      atimeNsec: int,
      mtimeSec: int,
      mtimeNsec: int
    ) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileTimesSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                atimeSec,
                atimeNsec,
                mtimeSec,
                mtimeNsec,
                ok,
                err
              )

    method SetFileTimes(
      path: Path,
      followSymlink: bool,
      atimeSec: int,
      atimeNsec: int,
      mtimeSec: int,
      mtimeNsec: int
    ) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileTimesSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                atimeSec,
                atimeNsec,
                mtimeSec,
                mtimeNsec,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileTimes(path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update the stdout target timestamp to the current time.
    method {:extern "NativeSetStdoutTimesNow"} {:axiom} NativeSetStdoutTimesNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    method SetStdoutTimesNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutTimesNow();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the stdout target access timestamp to the current time.
    method {:extern "NativeSetStdoutAccessTimeNow"} {:axiom} NativeSetStdoutAccessTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutAccessTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    method SetStdoutAccessTimeNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutAccessTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutAccessTimeNow();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the stdout target modification timestamp to the current time.
    method {:extern "NativeSetStdoutModificationTimeNow"} {:axiom} NativeSetStdoutModificationTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutModificationTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    method SetStdoutModificationTimeNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutModificationTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutModificationTimeNow();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts the selected stdout timestamp updates, preserving fields requested as Keep.
    method {:extern "NativeSetStdoutTimes"} {:axiom} NativeSetStdoutTimes(
      atime: TimestampUpdate,
      mtime: TimestampUpdate
    ) returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), atime, mtime, ok, err)

    method SetStdoutTimes(
      atime: TimestampUpdate,
      mtime: TimestampUpdate
    ) returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), atime, mtime, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutTimes(atime, mtime);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the file mode for the given path.
    method {:extern "NativeGetFileMode"} {:axiom} NativeGetFileMode(path: Path, followSymlink: bool) returns (ok: bool, mode: bv32, err: int)
      ensures C.GetFileModeSpec(old(fs()), path, followSymlink, ok, mode, err)

    method GetFileMode(path: Path, followSymlink: bool) returns (result: IOResult<bv32>)
      ensures C.GetFileModeSpec(old(fs()), path, followSymlink, result.Ok?, C.ResultValue(result, 0 as bv32), C.ResultErrno(result))
    {
      var ok, mode, err := NativeGetFileMode(path, followSymlink);
      if ok {
        result := Result.Ok(mode);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads all modeled inode metadata for the given path.
    method {:extern "NativeGetFileStatus"} {:axiom} NativeGetFileStatus(
      path: Path,
      followSymlink: bool
    ) returns (ok: bool, status: FileStatus, err: int)
      modifies statusObservationsRegion
      ensures C.GetFileStatusSpec(
                statusObservations(), old(statusCursor()), statusCursor(),
                old(fs()), path, followSymlink, ok, status, err)

    method GetFileStatus(
      path: Path,
      followSymlink: bool
    ) returns (result: IOResult<FileStatus>)
      modifies statusObservationsRegion
      ensures C.GetFileStatusSpec(
                statusObservations(), old(statusCursor()), statusCursor(),
                old(fs()), path, followSymlink, result.Ok?, C.ResultValue(result, DEFAULT_FILE_STATUS), C.ResultErrno(result))
    {
      var ok, status, err := NativeGetFileStatus(path, followSymlink);
      if ok {
        result := Result.Ok(status);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to set the file mode for the given path.
    method {:extern "NativeSetFileMode"} {:axiom} NativeSetFileMode(path: Path, followSymlink: bool, mode: bv32) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileModeSpec(old(fs()), old(now()), fs(), path, followSymlink, mode, ok, err)

    method SetFileMode(path: Path, followSymlink: bool, mode: bv32) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileModeSpec(old(fs()), old(now()), fs(), path, followSymlink, mode, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetFileMode(path, followSymlink, mode);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Returns the current process umask value.
    method {:extern "GetUmask"} {:axiom} GetUmask() returns (mask: bv32)
      ensures C.GetUmaskSpec(old(props()), mask)

    // Opens a directory with or without dot entries and returns an iteration handle.
    method {:extern "NativeOpenDir"} {:axiom} NativeOpenDir(path: Path, includeDots: bool)
      returns (ok: bool, handle: int, err: int)
      modifies dirHandlesRegion
      ensures C.OpenDirSpec(old(fs()), old(dirHandles()), dirHandles(), path, includeDots, ok, handle, err)

    method OpenDir(path: Path, includeDots: bool) returns (result: IOResult<int>)
      modifies dirHandlesRegion
      ensures C.OpenDirSpec(old(fs()), old(dirHandles()), dirHandles(), path, includeDots, result.Ok?, C.ResultValue(result, 0), C.ResultErrno(result))
    {
      var ok, handle, err := NativeOpenDir(path, includeDots);
      if ok {
        result := Result.Ok(handle);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads metadata from an already opened directory descriptor.
    method {:extern "NativeGetOpenDirectoryStatus"} {:axiom} NativeGetOpenDirectoryStatus(handle: int)
      returns (ok: bool, status: FileStatus, err: int)
      modifies statusObservationsRegion
      ensures C.GetOpenDirectoryStatusSpec(
                statusObservations(), old(statusCursor()), statusCursor(),
                old(fs()), old(dirHandles()), handle, ok, status, err)

    method GetOpenDirectoryStatus(handle: int) returns (result: IOResult<FileStatus>)
      modifies statusObservationsRegion
      ensures C.GetOpenDirectoryStatusSpec(
                statusObservations(), old(statusCursor()), statusCursor(),
                old(fs()), old(dirHandles()), handle, result.Ok?, C.ResultValue(result, DEFAULT_FILE_STATUS), C.ResultErrno(result))
    {
      var ok, status, err := NativeGetOpenDirectoryStatus(handle);
      if ok {
        result := Result.Ok(status);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Resolves a path identity without opening or mutating the target.
    method {:extern "NativeResolvePathIdentity"} {:axiom} NativeResolvePathIdentity(path: Path)
      returns (ok: bool, resolvedPath: Path, err: int)
      ensures C.ResolvePathIdentitySpec(old(fs()), old(cwd()), path, ok, resolvedPath, err)

    method ResolvePathIdentity(path: Path) returns (result: IOResult<Path>)
      ensures C.ResolvePathIdentitySpec(old(fs()), old(cwd()), path, result.Ok?, C.ResultValue(result, ""), C.ResultErrno(result))
    {
      var ok, resolvedPath, err := NativeResolvePathIdentity(path);
      if ok {
        result := Result.Ok(resolvedPath);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the next native entry according to the handle's dot-entry mode.
    method {:extern "NativeReadDir"} {:axiom} NativeReadDir(handle: int)
      returns (hasMore: bool, name: string, kind: DirectoryEntryKind, err: int)
      modifies dirHandlesRegion
      ensures C.ReadDirSpec(
                old(fs()), old(dirHandles()), dirHandles(), handle,
                hasMore, name, kind, err)

    method ReadDir(handle: int) returns (result: IOResult<DirectoryRead>)
      modifies dirHandlesRegion
      ensures C.ReadDirSpec(
                old(fs()), old(dirHandles()), dirHandles(), handle,
                (result.Ok? && result.v.DirectoryItem?), (if result.Ok? && result.v.DirectoryItem? then result.v.name else ""), (if result.Ok? && result.v.DirectoryItem? then result.v.kind else UnknownDirentKind), C.ResultErrno(result))
    {
      var hasMore, name, kind, err := NativeReadDir(handle);
      if err == 0 {
        result := Result.Ok((if hasMore then DirectoryItem(name, kind) else DirectoryEnd));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Closes a directory handle and removes its tracked state.
    method {:extern "CloseDir"} {:axiom} CloseDir(handle: int)
      modifies dirHandlesRegion
      ensures C.CloseDirSpec(old(dirHandles()), dirHandles(), handle)

    // Checks whether a path refers to a directory; modeled paths must succeed.
    method {:extern "NativeIsDirectory"} {:axiom} NativeIsDirectory(path: Path, followSymlink: bool) returns (ok: bool, isDir: bool, err: int)
      ensures C.IsDirectorySpec(old(fs()), path, followSymlink, ok, isDir, err)

    method IsDirectory(path: Path, followSymlink: bool) returns (result: IOResult<bool>)
      ensures C.IsDirectorySpec(old(fs()), path, followSymlink, result.Ok?, C.ResultValue(result, false), C.ResultErrno(result))
    {
      var ok, isDir, err := NativeIsDirectory(path, followSymlink);
      if ok {
        result := Result.Ok(isDir);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Checks whether a path refers to a symlink.
    method {:extern "NativeIsSymlink"} {:axiom} NativeIsSymlink(path: Path) returns (ok: bool, isSymlink: bool, err: int)
      ensures C.IsSymlinkSpec(old(fs()), path, ok, isSymlink, err)

    method IsSymlink(path: Path) returns (result: IOResult<bool>)
      ensures C.IsSymlinkSpec(old(fs()), path, result.Ok?, C.ResultValue(result, false), C.ResultErrno(result))
    {
      var ok, isSymlink, err := NativeIsSymlink(path);
      if ok {
        result := Result.Ok(isSymlink);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Renames a filesystem entry, moving directory subtrees as a unit.
    method {:extern "NativeRenamePath"} {:axiom} NativeRenamePath(source: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RenamePathSpec(old(fs()), old(now()), fs(), source, target, ok, err)

    method RenamePath(source: Path, target: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.RenamePathSpec(old(fs()), old(now()), fs(), source, target, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeRenamePath(source, target);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

  }
}
