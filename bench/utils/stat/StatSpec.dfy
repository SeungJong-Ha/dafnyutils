include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "StatSchema.dfy"

module StatSpec {
  import BenchWorld
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = StatSchema
  import SE = StringEscaping

  datatype CapturedStatus = CapturedStatusOk(
                              path: BenchWorld.Path,
                              followSymlink: bool,
                              status: BenchWorld.FileStatus
                            )
                          | CapturedStatusErr(
                              path: BenchWorld.Path,
                              followSymlink: bool,
                              errno: int
                            )

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: stat [OPTION]... FILE...\n"
    + "Display numeric file status using a required format.\n"
    + "\n"
    + "  -L, --dereference     follow links\n"
    + "  -c, --format=FORMAT   use FORMAT; append a newline after each result\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "Supported directives: %a %b %B %d %D %f %g %h %i %o %s %u %X %Y %Z %%\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "stat (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Michael Meskes.\n"
  }

  function MissingFormatMessageSpec(): BenchWorld.Bytes
  {
    "stat: a format is required in this benchmark\nTry 'stat --help' for more information.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "stat: missing operand\nTry 'stat --help' for more information.\n"
  }

  function ErrnoTextSpec(errno: int): string
  {
    if errno == 2 then "No such file or directory"
    else if errno == 13 then "Permission denied"
    else if errno == 20 then "Not a directory"
    else if errno == 40 then "Too many levels of symbolic links"
    else "unknown error"
  }

  function ErrorMessageSpec(path: BenchWorld.Path, errno: int): BenchWorld.Bytes
  {
    "stat: cannot statx " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ": " + ErrnoTextSpec(errno) + "\n"
  }

  function DigitForBaseSpec(digit: nat): char
    requires digit < 16
  {
    if digit < 10 then
      (('0' as int) + digit) as char
    else
      (('a' as int) + digit - 10) as char
  }

  function BaseNatTextSpec(value: nat, base: nat): string
    requires 2 <= base <= 16
    decreases value
  {
    if value < base then
      [DigitForBaseSpec(value)]
    else
      BaseNatTextSpec(value / base, base) + [DigitForBaseSpec(value % base)]
  }

  function IntTextSpec(value: int): string
  {
    if value < 0 then "-" + BaseNatTextSpec((-value) as nat, 10)
    else BaseNatTextSpec(value as nat, 10)
  }

  function IntHexTextSpec(value: int): string
  {
    if value < 0 then "-" + BaseNatTextSpec((-value) as nat, 16)
    else BaseNatTextSpec(value as nat, 16)
  }

  function RawModeValueSpec(status: BenchWorld.FileStatus): nat
  {
    var kindBits :=
      if status.kind == BenchWorld.RegularKind then 32768
      else if status.kind == BenchWorld.DirectoryKind then 16384
      else if status.kind == BenchWorld.SymlinkKind then 40960
      else if status.kind == BenchWorld.BlockDeviceKind then 24576
      else if status.kind == BenchWorld.CharacterDeviceKind then 8192
      else if status.kind == BenchWorld.FifoKind then 4096
      else 49152;
    kindBits + (status.mode as int) as nat
  }

  function SupportedDirectiveSpec(directive: char): bool
  {
    directive == '%' || directive == 'a' || directive == 'b' || directive == 'B' ||
    directive == 'd' || directive == 'D' || directive == 'f' || directive == 'g' ||
    directive == 'h' || directive == 'i' || directive == 'o' || directive == 's' ||
    directive == 'u' || directive == 'X' || directive == 'Y' || directive == 'Z'
  }

  function DirectiveTextSpec(
    directive: char,
    status: BenchWorld.FileStatus
  ): BenchWorld.Bytes
  {
    Utf8.Encode(if directive == '%' then "%"
    else if directive == 'a' then BaseNatTextSpec((status.mode as int) as nat, 8)
    else if directive == 'b' then BaseNatTextSpec(status.storage.allocatedBlocks, 10)
    else if directive == 'B' then BaseNatTextSpec(BenchWorld.STAT_BLOCK_BYTES, 10)
    else if directive == 'd' then IntTextSpec(status.hostKey.device)
    else if directive == 'D' then IntHexTextSpec(status.hostKey.device)
    else if directive == 'f' then BaseNatTextSpec(RawModeValueSpec(status), 16)
    else if directive == 'g' then BaseNatTextSpec(status.ownership.gid, 10)
    else if directive == 'h' then BaseNatTextSpec(status.linkCount, 10)
    else if directive == 'i' then IntTextSpec(status.hostKey.inode)
    else if directive == 'o' then BaseNatTextSpec(status.storage.preferredIoBlockBytes, 10)
    else if directive == 's' then BaseNatTextSpec(status.storage.size, 10)
    else if directive == 'u' then BaseNatTextSpec(status.ownership.uid, 10)
    else if directive == 'X' then IntTextSpec(status.times.atimeSec)
    else if directive == 'Y' then IntTextSpec(status.times.mtimeSec)
    else if directive == 'Z' then IntTextSpec(status.times.ctimeSec)
    else "?")
  }

  ghost predicate FormatStepRelation(
    format: string,
    status: BenchWorld.FileStatus,
    lo: nat,
    hi: nat,
    piece: BenchWorld.Bytes
  )
  {
    lo < |format| &&
    if format[lo] != '%' then
      hi == lo + 1 && piece == Utf8.EncodeChar(format[lo])
    else if lo + 1 == |format| then
      hi == lo + 1 && piece == "%"
    else
      lo + 1 < |format| && hi == lo + 2 &&
      piece == DirectiveTextSpec(format[lo + 1], status)
  }

  function ConcatPiecesSpec(pieces: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |pieces|
  {
    if |pieces| == 0 then []
    else pieces[0] + ConcatPiecesSpec(pieces[1..])
  }

  ghost predicate PrefixRenderingWitnessRelation(
    format: string,
    status: BenchWorld.FileStatus,
    end: nat,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    end <= |format| &&
    |cuts| == |pieces| + 1 &&
    |cuts| > 0 &&
    cuts[0] == 0 &&
    cuts[|pieces|] == end &&
    (forall i: nat {:trigger cuts[i]} | i < |pieces| ::
       FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])) &&
    rendered == ConcatPiecesSpec(pieces)
  }

  ghost predicate RenderingWitnessRelation(
    format: string,
    status: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    PrefixRenderingWitnessRelation(format, status, |format|, rendered, cuts, pieces)
  }

  ghost predicate FormatRenderingRelation(
    format: string,
    status: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes
  )
  {
    exists cuts: seq<nat>, pieces: seq<BenchWorld.Bytes> ::
      RenderingWitnessRelation(format, status, rendered, cuts, pieces)
  }

  ghost predicate FormatValidSpec(format: string)
  {
    exists status: BenchWorld.FileStatus, rendered: BenchWorld.Bytes ::
      FormatRenderingRelation(format, status, rendered)
  }

  ghost predicate StatusObservationRelation(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    followSymlink: bool,
    result: BenchWorld.Result<BenchWorld.FileStatus>
  )
  {
    result == IOContract.GetFileStatusResultFields(fs, path, followSymlink)
  }

  ghost predicate FileFragmentRelation(
    format: string,
    path: BenchWorld.Path,
    result: BenchWorld.Result<BenchWorld.FileStatus>,
                              stdoutFragment: BenchWorld.Bytes,
                              stderrFragment: BenchWorld.Bytes
  )
  {
    match result
    case Ok(status) =>
      exists rendered: BenchWorld.Bytes ::
        FormatRenderingRelation(format, status, rendered) &&
        stdoutFragment == rendered + "\n" && stderrFragment == ""
    case Err(error) =>
      stdoutFragment == "" && stderrFragment == ErrorMessageSpec(path, IOContract.IOErrorErrno(error))
  }

  ghost predicate OutputFragmentCutsRelation(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 && cuts[0] == 0 && cuts[|fragments|] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |output| &&
      output[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost function StatusResultSpec(
    cmd: Schema.StatCmd, fs: BenchWorld.FileSystem, index: nat,
    path: BenchWorld.Path
  ): BenchWorld.Result<BenchWorld.FileStatus>
  {
    match cmd.statusContext
    case UnboundStatusObservations => IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink)
    case BoundStatusObservations(observations, firstStatus) =>
      IOContract.ObservedFileStatusResultFields(observations, firstStatus + index,
                                                fs, path, cmd.followSymlink)
  }

  ghost predicate RunFilesRelation(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    exists stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes> ::
      |stdoutFragments| == |files| &&
      |stderrFragments| == |files| &&
      (forall i: nat | i < |files| ::
         FileFragmentRelation(
           cmd.format,
           files[i],
           StatusResultSpec(cmd, fs, i, files[i]),
           stdoutFragments[i],
           stderrFragments[i]
         )) &&
      hadError == (exists i: nat ::
                     i < |files| &&
                     StatusResultSpec(cmd, fs, i, files[i]).Err?) &&
      out == ConcatPiecesSpec(stdoutFragments) &&
      errOut == ConcatPiecesSpec(stderrFragments)
  }

  ghost predicate CapturedStatusesStructureRelation(
    cmd: Schema.StatCmd,
    fs: BenchWorld.FileSystem,
    captured: seq<CapturedStatus>
  )
  {
    CapturedRequestsSpec(cmd, captured) &&
    forall i: nat | i < |captured| ::
      match captured[i]
      case CapturedStatusOk(path, followSymlink, status) =>
        path == cmd.files[i] && followSymlink == cmd.followSymlink &&
        IOContract.FileStatusStructureContractFields(
          fs, path, followSymlink, true, status, 0)
      case CapturedStatusErr(path, followSymlink, errno) =>
        path == cmd.files[i] && followSymlink == cmd.followSymlink &&
        IOContract.FileStatusStructureContractFields(
          fs, path, followSymlink, false,
          BenchWorld.DEFAULT_FILE_STATUS, errno)
  }

  ghost predicate CapturedRequestsSpec(
    cmd: Schema.StatCmd,
    captured: seq<CapturedStatus>
  )
  {
    |captured| == (if cmd.mode == Schema.ModeRun then |cmd.files| else 0) &&
    forall i: nat | i < |captured| ::
      captured[i].path == cmd.files[i] &&
      captured[i].followSymlink == cmd.followSymlink
  }

  ghost predicate RunCapturedFilesRelation(
    cmd: Schema.StatCmd,
    captured: seq<CapturedStatus>,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    |captured| <= |cmd.files| &&
    exists stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes> ::
      |stdoutFragments| == |captured| &&
      |stderrFragments| == |captured| &&
      (forall i: nat | i < |captured| ::
         match captured[i]
         case CapturedStatusOk(_, _, status) =>
           exists rendered: BenchWorld.Bytes ::
             FormatRenderingRelation(cmd.format, status, rendered) &&
             stdoutFragments[i] == rendered + "\n" && stderrFragments[i] == ""
         case CapturedStatusErr(_, _, errno) =>
           stdoutFragments[i] == "" &&
           stderrFragments[i] == ErrorMessageSpec(cmd.files[i], errno)) &&
      hadError == (exists i: nat :: i < |captured| && captured[i].CapturedStatusErr?) &&
      out == ConcatPiecesSpec(stdoutFragments) &&
      errOut == ConcatPiecesSpec(stderrFragments)
  }

  ghost predicate CapturedOutputSpec(
    raw: Schema.StatCmdRaw,
    captured: seq<CapturedStatus>,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int
  )
  {
    var cmd := Schema.Command(raw);
    |captured| == (if cmd.mode == Schema.ModeRun then |cmd.files| else 0) &&
    if cmd.mode == Schema.ModeHelp then
      afterStdout == beforeStdout + HelpTextSpec() && afterStderr == beforeStderr && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      afterStdout == beforeStdout + VersionTextSpec() && afterStderr == beforeStderr && exit == 0
    else if cmd.mode == Schema.ModeMissingFormat then
      afterStdout == beforeStdout &&
      afterStderr == beforeStderr + MissingFormatMessageSpec() && exit == 1
    else if cmd.mode == Schema.ModeMissingOperand then
      afterStdout == beforeStdout &&
      afterStderr == beforeStderr + MissingOperandMessageSpec() && exit == 1
    else
      FormatValidSpec(cmd.format) &&
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunCapturedFilesRelation(cmd, captured, hadError, out, errOut) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + errOut &&
        exit == (if hadError then 1 else 0)
  }

  // Executable evaluator checkers establish the finite output relation while
  // the exact trace projection establishes its structural request relation.
  // The proof module then constructs the ordered observation provider and
  // connects both parts back to ObservedSpec.
  ghost predicate ObservedResultsSpec(
    raw: Schema.StatCmdRaw,
    fs: BenchWorld.FileSystem,
    captured: seq<CapturedStatus>,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int
  )
  {
    CapturedStatusesStructureRelation(Schema.Command(raw), fs, captured) &&
    CapturedOutputSpec(
      raw, captured, beforeStdout, afterStdout,
      beforeStderr, afterStderr, exit)
  }

  // The same observable relation is available to exact execution classifiers.
  ghost predicate ObservedSpec(
    raw: Schema.StatCmdRaw,
    fs: BenchWorld.FileSystem,
    observations: BenchWorld.StatusTimeObservations,
    firstStatus: nat,
    afterStatus: nat,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int
  )
  {
    var cmd := Schema.WithStatusObservations(Schema.Command(raw), observations, firstStatus);
    afterStatus == firstStatus + (if cmd.mode == Schema.ModeRun then |cmd.files| else 0) &&
    if cmd.mode == Schema.ModeHelp then
      afterStdout == beforeStdout + HelpTextSpec() && afterStderr == beforeStderr && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      afterStdout == beforeStdout + VersionTextSpec() && afterStderr == beforeStderr && exit == 0
    else if cmd.mode == Schema.ModeMissingFormat then
      afterStdout == beforeStdout &&
      afterStderr == beforeStderr + MissingFormatMessageSpec() && exit == 1
    else if cmd.mode == Schema.ModeMissingOperand then
      afterStdout == beforeStdout &&
      afterStderr == beforeStderr + MissingOperandMessageSpec() && exit == 1
    else
      FormatValidSpec(cmd.format) &&
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesRelation(cmd, cmd.files, fs, hadError, out, errOut) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + errOut &&
        exit == (if hadError then 1 else 0)
  }

  twostate predicate Spec(raw: Schema.StatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
  {
    ObservedSpec(raw, old(io.fs()), io.statusObservations(), old(io.statusCursor()), io.statusCursor(),
                 old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit)
  }
}
