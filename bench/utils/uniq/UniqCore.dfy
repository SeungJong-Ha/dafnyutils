include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "UniqSchema.dfy"
include "UniqSpec.dfy"

module UniqCore {
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Spec = UniqSpec
  import UniqSchema

  // Deferred GNU behavior: non-"-" OUTPUT operands require file-content
  // write/truncate effects that are not currently exposed by BenchIO.IO.
  function InputFromOperands(
    operands: seq<string>
  ): UniqSchema.Input
  {
    if |operands| > 0 && operands[0] != "-" then
      UniqSchema.File(operands[0])
    else
      UniqSchema.Stdin
  } by method {
    return if |operands| > 0 && operands[0] != "-" then
        UniqSchema.File(operands[0])
      else
        UniqSchema.Stdin;
  }

  function Command(
    raw: UniqSchema.UniqCmdRaw
  ): UniqSchema.UniqCmd
  {
    var mode :=
      if raw.seenHelp &&
         (!raw.seenVersion ||
          raw.helpTokenIndex <= raw.versionTokenIndex) then
        UniqSchema.ModeHelp
      else if raw.seenVersion then
        UniqSchema.ModeVersion
      else if UniqSchema.UnsupportedSkipOperand(raw.operands) != "" then
        UniqSchema.ModeUnsupportedSkipChars(
          UniqSchema.UnsupportedSkipOperand(raw.operands)
        )
      else if |raw.operands| > 2 then
        UniqSchema.ModeExtraOperand(raw.operands[2])
      else if |raw.operands| == 2 && raw.operands[1] != "-" then
        UniqSchema.ModeUnsupportedOutput(raw.operands[1])
      else
        UniqSchema.ModeRun;
    UniqSchema.UniqCmd(
      mode,
      raw.seenCount,
      !raw.seenRepeated,
      !raw.seenUnique,
      raw.seenIgnoreCase,
      raw.skipFields,
      InputFromOperands(raw.operands)
    )
  } by method {
    var mode :=
      if raw.seenHelp &&
         (!raw.seenVersion ||
          raw.helpTokenIndex <= raw.versionTokenIndex) then
        UniqSchema.ModeHelp
      else if raw.seenVersion then
        UniqSchema.ModeVersion
      else if UniqSchema.UnsupportedSkipOperand(raw.operands) != "" then
        UniqSchema.ModeUnsupportedSkipChars(
          UniqSchema.UnsupportedSkipOperand(raw.operands)
        )
      else if |raw.operands| > 2 then
        UniqSchema.ModeExtraOperand(raw.operands[2])
      else if |raw.operands| == 2 && raw.operands[1] != "-" then
        UniqSchema.ModeUnsupportedOutput(raw.operands[1])
      else
        UniqSchema.ModeRun;
    return UniqSchema.UniqCmd(
        mode,
        raw.seenCount,
        !raw.seenRepeated,
        !raw.seenUnique,
        raw.seenIgnoreCase,
        raw.skipFields,
        InputFromOperands(raw.operands)
      );
  }

  function LowerAscii(ch: BenchWorld.RawByte): BenchWorld.RawByte
  {
    var code := ch as int;
    if ('A' as int) <= code <= ('Z' as int) then
      (code + (('a' as int) - ('A' as int))) as char
    else
      ch
  } by method {
    var code := ch as int;
    if ('A' as int) <= code <= ('Z' as int) {
      return (code + (('a' as int) - ('A' as int))) as char;
    } else {
      return ch;
    }
  }

  function EqualFoldAscii(
    a: BenchWorld.Bytes,
    b: BenchWorld.Bytes
  ): bool
    decreases |a|
  {
    if |a| != |b| then
      false
    else if |a| == 0 then
      true
    else
      LowerAscii(a[0]) == LowerAscii(b[0]) &&
      EqualFoldAscii(a[1..], b[1..])
  } by method {
    if |a| != |b| {
      return false;
    } else if |a| == 0 {
      return true;
    } else {
      return LowerAscii(a[0]) == LowerAscii(b[0]) &&
             EqualFoldAscii(a[1..], b[1..]);
    }
  }

  function IsFieldBlank(ch: BenchWorld.RawByte): bool
  {
    ch == ' ' || ch == '\t'
  }

  function SkipBlanks(line: BenchWorld.Bytes, i: nat): nat
    requires i <= |line|
    ensures i <= SkipBlanks(line, i) <= |line|
    ensures i < |line| && IsFieldBlank(line[i]) ==> i < SkipBlanks(line, i)
    ensures forall j: nat :: i <= j < SkipBlanks(line, i) ==> IsFieldBlank(line[j])
    ensures SkipBlanks(line, i) < |line| ==> !IsFieldBlank(line[SkipBlanks(line, i)])
    decreases |line| - i
  {
    if i < |line| && IsFieldBlank(line[i]) then SkipBlanks(line, i + 1) else i
  }

  function SkipNonBlanks(line: BenchWorld.Bytes, i: nat): nat
    requires i <= |line|
    ensures i <= SkipNonBlanks(line, i) <= |line|
    ensures i < |line| && !IsFieldBlank(line[i]) ==> i < SkipNonBlanks(line, i)
    ensures forall j: nat :: i <= j < SkipNonBlanks(line, i) ==> !IsFieldBlank(line[j])
    ensures SkipNonBlanks(line, i) < |line| ==> IsFieldBlank(line[SkipNonBlanks(line, i)])
    decreases |line| - i
  {
    if i < |line| && !IsFieldBlank(line[i]) then SkipNonBlanks(line, i + 1) else i
  }

  function SkipFieldsIndex(line: BenchWorld.Bytes, start: nat, count: nat): nat
    requires start <= |line|
    ensures start <= SkipFieldsIndex(line, start, count) <= |line|
    decreases count
  {
    if count == 0 || start == |line| then start
    else
      var afterBlanks := SkipBlanks(line, start);
      var afterField := SkipNonBlanks(line, afterBlanks);
      SkipFieldsIndex(line, afterField, count - 1)
  }

  function LinesEqual(
    cmd: UniqSchema.UniqCmd,
    a: BenchWorld.Bytes,
    b: BenchWorld.Bytes
  ): bool
  {
    var left := a[SkipFieldsIndex(a, 0, cmd.skipFields)..];
    var right := b[SkipFieldsIndex(b, 0, cmd.skipFields)..];
    if cmd.ignoreCase then EqualFoldAscii(left, right) else left == right
  } by method {
    var left := a[SkipFieldsIndex(a, 0, cmd.skipFields)..];
    var right := b[SkipFieldsIndex(b, 0, cmd.skipFields)..];
    if cmd.ignoreCase {
      return EqualFoldAscii(left, right);
    } else {
      return left == right;
    }
  }

  function LinesFrom(
    data: BenchWorld.Bytes,
    current: BenchWorld.Bytes
  ): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      if |current| == 0 then [] else [current]
    else if data[0] == '\n' then
      [current] + LinesFrom(data[1..], [])
    else
      LinesFrom(data[1..], current + [data[0]])
  } by method {
    if |data| == 0 {
      return if |current| == 0 then [] else [current];
    } else if data[0] == '\n' {
      return [current] + LinesFrom(data[1..], []);
    } else {
      return LinesFrom(data[1..], current + [data[0]]);
    }
  }

  function Lines(data: BenchWorld.Bytes): seq<BenchWorld.Bytes>
  {
    LinesFrom(data, [])
  } by method {
    return LinesFrom(data, []);
  }

  function GroupsFrom(
    cmd: UniqSchema.UniqCmd,
    rest: seq<BenchWorld.Bytes>,
    current: BenchWorld.Bytes,
    count: nat
  ): seq<Spec.Group>
    requires 1 <= count
    decreases |rest|
  {
    if |rest| == 0 then
      [Spec.Group(current, count)]
    else if LinesEqual(cmd, current, rest[0]) then
      GroupsFrom(cmd, rest[1..], current, count + 1)
    else
      [Spec.Group(current, count)] +
      GroupsFrom(cmd, rest[1..], rest[0], 1)
  } by method {
    if |rest| == 0 {
      return [Spec.Group(current, count)];
    } else if LinesEqual(cmd, current, rest[0]) {
      return GroupsFrom(cmd, rest[1..], current, count + 1);
    } else {
      return [Spec.Group(current, count)] +
        GroupsFrom(cmd, rest[1..], rest[0], 1);
    }
  }

  function Groups(
    cmd: UniqSchema.UniqCmd,
    lines: seq<BenchWorld.Bytes>
  ): seq<Spec.Group>
  {
    if |lines| == 0 then
      []
    else
      GroupsFrom(cmd, lines[1..], lines[0], 1)
  } by method {
    if |lines| == 0 {
      return [];
    } else {
      return GroupsFrom(cmd, lines[1..], lines[0], 1);
    }
  }

  function DigitChar(d: int): BenchWorld.RawByte
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  } by method {
    if 0 <= d < 10 {
      return (d + ('0' as int)) as char;
    } else {
      return '0';
    }
  }

  function Digits(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then
      [DigitChar(n as int)]
    else
      Digits(n / 10) + [DigitChar((n % 10) as int)]
  } by method {
    if n < 10 {
      return [DigitChar(n as int)];
    } else {
      return Digits(n / 10) + [DigitChar((n % 10) as int)];
    }
  }

  function PadLeft(
    text: BenchWorld.Bytes,
    width: int
  ): BenchWorld.Bytes
    decreases width - |text|
  {
    if |text| >= width then
      text
    else
      PadLeft([' '] + text, width)
  } by method {
    if |text| >= width {
      return text;
    } else {
      return PadLeft([' '] + text, width);
    }
  }

  function CountPrefix(count: nat): BenchWorld.Bytes
  {
    PadLeft(Digits(count), 7) + [' ']
  } by method {
    return PadLeft(Digits(count), 7) + [' '];
  }

  function ShouldOutputGroup(
    cmd: UniqSchema.UniqCmd,
    group: Spec.Group
  ): bool
  {
    (group.count == 1 && cmd.outputUnique) ||
    (group.count > 1 && cmd.outputRepeated)
  } by method {
    return (group.count == 1 && cmd.outputUnique) ||
           (group.count > 1 && cmd.outputRepeated);
  }

  function RenderGroup(
    cmd: UniqSchema.UniqCmd,
    group: Spec.Group
  ): BenchWorld.Bytes
  {
    if ShouldOutputGroup(cmd, group) then
      (if cmd.countOccurrences then CountPrefix(group.count) else []) +
      group.line + ['\n']
    else
      []
  } by method {
    if ShouldOutputGroup(cmd, group) {
      var prefix :=
        if cmd.countOccurrences then CountPrefix(group.count) else [];
      return prefix + group.line + ['\n'];
    } else {
      return [];
    }
  }

  function RenderGroups(
    cmd: UniqSchema.UniqCmd,
    groups: seq<Spec.Group>
  ): BenchWorld.Bytes
    decreases |groups|
  {
    if |groups| == 0 then
      []
    else
      RenderGroup(cmd, groups[0]) +
      RenderGroups(cmd, groups[1..])
  } by method {
    if |groups| == 0 {
      return [];
    } else {
      return RenderGroup(cmd, groups[0]) +
        RenderGroups(cmd, groups[1..]);
    }
  }

  function RenderData(
    cmd: UniqSchema.UniqCmd,
    data: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    RenderGroups(cmd, Groups(cmd, Lines(data)))
  } by method {
    return RenderGroups(cmd, Groups(cmd, Lines(data)));
  }

  function OutputForRead(
    cmd: UniqSchema.UniqCmd,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => RenderData(cmd, data)
    case Err(_) => []
  } by method {
    match result
    case Ok(data) => return RenderData(cmd, data);
    case Err(_) => return [];
  }

  function ErrorForRead(
    input: UniqSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ReadErrorMessageSpec(path, err)
  } by method {
    match input
    case Stdin => return [];
    case File(path) =>
      match result
      case Ok(_) => return [];
      case Err(err) => return Spec.ReadErrorMessageSpec(path, err);
  }

  function HadInputError(
    input: UniqSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): bool
  {
    match input
    case Stdin => false
    case File(_) => result.Err?
  } by method {
    match input
    case Stdin => return false;
    case File(_) => return result.Err?;
  }

  ghost predicate OutputRelation(
    cmd: UniqSchema.UniqCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    output == RenderData(cmd, data)
  }

  ghost predicate InputTraceRelation(
    cmd: UniqSchema.UniqCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
  {
    |readResults| == 1 &&
    match cmd.input
    case Stdin =>
      readResults[0] == Result.Ok(preStdin) &&
      OutputRelation(cmd, preStdin, stdoutPart) &&
      stderrPart == [] &&
      !hadError
    case File(path) =>
      readResults[0] == IOContract.ObservedReadFileResultFields(
        preFs, preStreams, path
      ) &&
      match readResults[0]
      case Ok(data) =>
        OutputRelation(cmd, data, stdoutPart) &&
        stderrPart == [] &&
        !hadError
      case Err(err) =>
        stdoutPart == [] &&
        stderrPart == Spec.ReadErrorMessageSpec(path, err) &&
        hadError
  }

  twostate predicate CoreSummary(
    raw: UniqSchema.UniqCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    new stdoutPart: BenchWorld.Bytes,
    new stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
    reads io.Footprint()
  {
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeUnsupportedOutput(path) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() ==
      old(io.stderr()) + Spec.UnsupportedOutputMessageSpec(path) &&
      exit == 1
    case ModeUnsupportedSkipChars(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() ==
      old(io.stderr()) + Spec.UnsupportedSkipCharsMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() ==
      old(io.stderr()) + Spec.ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeRun =>
      InputTraceRelation(
        cmd,
        old(io.fs()),
        old(io.stdin()),
        old(io.trustedStreams()),
        readResults,
        stdoutPart,
        stderrPart,
        hadError
      ) &&
      io.stdin() ==
      (match cmd.input
       case Stdin => IOContract.AfterReadStdinFields(old(io.stdin()))
       case File(_) => old(io.stdin())) &&
      io.stdout() == old(io.stdout()) + stdoutPart &&
      io.stderr() == old(io.stderr()) + stderrPart &&
      exit == (if hadError then 1 else 0)
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method UnsupportedOutputMessage(
    path: BenchWorld.Path
  ) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.UnsupportedOutputMessageSpec(path)
  {
    msg := Spec.UnsupportedOutputMessageSpec(path);
  }

  method UnsupportedSkipCharsMessage(
    operand: string
  ) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.UnsupportedSkipCharsMessageSpec(operand)
  {
    msg := Spec.UnsupportedSkipCharsMessageSpec(operand);
  }

  method ExtraOperandMessage(
    operand: string
  ) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.ExtraOperandMessageSpec(operand)
  {
    msg := Spec.ExtraOperandMessageSpec(operand);
  }

  method {:isolate_assertions} RunCore(
    raw: UniqSchema.UniqCmdRaw,
    io: BenchIO.IO
  ) returns (
      exit: int,
      ghost witnessResult: BenchWorld.IOResult<BenchWorld.Bytes>,
                                             ghost stdoutPart: BenchWorld.Bytes,
                                             ghost stderrPart: BenchWorld.Bytes,
                                             ghost hadError: bool
    )
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(
              raw, io, exit, [witnessResult], stdoutPart, stderrPart, hadError
            )
    decreases *
  {
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    witnessResult := Result.Ok([]);
    stdoutPart := [];
    stderrPart := [];
    hadError := false;
    var cmd := Command(raw);

    match cmd.mode {
      case ModeHelp =>
        var help := GetHelpText();
        var _ := io.WriteStdout(help, BenchWorld.ThrowOnError);
        exit := 0;
        assert io.stdin() == preStdin;
        assert io.stderr() == preStderr;
        assert io.stdout() == preStdout + Spec.HelpTextSpec();
        return;

      case ModeVersion =>
        var version := GetVersionText();
        var _ := io.WriteStdout(version, BenchWorld.ThrowOnError);
        exit := 0;
        assert io.stdin() == preStdin;
        assert io.stderr() == preStderr;
        assert io.stdout() == preStdout + Spec.VersionTextSpec();
        return;

      case ModeUnsupportedOutput(path) =>
        var msg := UnsupportedOutputMessage(path);
        var _ := io.WriteStderr(msg, BenchWorld.ThrowOnError);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() ==
               preStderr + Spec.UnsupportedOutputMessageSpec(path);
        return;

      case ModeUnsupportedSkipChars(operand) =>
        var msg := UnsupportedSkipCharsMessage(operand);
        var _ := io.WriteStderr(msg, BenchWorld.ThrowOnError);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() ==
               preStderr + Spec.UnsupportedSkipCharsMessageSpec(operand);
        return;

      case ModeExtraOperand(operand) =>
        var msg := ExtraOperandMessage(operand);
        var _ := io.WriteStderr(msg, BenchWorld.ThrowOnError);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() ==
               preStderr + Spec.ExtraOperandMessageSpec(operand);
        return;

      case ModeRun =>
        var result: BenchWorld.IOResult<BenchWorld.Bytes>;
        match cmd.input {
          case Stdin =>
            var data :- assert io.ReadStdin(BenchWorld.ThrowOnError);
            result := Result.Ok(data);
          case File(path) =>
            result := io.ReadFile(path);
        }

        var out := OutputForRead(cmd, result);
        var err := ErrorForRead(cmd.input, result);
        var inputHadError := HadInputError(cmd.input, result);
        witnessResult := result;
        stdoutPart := out;
        stderrPart := err;
        hadError := inputHadError;
        var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
        var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
        exit := if inputHadError then 1 else 0;
        reveal InputTraceRelation();
               reveal OutputRelation();
                      return;
    }
  }
}
