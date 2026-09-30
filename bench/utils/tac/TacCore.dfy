include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/CliTypes.dfy"
include "TacSchema.dfy"
include "TacSpec.dfy"

module TacCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes
  import IOContract
  import TacSchema
  import Spec = TacSpec

  function InputsFromOperands(operands: seq<string>): seq<TacSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then TacSchema.Stdin else TacSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method
  {
    if |operands| == 0 {
      return [];
    }
    var head := if operands[0] == "-" then TacSchema.Stdin else TacSchema.File(operands[0]);
    return [head] + InputsFromOperands(operands[1..]);
  }

  function SeparatorValue(raw: CliTypes.OptionalString): BenchWorld.Bytes
    ensures |SeparatorValue(raw)| > 0
  {
    match raw
    case Some(value) => if value == "" then ['\0'] else Utf8.Encode(value)
    case None => ['\n']
  } by method
  {
    match raw
    case Some(value) =>
      return if value == "" then ['\0'] else Utf8.Encode(value);
    case None =>
      return ['\n'];
  }

  function Command(raw: TacSchema.TacCmdRaw): TacSchema.TacCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        TacSchema.ModeHelp
      else if raw.seenVersion then
        TacSchema.ModeVersion
      else
        TacSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == TacSchema.ModeRun && |inputs| == 0 then [TacSchema.Stdin] else inputs;
    TacSchema.TacCmd(mode, raw.seenBefore, SeparatorValue(raw.separator), runInputs)
  } by method
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        TacSchema.ModeHelp
      else if raw.seenVersion then
        TacSchema.ModeVersion
      else
        TacSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == TacSchema.ModeRun && |inputs| == 0 then [TacSchema.Stdin] else inputs;
    return TacSchema.TacCmd(mode, raw.seenBefore, SeparatorValue(raw.separator), runInputs);
  }

  ghost function PrefixStdin(cmd: TacSchema.TacCmd, preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin => []
      case File(_) => PrefixStdin(cmd, preStdin, i - 1)
  }

  ghost function ReadResult(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Result<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin => BenchWorld.Ok(PrefixStdin(cmd, preStdin, i))
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function SearchLimit(pastEnd: nat, sep: BenchWorld.Bytes): nat
    requires |sep| > 0
  {
    if pastEnd < |sep| then 0 else pastEnd - |sep| + 1
  } by method
  {
    return if pastEnd < |sep| then 0 else pastEnd - |sep| + 1;
  }

  function MatchAt(data: BenchWorld.Bytes, sep: BenchWorld.Bytes, start: int): bool
    requires |sep| > 0
  {
    0 <= start && start + |sep| <= |data| && data[start..start + |sep|] == sep
  } by method
  {
    return 0 <= start &&
           start + |sep| <= |data| &&
           data[start..start + |sep|] == sep;
  }

  function BackedLimit(start: nat, sep: BenchWorld.Bytes): nat
    requires |sep| > 0
  {
    if start < |sep| then 0 else start - |sep| + 1
  } by method
  {
    return if start < |sep| then 0 else start - |sep| + 1;
  }

  ghost predicate ValidStarts(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    starts: seq<nat>
  )
  {
    (forall i: nat {:trigger starts[i]} | i < |starts| ::
       starts[i] + |sep| <= |data| &&
       data[starts[i]..starts[i] + |sep|] == sep) &&
    (forall i: nat {:trigger starts[i], starts[i + 1]} | i + 1 < |starts| ::
       starts[i] + |sep| <= starts[i + 1])
  }

  function SelectedStartsScan(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    limit: nat
  ): seq<nat>
    requires |sep| > 0
    requires limit <= SearchLimit(|data|, sep)
    ensures ValidStarts(data, sep, SelectedStartsScan(data, sep, limit))
    ensures forall i: nat {:trigger SelectedStartsScan(data, sep, limit)[i]} |
              i < |SelectedStartsScan(data, sep, limit)| ::
              SelectedStartsScan(data, sep, limit)[i] < limit
    decreases limit
  {
    if limit == 0 then
      []
    else if MatchAt(data, sep, limit - 1) then
      SelectedStartsScan(data, sep, BackedLimit(limit - 1, sep)) + [limit - 1]
    else
      SelectedStartsScan(data, sep, limit - 1)
  } by method
  {
    if limit == 0 {
      return [];
    }
    var candidate := limit - 1;
    if MatchAt(data, sep, candidate) {
      var nextLimit := BackedLimit(candidate, sep);
      return SelectedStartsScan(data, sep, nextLimit) + [candidate];
    }
    return SelectedStartsScan(data, sep, limit - 1);
  }

  function SelectedStarts(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes
  ): seq<nat>
    requires |sep| > 0
    ensures ValidStarts(data, sep, SelectedStarts(data, sep))
  {
    SelectedStartsScan(data, sep, SearchLimit(|data|, sep))
  } by method
  {
    return SelectedStartsScan(data, sep, SearchLimit(|data|, sep));
  }

  function InputCuts(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    before: bool,
    starts: seq<nat>
  ): seq<nat>
    requires |sep| > 0
    requires ValidStarts(data, sep, starts)
  {
    [0] +
    seq(
    |starts|,
    i requires 0 <= i < |starts| =>
      starts[i] + (if before then 0 else |sep|)
      ) +
    [|data|]
  } by method
  {
    var cuts := [0];
    var i := 0;
    while i < |starts|
      invariant 0 <= i <= |starts|
      invariant cuts == [0] +
                        seq(
                        i,
                        j requires 0 <= j < i =>
                          starts[j] + (if before then 0 else |sep|)
                          )
      decreases |starts| - i
    {
      cuts := cuts + [starts[i] + (if before then 0 else |sep|)];
      i := i + 1;
    }
    return cuts + [|data|];
  }

  function ReverseIntervals(
    data: BenchWorld.Bytes,
    cuts: seq<nat>,
    count: nat
  ): BenchWorld.Bytes
    requires 0 < |cuts|
    requires count < |cuts|
    decreases count
  {
    if count == 0 then
      []
    else if cuts[count - 1] > cuts[count] || cuts[count] > |data| then
      []
    else
      data[cuts[count - 1]..cuts[count]] +
      ReverseIntervals(data, cuts, count - 1)
  } by method
  {
    if count == 0 {
      return [];
    } else if cuts[count - 1] > cuts[count] || cuts[count] > |data| {
      return [];
    }
    return data[cuts[count - 1]..cuts[count]] +
      ReverseIntervals(data, cuts, count - 1);
  }

  function ReverseRecords(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    before: bool
  ): BenchWorld.Bytes
    requires |sep| > 0
  {
    var starts := SelectedStarts(data, sep);
    var cuts := InputCuts(data, sep, before, starts);
    ReverseIntervals(data, cuts, |cuts| - 1)
  } by method
  {
    var starts := SelectedStarts(data, sep);
    var cuts := InputCuts(data, sep, before, starts);
    return ReverseIntervals(data, cuts, |cuts| - 1);
  }

  ghost function OutputPiece(
    cmd: TacSchema.TacCmd,
    result: BenchWorld.Result<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    requires |cmd.separator| > 0
  {
    match result
    case Ok(data) => ReverseRecords(data, cmd.separator, cmd.before)
    case Err(_) => []
  }

  ghost function PrefixOutput(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    requires |cmd.separator| > 0
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutput(cmd, preFs, preStreams, preStdin, i - 1) +
      OutputPiece(cmd, ReadResult(cmd, preFs, preStreams, preStdin, i - 1))
  }

  ghost function PrefixErrorOutput(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorOutput(cmd, preFs, preStreams, preStdin, i - 1) +
      Spec.ErrorPiece(cmd.inputs[i - 1], ReadResult(cmd, preFs, preStreams, preStdin, i - 1), preFs, preStreams)
  }

  ghost function PrefixHadError(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadError(cmd, preFs, preStreams, preStdin, i - 1) ||
      Spec.HadErrorPiece(cmd.inputs[i - 1], ReadResult(cmd, preFs, preStreams, preStdin, i - 1))
  }

  twostate predicate CoreSummary(raw: TacSchema.TacCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == TacSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TacSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      io.stdin() == PrefixStdin(cmd, old(io.stdin()), |cmd.inputs|) &&
      io.stdout() == old(io.stdout()) + PrefixOutput(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) &&
      io.stderr() == old(io.stderr()) + PrefixErrorOutput(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) &&
      exit == (if PrefixHadError(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) then 1 else 0)
  }

  lemma PrefixStdinCoreStep(cmd: TacSchema.TacCmd, preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures PrefixStdin(cmd, preStdin, i + 1) ==
            match cmd.inputs[i]
            case Stdin => IOContract.AfterReadStdinFields(PrefixStdin(cmd, preStdin, i))
            case File(_) => PrefixStdin(cmd, preStdin, i)
  {
  }

  lemma PrefixOutputCoreStep(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    requires |cmd.separator| > 0
    ensures PrefixOutput(cmd, preFs, preStreams, preStdin, i + 1) ==
            PrefixOutput(cmd, preFs, preStreams, preStdin, i) +
            OutputPiece(cmd, ReadResult(cmd, preFs, preStreams, preStdin, i))
  {
  }

  lemma PrefixErrorOutputCoreStep(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixErrorOutput(cmd, preFs, preStreams, preStdin, i + 1) ==
            PrefixErrorOutput(cmd, preFs, preStreams, preStdin, i) +
            Spec.ErrorPiece(cmd.inputs[i], ReadResult(cmd, preFs, preStreams, preStdin, i), preFs, preStreams)
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadError(cmd, preFs, preStreams, preStdin, i + 1) ==
            (PrefixHadError(cmd, preFs, preStreams, preStdin, i) ||
             Spec.HadErrorPiece(cmd.inputs[i], ReadResult(cmd, preFs, preStreams, preStdin, i)))
  {
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

  method GetErrnoText(err: BenchWorld.IOError) returns (text: string)
    ensures text == Spec.ErrnoText(err)
  {
    text := Spec.ErrnoText(err);
  }

  method ErrorMessageMethod(path: BenchWorld.Path, err: BenchWorld.IOError) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.ErrorMessageSpec(path, err)
  {
    msg := Spec.ErrorMessageSpec(path, err);
  }

  method {:isolate_assertions} RunCore(raw: TacSchema.TacCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var preStreams := io.trustedStreams();
    var cmd := Command(raw);

    if cmd.mode == TacSchema.ModeHelp {
      var help := GetHelpText();
      var _, _ := io.WriteStdout(help, BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == TacSchema.ModeVersion {
      var version := GetVersionText();
      var _, _ := io.WriteStdout(version, BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var output: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant io.stdin() == PrefixStdin(cmd, preStdin, i)
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant output == PrefixOutput(cmd, preFs, preStreams, preStdin, i)
      invariant err == PrefixErrorOutput(cmd, preFs, preStreams, preStdin, i)
      invariant hadError == PrefixHadError(cmd, preFs, preStreams, preStdin, i)
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      var readResult: BenchWorld.Result<BenchWorld.Bytes>;
      match input {
        case Stdin =>
          ghost var beforeStdin := io.stdin();
          var data, _ := io.ReadStdin(BenchWorld.ThrowOnError);
          readResult := BenchWorld.Ok(data);
          PrefixStdinCoreStep(cmd, preStdin, i);
          assert beforeStdin == PrefixStdin(cmd, preStdin, i);
          assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
          assert readResult == ReadResult(cmd, preFs, preStreams, preStdin, i);
          var piece := ReverseRecords(data, cmd.separator, cmd.before);
          output := output + piece;
        case File(path) =>
          var readData, readErr, readStage := io.ReadFile(path, BenchWorld.FromStart);
          readResult := IOContract.FileReadResultFromOutcome(readData, readErr);
          assert readResult == IOContract.ObservedReadFileResultFields(preFs, preStreams, path);
          assert readResult == ReadResult(cmd, preFs, preStreams, preStdin, i);
          if readResult.Ok? {
            var piece := ReverseRecords(readResult.v, cmd.separator, cmd.before);
            output := output + piece;
          } else {
            hadError := true;
            var msg: BenchWorld.Bytes;
            if readResult.e == BenchWorld.IsDirectory {
              var ignored, dirErr, stage := io.ReadFile(path, BenchWorld.AfterSeekEnd);
              assert IOContract.TrustedReadFileContractFields(
                preStreams, preFs, path, BenchWorld.AfterSeekEnd, ignored, dirErr, stage
              );
              assert Spec.DirectoryReadOutcome(preStreams, preFs, path) ==
                BenchWorld.StreamReadFileResult(ignored, dirErr, stage);
              var dirText := io.GetCLocaleErrnoText(dirErr);
              msg := if stage == BenchWorld.OpenFailed then
                Spec.DirectoryOpenErrorMessageSpec(path, dirText)
                else Spec.DirectoryReadErrorMessageSpec(path, dirText);
            } else {
              msg := ErrorMessageMethod(path, readResult.e);
            }
            assert msg == Spec.ErrorPiece(input, readResult, preFs, preStreams);
            err := err + msg;
          }
      }
      assert err == PrefixErrorOutput(cmd, preFs, preStreams, preStdin, i) +
                    Spec.ErrorPiece(input, readResult, preFs, preStreams);
      PrefixOutputCoreStep(cmd, preFs, preStreams, preStdin, i);
      PrefixErrorOutputCoreStep(cmd, preFs, preStreams, preStdin, i);
      PrefixHadErrorCoreStep(cmd, preFs, preStreams, preStdin, i);
      i := i + 1;
    }

    assert output == PrefixOutput(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
    assert err == PrefixErrorOutput(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
    assert hadError == PrefixHadError(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
    var _, _ := io.WriteStdout(output, BenchWorld.ThrowOnError);
    assert io.stdout() == preStdout + output;
    var _, _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
    assert io.stderr() == preStderr + err;
    exit := if hadError then 1 else 0;
    assert CoreSummary(raw, io, exit);
  }
}
