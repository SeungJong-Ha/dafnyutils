include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TailSchema.dfy"
include "TailRecordCore.dfy"
include "TailSpec.dfy"

module TailCore {
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import TailSchema
  import TailRecordCore
  import Spec = TailSpec

  function InputsFromOperands(operands: seq<string>): seq<TailSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then TailSchema.Stdin(Spec.StandardInputName()) else TailSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var first :=
        if operands[0] == "-"
        then TailSchema.Stdin(Spec.StandardInputName())
        else TailSchema.File(operands[0]);
      return [first] + InputsFromOperands(operands[1..]);
    }
  }

  ghost function HelpBeforeOther(raw: TailSchema.TailCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (raw.invalidCountTokenIndex == -1 || raw.helpTokenIndex <= raw.invalidCountTokenIndex)
  }

  ghost function VersionBeforeInvalid(raw: TailSchema.TailCmdRaw): bool
  {
    raw.seenVersion &&
    (raw.invalidCountTokenIndex == -1 || raw.versionTokenIndex <= raw.invalidCountTokenIndex)
  }

  function Command(raw: TailSchema.TailCmdRaw): TailSchema.TailCmd
  {
    var mode :=
      if HelpBeforeOther(raw) then
        TailSchema.ModeHelp
      else if VersionBeforeInvalid(raw) then
        TailSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        TailSchema.ModeInvalidCount
      else
        TailSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs :=
      if mode == TailSchema.ModeRun && |inputs| == 0
      then [TailSchema.Stdin(Spec.StandardInputName())]
      else inputs;
    TailSchema.TailCmd(
      mode,
      raw.selection,
      raw.headerMode,
      raw.zeroTerminated,
      raw.invalidCountUnit,
      raw.invalidCountValue,
      runInputs
    )
  } by method {
    var mode :=
      if raw.seenHelp &&
         (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
         (raw.invalidCountTokenIndex == -1 ||
          raw.helpTokenIndex <= raw.invalidCountTokenIndex) then
        TailSchema.ModeHelp
      else if raw.seenVersion &&
              (raw.invalidCountTokenIndex == -1 ||
               raw.versionTokenIndex <= raw.invalidCountTokenIndex) then
        TailSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        TailSchema.ModeInvalidCount
      else
        TailSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs :=
      if mode == TailSchema.ModeRun && |inputs| == 0
      then [TailSchema.Stdin(Spec.StandardInputName())]
      else inputs;
    return TailSchema.TailCmd(
        mode,
        raw.selection,
        raw.headerMode,
        raw.zeroTerminated,
        raw.invalidCountUnit,
        raw.invalidCountValue,
        runInputs
      );
  }

  ghost function IsStdinInput(input: TailSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function InputName(input: TailSchema.Input): string
  {
    match input
    case Stdin(displayName) => displayName
    case File(path) => path
  } by method {
    return
      match input
      case Stdin(displayName) => displayName
      case File(path) => path;
  }

  ghost function PrefixStdinCore(cmd: TailSchema.TailCmd, preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin(_) => []
      case File(_) => PrefixStdinCore(cmd, preStdin, i - 1)
  }

  ghost function ReadResultCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) => Result.Ok(PrefixStdinCore(cmd, preStdin, i))
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function DropFirstBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if count == 0 then data else if |data| <= count then [] else data[count..]
  } by method {
    if count == 0 {
      return data;
    } else if |data| <= count {
      return [];
    } else {
      return data[count..];
    }
  }

  function TakeLastBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if |data| <= count then data else data[|data| - count..]
  } by method {
    if |data| <= count {
      return data;
    } else {
      return data[|data| - count..];
    }
  }

  function RenderData(cmd: TailSchema.TailCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.selection.unit == TailSchema.CountBytes then
      if cmd.selection.fromStart then
        DropFirstBytes(data, if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1)
      else
        TakeLastBytes(data, cmd.selection.amount)
    else
      var delimiter := TailRecordCore.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart then
        TailRecordCore.DropFirstRecords(data, if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1, delimiter)
      else
        TailRecordCore.TakeLastRecords(data, cmd.selection.amount, delimiter)
  } by method {
    if cmd.selection.unit == TailSchema.CountBytes {
      if cmd.selection.fromStart {
        return DropFirstBytes(
            data,
            if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1
          );
      } else {
        return TakeLastBytes(data, cmd.selection.amount);
      }
    } else {
      var delimiter := TailRecordCore.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart {
        return TailRecordCore.DropFirstRecords(
            data,
            if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1,
            delimiter
          );
      } else {
        return TailRecordCore.TakeLastRecords(data, cmd.selection.amount, delimiter);
      }
    }
  }

  function ShouldPrintHeaders(cmd: TailSchema.TailCmd): bool
  {
    cmd.headerMode == TailSchema.HeadersAlways ||
    (cmd.headerMode == TailSchema.HeadersMultiple && |cmd.inputs| > 1)
  } by method {
    return cmd.headerMode == TailSchema.HeadersAlways ||
           (cmd.headerMode == TailSchema.HeadersMultiple && |cmd.inputs| > 1);
  }

  function SuppressZeroTrailingSelection(cmd: TailSchema.TailCmd): bool
  {
    !cmd.selection.fromStart && cmd.selection.amount == 0
  } by method {
    return !cmd.selection.fromStart && cmd.selection.amount == 0;
  }

  function HeaderForInput(cmd: TailSchema.TailCmd, input: TailSchema.Input, printedHeaders: int): BenchWorld.Bytes
  {
    if ShouldPrintHeaders(cmd) then
      (if printedHeaders == 0 then [] else ['\n']) +
      Spec.HeaderText(InputName(input))
    else
      []
  } by method {
    if ShouldPrintHeaders(cmd) {
      return (if printedHeaders == 0 then [] else ['\n']) +
        Spec.HeaderText(InputName(input));
    } else {
      return [];
    }
  }

  function ResultHasHeader(cmd: TailSchema.TailCmd, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    match result
    case Ok(_) => !SuppressZeroTrailingSelection(cmd)
    case Err(err) => IOContract.IOErrorIsDirectory(err)
  } by method {
    return
      match result
      case Ok(_) => !SuppressZeroTrailingSelection(cmd)
      case Err(err) => IOContract.IOErrorIsDirectory(err);
  }

  function OutputPiece(
    cmd: TailSchema.TailCmd,
    input: TailSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              printedHeaders: int
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) =>
      if SuppressZeroTrailingSelection(cmd) then
        []
      else
        HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, data)
    case Err(err) => if IOContract.IOErrorIsDirectory(err) then HeaderForInput(cmd, input, printedHeaders) else []
  } by method {
    match result
    case Ok(data) =>
      if SuppressZeroTrailingSelection(cmd) {
        return [];
      } else {
        return HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, data);
      }
    case Err(err) =>
      if IOContract.IOErrorIsDirectory(err) {
        return HeaderForInput(cmd, input, printedHeaders);
      } else {
        return [];
      }
  }

  function ErrorPiece(input: TailSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin(_) => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessage(path, err)
  } by method {
    match input
    case Stdin(_) =>
      return [];
    case File(path) =>
      match result
      case Ok(_) =>
        return [];
      case Err(err) =>
        return Spec.ErrorMessage(path, err);
  }

  function HadErrorPiece(input: TailSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin(_) => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  } by method {
    return
      match input
      case Stdin(_) => false
      case File(_) =>
        match result
        case Ok(_) => false
        case Err(_) => true;
  }

  ghost function PrefixHeaderCountCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): nat
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      0
    else
      PrefixHeaderCountCore(cmd, preFs, preStdin, i - 1, preStreams) +
      (if ResultHasHeader(cmd, ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams)) then 1 else 0)
  }

  ghost function PrefixOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutputCore(cmd, preFs, preStdin, i - 1, preStreams) +
      OutputPiece(
        cmd,
        cmd.inputs[i - 1],
        ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams),
        PrefixHeaderCountCore(cmd, preFs, preStdin, i - 1, preStreams)
      )
  }

  ghost function PrefixErrorOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorOutputCore(cmd, preFs, preStdin, i - 1, preStreams) +
      ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams))
  }

  ghost function PrefixHadErrorCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadErrorCore(cmd, preFs, preStdin, i - 1, preStreams) ||
      HadErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams))
  }

  ghost function RunOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
  {
    PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|, preStreams)
  }

  twostate predicate CoreSummary(raw: TailSchema.TailCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == TailSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else if SuppressZeroTrailingSelection(cmd) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      io.stdin() == PrefixStdinCore(cmd, old(io.stdin()), |cmd.inputs|) &&
      io.stdout() == old(io.stdout()) + RunOutputCore(cmd, old(io.fs()), old(io.stdin()), old(io.trustedStreams())) &&
      io.stderr() == old(io.stderr()) + PrefixErrorOutputCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|, old(io.trustedStreams())) &&
      exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|, old(io.trustedStreams())) then 1 else 0)
  }

  lemma PrefixStdinCoreStep(cmd: TailSchema.TailCmd, preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStdin, i + 1) ==
            match cmd.inputs[i]
            case Stdin(_) => IOContract.AfterReadStdinFields(PrefixStdinCore(cmd, preStdin, i))
            case File(_) => PrefixStdinCore(cmd, preStdin, i)
  {
  }

  lemma PrefixHeaderCountCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixHeaderCountCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixHeaderCountCore(cmd, preFs, preStdin, i, preStreams) +
            (if ResultHasHeader(cmd, ReadResultCore(cmd, preFs, preStdin, i, preStreams)) then 1 else 0)
  {
  }

  lemma PrefixOutputCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixOutputCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixOutputCore(cmd, preFs, preStdin, i, preStreams) +
            OutputPiece(
              cmd,
              cmd.inputs[i],
              ReadResultCore(cmd, preFs, preStdin, i, preStreams),
              PrefixHeaderCountCore(cmd, preFs, preStdin, i, preStreams)
            )
  {
  }

  lemma PrefixErrorOutputCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixErrorOutputCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixErrorOutputCore(cmd, preFs, preStdin, i, preStreams) +
            ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i, preStreams))
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixHadErrorCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            (PrefixHadErrorCore(cmd, preFs, preStdin, i, preStreams) ||
             HadErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i, preStreams)))
  {
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpText()
  {
    out := Spec.HelpText();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionText()
  {
    out := Spec.VersionText();
  }

  method RunCore(raw: TailSchema.TailCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);

    if cmd.mode == TailSchema.ModeHelp {
      var help := GetHelpText();
      var _ := io.WriteStdout(help, BenchWorld.ThrowOnError);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.HelpText();
      return;
    }

    if cmd.mode == TailSchema.ModeVersion {
      var version := GetVersionText();
      var _ := io.WriteStdout(version, BenchWorld.ThrowOnError);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.VersionText();
      return;
    }

    if cmd.mode == TailSchema.ModeInvalidCount {
      var invalid := Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      var _ := io.WriteStderr(invalid, BenchWorld.ThrowOnError);
      exit := 1;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert io.stderr() == preStderr + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      return;
    }

    var suppressZero := SuppressZeroTrailingSelection(cmd);
    if suppressZero {
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert io.stderr() == preStderr;
      return;
    }

    var out: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    var headers := 0;

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant io.stdin() == PrefixStdinCore(cmd, preStdin, i)
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant out == PrefixOutputCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant err == PrefixErrorOutputCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant hadError == PrefixHadErrorCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant headers == PrefixHeaderCountCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
      match input {
        case Stdin(_) =>
          ghost var beforeStdin := io.stdin();
          var data :- assert io.ReadStdin(BenchWorld.ThrowOnError);
          readResult := Result.Ok(data);
          PrefixStdinCoreStep(cmd, preStdin, i);
          PrefixHeaderCountCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixHadErrorCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          assert beforeStdin == PrefixStdinCore(cmd, preStdin, i);
          assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
          assert data == beforeStdin;
        case File(path) =>
          readResult := io.ReadFile(path);
      }
      if input.File? {
        PrefixStdinCoreStep(cmd, preStdin, i);
        PrefixHeaderCountCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixHadErrorCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
      }
      assert readResult == ReadResultCore(cmd, preFs, preStdin, i, old(io.trustedStreams()));

      var piece := OutputPiece(cmd, input, readResult, headers);
      var errorPiece := ErrorPiece(input, readResult);
      var inputHadError := HadErrorPiece(input, readResult);
      var inputHadHeader := ResultHasHeader(cmd, readResult);

      out := out + piece;
      err := err + errorPiece;
      hadError := hadError || inputHadError;
      headers := headers + (if inputHadHeader then 1 else 0);
      i := i + 1;
    }

    if |out| > 0 {
      var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
    } else {
      assert out == [];
      assert io.stdout() == preStdout + out;
    }
    if |err| > 0 {
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
    } else {
      assert err == [];
      assert io.stderr() == preStderr + err;
    }
    exit := if hadError then 1 else 0;

    assert out == RunOutputCore(cmd, preFs, preStdin, old(io.trustedStreams()));
    assert err == PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
    assert hadError == PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
    assert io.stdin() == PrefixStdinCore(cmd, preStdin, |cmd.inputs|);
    assert io.stdout() == preStdout + RunOutputCore(cmd, preFs, preStdin, old(io.trustedStreams()));
    assert io.stderr() == preStderr + PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
  }
}
