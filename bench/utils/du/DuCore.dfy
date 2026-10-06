include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "DuSchema.dfy"
include "DuSpec.dfy"

module DuCore {
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = DuSchema
  import Spec = DuSpec
  import Utf8 = Utf8Semantics

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  function NatText(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      NatText(n / 10) + [DigitChar(n % 10)]
  }

  function CountLine(size: nat, path: BenchWorld.Path): BenchWorld.Bytes
  {
    NatText(size) + "\t" + Utf8.Encode(path) + "\n"
  }

  function OutputPiece(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => CountLine(|data|, path)
    case Err(_) => []
  }

  function ErrorPiece(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(_) => []
    case Err(err) => Spec.ErrorMessageSpec(path, err)
  }

  ghost function ReadResultCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.operands|
  {
    IOContract.ObservedReadFileResultFields(preFs, preStreams, cmd.operands[i])
  }

  ghost function PrefixOutputCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.operands|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutputCore(cmd, preFs, preStreams, i - 1) +
      OutputPiece(cmd.operands[i - 1], ReadResultCore(cmd, preFs, preStreams, i - 1))
  }

  ghost function PrefixErrorsCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.operands|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorsCore(cmd, preFs, preStreams, i - 1) +
      ErrorPiece(cmd.operands[i - 1], ReadResultCore(cmd, preFs, preStreams, i - 1))
  }

  ghost predicate PrefixHadErrorCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  )
    requires i <= |cmd.operands|
    decreases i
  {
    i > 0 &&
    (PrefixHadErrorCore(cmd, preFs, preStreams, i - 1) ||
     ReadResultCore(cmd, preFs, preStreams, i - 1).Err?)
  }

  twostate predicate CoreSummary(raw: Schema.DuCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeUnsupportedAccounting then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedAccountingMessageSpec() &&
      exit == 1
    else
      io.stdout() == old(io.stdout()) + PrefixOutputCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) &&
      io.stderr() == old(io.stderr()) + PrefixErrorsCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) &&
      exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) then 1 else 0)
  }

  method RunCore(raw: Schema.DuCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      var _ := io.WriteStdout(Spec.HelpTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var _ := io.WriteStdout(Spec.VersionTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeUnsupportedAccounting {
      var _ := io.WriteStderr(Spec.UnsupportedAccountingMessageSpec(), BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var output: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;

    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant output == PrefixOutputCore(cmd, preFs, preStreams, i)
      invariant err == PrefixErrorsCore(cmd, preFs, preStreams, i)
      invariant hadError == PrefixHadErrorCore(cmd, preFs, preStreams, i)
      decreases |cmd.operands| - i
    {
      var path := cmd.operands[i];
      var readResult := io.ReadFile(path);
      assert readResult == ReadResultCore(cmd, preFs, preStreams, i);

      match readResult {
        case Ok(data) =>
          output := output + OutputPiece(path, readResult);
        case Err(e) =>
          err := err + ErrorPiece(path, readResult);
          hadError := true;
      }
      i := i + 1;
    }

    assert io.stdout() == preStdout;
    assert io.stderr() == preStderr;
    var _ := io.WriteStdout(output, BenchWorld.ThrowOnError);
    assert io.stdout() == preStdout + output;
    assert io.stderr() == preStderr;
    var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
    assert io.stdout() == preStdout + output;
    assert io.stderr() == preStderr + err;
    exit := if hadError then 1 else 0;
    assert output == PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|);
    assert err == PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|);
    assert hadError == PrefixHadErrorCore(cmd, preFs, preStreams, |cmd.operands|);
    assert CoreSummary(raw, io, exit);
  }
}
