include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "UnlinkSchema.dfy"
include "UnlinkSpec.dfy"

module UnlinkCore {
  import BenchIO
  import BenchWorld
  import Schema = UnlinkSchema
  import Spec = UnlinkSpec
  import Utf8 = Utf8Semantics
  import C = IOContract

  twostate predicate CoreSummary(raw: Schema.UnlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion,
      io.trustedStreamsRegion, io.fsRegion, io.nowRegion,
      io.trustedFilesystemRegion
  {
    Spec.Spec(raw, io, exit)
  }

  method RunCore(raw: Schema.UnlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    if raw.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpTextSpec());
      exit := 0;
      assert io.stdout() == old(io.stdout()) + Spec.HelpTextSpec();
      assert io.stderr() == old(io.stderr());
    } else if raw.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionTextSpec());
      exit := 0;
      assert io.stdout() == old(io.stdout()) + Spec.VersionTextSpec();
      assert io.stderr() == old(io.stderr());
    } else if |raw.operands| == 0 {
      io.AppendStderr(Spec.MissingOperandText());
      exit := 1;
      assert io.stderr() == old(io.stderr()) + Spec.MissingOperandText();
    } else if |raw.operands| > 1 {
      var quoted := io.QuoteArgument(Utf8.Encode(raw.operands[1]));
      var committed, writeErr := io.WriteStderrWithOutcome(Spec.ExtraOperandText(quoted));
      exit := 1;
      
      assert C.QuoteArgumentSpec(Utf8.Encode(raw.operands[1]), quoted);
      assert Spec.StderrResult(io, Spec.ExtraOperandText(quoted), writeErr);
    } else {
      var ok, err := io.UnlinkPath(raw.operands[0]);
      assert Spec.UnlinkResult(io, raw.operands[0], ok, err);

      if ok {
        exit := 0;
        assert io.stderr() == old(io.stderr());
      } else {
        var quoted := io.QuoteafPath(raw.operands[0]);
        var reason := io.GetCLocaleErrnoText(err);
        var committed, writeErr := io.WriteStderrWithOutcome(Spec.CannotUnlinkText(quoted, reason));
        exit := 1;

        assert C.QuoteafPathSpec(raw.operands[0], quoted);
        assert C.GetCLocaleErrnoTextSpec(err, reason);
        assert Spec.StderrResult(io, Spec.CannotUnlinkText(quoted, reason), writeErr);

        assert exists q: BenchWorld.Bytes, r: string, w: int ::
          C.QuoteafPathSpec(raw.operands[0], q) &&
          C.GetCLocaleErrnoTextSpec(err, r) &&
          Spec.StderrResult(io, Spec.CannotUnlinkText(q, r), w);
          
        assert Spec.UnlinkResult(io, raw.operands[0], ok, err);
        assert Spec.Spec(raw, io, exit);
      }
    }
    assert Spec.Spec(raw, io, exit);
  }
}
