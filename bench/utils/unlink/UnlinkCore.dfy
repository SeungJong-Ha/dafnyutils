include "../../core/IO.dfy"
include "UnlinkSchema.dfy"
include "UnlinkSpec.dfy"

module UnlinkCore {
  import BenchIO
  import Schema = UnlinkSchema
  import Spec = UnlinkSpec
  import C = IOContract
  import Utf8 = Utf8Semantics

  twostate predicate CoreSummary(raw: Schema.UnlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
          Spec.ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandText() &&
      exit == 1
    else
      exists ok: bool, err: int ::
        Spec.UnlinkResult(io, raw.operands[0], ok, err) &&
        io.stdout() == old(io.stdout()) &&
        (if ok then
          io.stderr() == old(io.stderr()) && exit == 0
        else
          io.stderr() == old(io.stderr()) +
            Spec.CannotUnlinkText(C.QuoteafPathResult(raw.operands[0]), C.CLocaleErrnoTextResult(err)) &&
          exit == 1)
  }

  method RunCore(raw: Schema.UnlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    if raw.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpTextSpec());
      exit := 0;
    } else if raw.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionTextSpec());
      exit := 0;
    } else if raw.mode.ModeExtraOperand? {
      var quotedOperand := io.QuoteArgument(Utf8.Encode(raw.mode.operand));
      io.AppendStderr(Spec.ExtraOperandText(quotedOperand));
      exit := 1;
    } else if |raw.operands| == 0 {
      io.AppendStderr(Spec.MissingOperandText());
      exit := 1;
    } else {
      var ok, err := io.UnlinkPath(raw.operands[0]);
      assert Spec.UnlinkResult(io, raw.operands[0], ok, err);

      if ok {
        exit := 0;
      } else {
        var reason := io.GetCLocaleErrnoText(err);
        var quotedPath := io.QuoteafPath(raw.operands[0]);
        io.AppendStderr(Spec.CannotUnlinkText(quotedPath, reason));
        exit := 1;

        assert C.GetCLocaleErrnoTextSpec(err, reason);
        assert Spec.UnlinkResult(io, raw.operands[0], ok, err);
      }
    }
  }
}
