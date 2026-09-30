include "../../core/World.dfy"
include "PrintfSchema.dfy"
include "PrintfCore.dfy"
include "PrintfSpec.dfy"

module PrintfProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = PrintfSchema
  import Core = PrintfCore
  import Spec = PrintfSpec

  lemma ClassifyFragmentIff(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat,
    end: nat,
    afterArg: nat,
    output: BW.Bytes
  )
    requires start < |format|
    requires nextArg <= |args|
    ensures (Core.ClassifyFragment(format, args, start, nextArg) ==
             Spec.OneFragment(Spec.FormatFragment(end, afterArg, output))) ==
            Spec.FormatFragmentRelation(
              format, args, start, nextArg, end, afterArg, output)
  {
  }

  lemma ClassifyStopIff(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat,
    status: int,
    stderr: BW.Bytes
  )
    requires start < |format|
    requires nextArg <= |args|
    ensures Spec.FormatStopRelation(format, start, status, stderr) ==
      (Core.ClassifyFragment(format, args, start, nextArg) ==
         Spec.StopFragment(status, stderr) ||
       (Core.ClassifyFragment(format, args, start, nextArg) == Spec.NoFragment &&
        status == 2 && stderr == Spec.UnsupportedFormatMessage()))
  {
  }

  lemma BuildFormatDerivation(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat
  ) returns (derivation: Spec.FormatDerivation)
    requires start <= |format|
    requires startArg <= |args|
    ensures Spec.FormatDerivationRelation(
      format, args, start, startArg,
      Core.RenderPass(format, args, start, startArg).2,
      Core.RenderPass(format, args, start, startArg).1,
      Core.RenderPass(format, args, start, startArg).0,
      Core.RenderPass(format, args, start, startArg).3,
      derivation)
    decreases |format| - start
  {
    if start == |format| {
      derivation := Spec.FormatDone;
    } else {
      match Core.ClassifyFragment(format, args, start, startArg)
      case NoFragment =>
        ClassifyStopIff(format, args, start, startArg,
                        2, Spec.UnsupportedFormatMessage());
        derivation := Spec.FormatStop;
      case StopFragment(status, stderr) =>
        ClassifyStopIff(format, args, start, startArg, status, stderr);
        derivation := Spec.FormatStop;
      case OneFragment(fragment) =>
        ClassifyFragmentIff(format, args, start, startArg,
                            fragment.end, fragment.afterArg, fragment.output);
        var restDerivation := BuildFormatDerivation(
          format, args, fragment.end, fragment.afterArg);
        var rest := Core.RenderPass(format, args, fragment.end, fragment.afterArg);
        derivation := Spec.FormatStep(fragment, rest.1, restDerivation);
    }
  }

  lemma BuildRepeatedDerivation(
    format: string,
    args: seq<string>,
    startArg: nat
  ) returns (derivation: Spec.RepeatedDerivation)
    requires startArg <= |args|
    ensures Spec.RepeatedPassesFromRelation(
      format, args, startArg,
      Core.RenderRepeatedFrom(format, args, startArg).0,
      Core.RenderRepeatedFrom(format, args, startArg).1,
      Core.RenderRepeatedFrom(format, args, startArg).2,
      derivation)
    decreases |args| - startArg
  {
    var pass := Core.RenderPass(format, args, 0, startArg);
    var passDerivation := BuildFormatDerivation(format, args, 0, startArg);
    assert Spec.FormatPassRelation(
      format, args, startArg, pass.2, pass.1, pass.0, pass.3) by {
      assert exists d: Spec.FormatDerivation ::
        Spec.FormatDerivationRelation(
          format, args, 0, startArg, pass.2, pass.1, pass.0, pass.3, d) by {
        ghost var d := passDerivation;
      }
    }
    if pass.0 != 0 {
      derivation := Spec.RepeatedStop(pass.2, pass.1, pass.0, pass.3);
    } else if pass.2 == startArg || pass.2 >= |args| {
      derivation := Spec.RepeatedDone(pass.2, pass.1);
    } else {
      assert startArg < pass.2 < |args|;
      var restDerivation := BuildRepeatedDerivation(format, args, pass.2);
      var rest := Core.RenderRepeatedFrom(format, args, pass.2);
      derivation := Spec.RepeatedStep(pass.2, pass.1, rest.1, restDerivation);
    }
  }

  lemma RenderRepeatedRefines(format: string, args: seq<string>)
    ensures Spec.RenderRelation(
      format, args,
      Core.RenderRepeated(format, args).0 != 2,
      Core.RenderRepeated(format, args).1,
      Core.RenderRepeated(format, args).2)
  {
    var derivation := BuildRepeatedDerivation(format, args, 0);
    assert exists status: int, d: Spec.RepeatedDerivation ::
      (status == 0 || status == 1 || status == 2) &&
      (Core.RenderRepeated(format, args).0 != 2) == (status != 2) &&
      Spec.RepeatedPassesFromRelation(
        format, args, 0, status,
        Core.RenderRepeated(format, args).1,
        Core.RenderRepeated(format, args).2, d) by {
      ghost var status := Core.RenderRepeated(format, args).0;
      ghost var d := derivation;
    }
  }

  lemma EvaluateRefines(raw: Schema.PrintfCmdRaw)
    ensures Spec.EvaluationRelation(
      raw, Core.Evaluate(raw).0, Core.Evaluate(raw).1, Core.Evaluate(raw).2)
  {
    if !Schema.HelpSelected(raw) &&
       !Schema.VersionSelected(raw) &&
       |raw.operands| > 0 {
      RenderRepeatedRefines(raw.operands[0], raw.operands[1..]);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    EvaluateRefines(raw);
  }
}
