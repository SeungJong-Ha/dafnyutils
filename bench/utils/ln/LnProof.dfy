include "../../core/World.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"
include "LnCore.dfy"
include "LnSpec.dfy"

module LnProof {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LnSchema
  import Core = LnCore
  import Spec = LnSpec

  lemma DestinationEq(
    fs: BenchWorld.FileSystem, operands: seq<string>
  )
    requires 1 <= |operands| <= 2
    ensures Core.CoreDestination(fs, operands) == Spec.LinkDestination(fs, operands)
  {
    if |operands| == 2 && operands[0] != "" {
      assert Core.LinkNameIsDirectoryFs(fs, operands[1]) ==
        Spec.LinkNameIsDirectoryFs(fs, operands[1]);
    }
  }

  lemma StepSummaryImpliesSpec(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    source: BenchWorld.Path,
    destination: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
    requires Core.CoreStepSummary(
      beforeFs, afterFs, now, trustedFilesystem, source,
      destination, symbolic, diagnostic, success)
    ensures Spec.LinkStepRelation(
      beforeFs, afterFs, now, trustedFilesystem, source,
      destination, symbolic, diagnostic, success)
  {
    reveal Spec.LinkStepRelation();
  }

  lemma {:isolate_assertions} SpecBatchFromWitness(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    sources: seq<BenchWorld.Path>,
    directory: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool,
    states: seq<BenchWorld.FileSystem>,
    diagnostics: seq<BenchWorld.Bytes>,
    results: seq<bool>,
    pieces: seq<BenchWorld.Bytes>,
    stepResults: seq<bool>
  )
    requires |states| == |sources| + 1
    requires |diagnostics| == |sources| + 1
    requires |results| == |sources| + 1
    requires |pieces| == |sources|
    requires |stepResults| == |sources|
    requires states[0] == beforeFs && states[|sources|] == afterFs
    requires diagnostics[0] == [] && diagnostics[|sources|] == diagnostic
    requires results[0] && results[|sources|] == success
    requires forall i: nat :: i < |sources| ==>
      Spec.LinkStepRelation(
        states[i], states[i + 1], now, trustedFilesystem,
        sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
        pieces[i], stepResults[i]) &&
      diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
      results[i + 1] == (results[i] && stepResults[i])
    ensures Spec.LinkBatchRelation(
      beforeFs, afterFs, now, trustedFilesystem, sources,
      directory, symbolic, diagnostic, success)
  {
    reveal Spec.LinkBatchRelation();
    assert Spec.LinkBatchRelation(
      beforeFs, afterFs, now, trustedFilesystem, sources,
      directory, symbolic, diagnostic, success);
  }

  lemma {:isolate_assertions} BatchStepTraceImpliesSpec(
    now: int,
    trustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    sources: seq<BenchWorld.Path>,
    directory: BenchWorld.Path,
    symbolic: bool,
    states: seq<BenchWorld.FileSystem>,
    diagnostics: seq<BenchWorld.Bytes>,
    results: seq<bool>,
    pieces: seq<BenchWorld.Bytes>,
    stepResults: seq<bool>
  )
    requires |states| == |sources| + 1
    requires |diagnostics| == |sources| + 1
    requires |results| == |sources| + 1
    requires |pieces| == |sources|
    requires |stepResults| == |sources|
    requires forall i: nat :: i < |sources| ==>
      Core.CoreStepSummary(
        states[i], states[i + 1], now, trustedFilesystem,
        sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
        pieces[i], stepResults[i]) &&
      diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
      results[i + 1] == (results[i] && stepResults[i])
    ensures forall i: nat :: i < |sources| ==>
      Spec.LinkStepRelation(
        states[i], states[i + 1], now, trustedFilesystem,
        sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
        pieces[i], stepResults[i]) &&
      diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
      results[i + 1] == (results[i] && stepResults[i])
  {
    hide Core.CoreStepSummary;
    forall i: nat | i < |sources|
      ensures Spec.LinkStepRelation(
        states[i], states[i + 1], now, trustedFilesystem,
        sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
        pieces[i], stepResults[i]) &&
        diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
        results[i + 1] == (results[i] && stepResults[i])
    {
      StepSummaryImpliesSpec(
        states[i], states[i + 1], now, trustedFilesystem,
        sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
        pieces[i], stepResults[i]);
    }
  }

  lemma {:isolate_assertions} BatchSummaryImpliesSpec(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    sources: seq<BenchWorld.Path>,
    directory: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
    requires Core.CoreBatchSummary(
      beforeFs, afterFs, now, trustedFilesystem, sources,
      directory, symbolic, diagnostic, success)
    ensures Spec.LinkBatchRelation(
      beforeFs, afterFs, now, trustedFilesystem, sources,
      directory, symbolic, diagnostic, success)
  {
    hide Core.CoreStepSummary;
    var states: seq<BenchWorld.FileSystem>,
        diagnostics: seq<BenchWorld.Bytes>,
        results: seq<bool>,
        pieces: seq<BenchWorld.Bytes>,
        stepResults: seq<bool> :|
      |states| == |sources| + 1 &&
      |diagnostics| == |sources| + 1 &&
      |results| == |sources| + 1 &&
      |pieces| == |sources| &&
      |stepResults| == |sources| &&
      states[0] == beforeFs &&
      states[|sources|] == afterFs &&
      diagnostics[0] == [] &&
      diagnostics[|sources|] == diagnostic &&
      results[0] &&
      results[|sources|] == success &&
      (forall i: nat :: i < |sources| ==>
        Core.CoreStepSummary(
          states[i], states[i + 1], now, trustedFilesystem,
          sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
          pieces[i], stepResults[i]) &&
        diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
        results[i + 1] == (results[i] && stepResults[i]));
    hide Core.CoreBatchSummary;
    BatchStepTraceImpliesSpec(
      now, trustedFilesystem, sources, directory, symbolic,
      states, diagnostics, results, pieces, stepResults);
    SpecBatchFromWitness(
      beforeFs, afterFs, now, trustedFilesystem, sources, directory,
      symbolic, diagnostic, success, states, diagnostics, results,
      pieces, stepResults);
  }

  twostate lemma {:isolate_assertions} CoreSummaryImpliesSpec(
    raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    hide Core.CoreStepSummary;
    hide Core.CoreBatchSummary;
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun && 1 <= |cmd.operands| <= 2 {
      var source := cmd.operands[0];
      DestinationEq(old(io.fs()), cmd.operands);
      var destination := Core.CoreDestination(old(io.fs()), cmd.operands);
      var diagnostic: BenchWorld.Bytes, success: bool :|
        Core.CoreStepSummary(
          old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
          source, destination, cmd.symbolic, diagnostic, success) &&
        io.stderr() == old(io.stderr()) + diagnostic &&
        exit == (if success then 0 else 1);
      StepSummaryImpliesSpec(
        old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
        source, destination, cmd.symbolic, diagnostic, success);
      reveal Spec.LinkStepRelation();
    }
    if cmd.mode == Schema.ModeRun && |cmd.operands| > 2 {
      var target := cmd.operands[|cmd.operands| - 1];
      var targetOk: bool, targetIsDir: bool, targetErr: int :|
        IOContract.IsDirectoryStrictContractFields(
          old(io.fs()), target, true, targetOk, targetIsDir, targetErr) &&
        (if !(targetOk && targetIsDir) then
           io.fs() == old(io.fs()) &&
           io.stderr() == old(io.stderr()) +
             Spec.TargetDirectoryErrorMessageSpec(target, if targetOk then 20 else targetErr) &&
           exit == 1
         else
           exists diagnostic: BenchWorld.Bytes, success: bool
             {:trigger Core.CoreBatchSummary(old(io.fs()), io.fs(), old(io.now()),
               old(io.trustedFilesystem()), cmd.operands[..|cmd.operands| - 1],
               target, cmd.symbolic, diagnostic, success)} ::
             Core.CoreBatchSummary(
               old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
               cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
               diagnostic, success) &&
             io.stderr() == old(io.stderr()) + diagnostic &&
             exit == (if success then 0 else 1));
      if targetOk && targetIsDir {
        var diagnostic: BenchWorld.Bytes, success: bool :|
          Core.CoreBatchSummary(
            old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
            cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
            diagnostic, success) &&
          io.stderr() == old(io.stderr()) + diagnostic &&
          exit == (if success then 0 else 1);
        BatchSummaryImpliesSpec(
          old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
          cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
          diagnostic, success);
      }
    }
  }
}
