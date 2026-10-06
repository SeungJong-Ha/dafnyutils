include "../../core/World.dfy"
include "DuSchema.dfy"
include "DuCore.dfy"
include "DuSpec.dfy"

module DuProof {
  import Result = Results
  import BenchIO
  import BenchWorld
  import Schema = DuSchema
  import Core = DuCore
  import Spec = DuSpec

  lemma NatTextRefines(n: nat)
    ensures Core.NatText(n) == Spec.NatText(n)
    decreases n
  {
    if n >= 10 {
      NatTextRefines(n / 10);
    }
  }

  lemma OutputPieceRefines(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    ensures Core.OutputPiece(path, result) == Spec.OutputPieceSpec(path, result)
  {
    match result
    case Ok(data) =>
      NatTextRefines(|data|);
    case Err(_) =>
  }

  lemma ErrorPieceRefines(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    ensures Core.ErrorPiece(path, result) == Spec.ErrorPieceSpec(path, result)
  {
  }

  lemma OutputSegment(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    count: nat,
    i: nat
  )
    requires i < count <= |cmd.operands|
    ensures |Core.PrefixOutputCore(cmd, preFs, preStreams, i + 1)| <=
            |Core.PrefixOutputCore(cmd, preFs, preStreams, count)|
    ensures Core.PrefixOutputCore(cmd, preFs, preStreams, count)[
            |Core.PrefixOutputCore(cmd, preFs, preStreams, i)|..
            |Core.PrefixOutputCore(cmd, preFs, preStreams, i + 1)|
            ] == Spec.OutputPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i))
    decreases count - i
  {
    OutputPieceRefines(
      cmd.operands[count - 1],
      Core.ReadResultCore(cmd, preFs, preStreams, count - 1)
    );
    OutputPieceRefines(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i));
    if i + 1 < count {
      OutputSegment(cmd, preFs, preStreams, count - 1, i);
      assert Core.PrefixOutputCore(cmd, preFs, preStreams, count) ==
             Core.PrefixOutputCore(cmd, preFs, preStreams, count - 1) +
             Spec.OutputPieceSpec(
               cmd.operands[count - 1],
               Core.ReadResultCore(cmd, preFs, preStreams, count - 1)
             );
    } else {
      assert count == i + 1;
      assert Core.PrefixOutputCore(cmd, preFs, preStreams, count) ==
             Core.PrefixOutputCore(cmd, preFs, preStreams, i) +
             Spec.OutputPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i));
    }
  }

  lemma ErrorSegment(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    count: nat,
    i: nat
  )
    requires i < count <= |cmd.operands|
    ensures |Core.PrefixErrorsCore(cmd, preFs, preStreams, i + 1)| <=
            |Core.PrefixErrorsCore(cmd, preFs, preStreams, count)|
    ensures Core.PrefixErrorsCore(cmd, preFs, preStreams, count)[
            |Core.PrefixErrorsCore(cmd, preFs, preStreams, i)|..
            |Core.PrefixErrorsCore(cmd, preFs, preStreams, i + 1)|
            ] == Spec.ErrorPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i))
    decreases count - i
  {
    ErrorPieceRefines(
      cmd.operands[count - 1],
      Core.ReadResultCore(cmd, preFs, preStreams, count - 1)
    );
    ErrorPieceRefines(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i));
    if i + 1 < count {
      ErrorSegment(cmd, preFs, preStreams, count - 1, i);
    }
  }

  lemma OutputEvidence(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
    requires |pieces| == |cmd.operands|
    requires forall i: nat | i < |cmd.operands| ::
               pieces[i] ==
               Spec.OutputPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i))
    requires |cuts| == |cmd.operands| + 1
    requires forall i: nat | i <= |cmd.operands| ::
               cuts[i] == |Core.PrefixOutputCore(cmd, preFs, preStreams, i)|
    ensures Spec.FragmentsConcatenate(
              pieces,
              Core.PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|),
              cuts
            )
  {
    ghost var combined := Core.PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|);
    assert |cuts| == |pieces| + 1;
    assert cuts[0] == 0;
    assert cuts[|pieces|] == |combined|;
    forall i: nat {:trigger cuts[i + 1], pieces[i]} | i < |pieces|
      ensures
        cuts[i] <= cuts[i + 1] &&
        cuts[i + 1] <= |combined| &&
        cuts[i + 1] == cuts[i] + |pieces[i]| &&
        combined[cuts[i]..cuts[i + 1]] == pieces[i]
    {
      OutputSegment(cmd, preFs, preStreams, |cmd.operands|, i);
      assert cuts[i] == |Core.PrefixOutputCore(cmd, preFs, preStreams, i)|;
      assert cuts[i + 1] == |Core.PrefixOutputCore(cmd, preFs, preStreams, i + 1)|;
      assert pieces[i] == Spec.OutputPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i));
    }
    assert Spec.FragmentsConcatenate(pieces, combined, cuts);
  }

  lemma ErrorEvidence(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
    requires |pieces| == |cmd.operands|
    requires forall i: nat | i < |cmd.operands| ::
               pieces[i] ==
               Spec.ErrorPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i))
    requires |cuts| == |cmd.operands| + 1
    requires forall i: nat | i <= |cmd.operands| ::
               cuts[i] == |Core.PrefixErrorsCore(cmd, preFs, preStreams, i)|
    ensures Spec.FragmentsConcatenate(
              pieces,
              Core.PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|),
              cuts
            )
  {
    ghost var combined := Core.PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|);
    assert |cuts| == |pieces| + 1;
    assert cuts[0] == 0;
    assert cuts[|pieces|] == |combined|;
    forall i: nat {:trigger cuts[i + 1], pieces[i]} | i < |pieces|
      ensures cuts[i] <= cuts[i + 1] &&
              cuts[i + 1] <= |combined| &&
              cuts[i + 1] == cuts[i] + |pieces[i]| &&
              combined[cuts[i]..cuts[i + 1]] == pieces[i]
    {
      ErrorSegment(cmd, preFs, preStreams, |cmd.operands|, i);
      assert cuts[i] == |Core.PrefixErrorsCore(cmd, preFs, preStreams, i)|;
      assert cuts[i + 1] == |Core.PrefixErrorsCore(cmd, preFs, preStreams, i + 1)|;
      assert pieces[i] == Spec.ErrorPieceSpec(cmd.operands[i], Core.ReadResultCore(cmd, preFs, preStreams, i));
    }
    assert Spec.FragmentsConcatenate(pieces, combined, cuts);
  }
  lemma {:induction false} BuildRunWitness(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ) returns (
      observations: map<nat, BenchWorld.IOResult<BenchWorld.Bytes>>,
      outputPieces: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat>,
      errorPieces: seq<BenchWorld.Bytes>,
      errorCuts: seq<nat>
    )
    ensures Spec.FileObservationRelation(cmd, preFs, preStreams, observations)
    ensures Spec.PieceSequencesRelation(cmd, observations, outputPieces, errorPieces)
    ensures Spec.FragmentsConcatenate(
              outputPieces,
              Core.PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|),
              outputCuts
            )
    ensures Spec.FragmentsConcatenate(
              errorPieces,
              Core.PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|),
              errorCuts
            )
  {
    observations := map[];
    outputPieces := [];
    outputCuts := [0];
    errorPieces := [];
    errorCuts := [0];

    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant forall j: nat :: j in observations.Keys <==> j < i
      invariant forall j: nat | j < i ::
                  observations[j] == Core.ReadResultCore(cmd, preFs, preStreams, j)
      invariant |outputPieces| == i
      invariant |errorPieces| == i
      invariant forall j: nat | j < i ::
                  outputPieces[j] ==
                  Spec.OutputPieceSpec(cmd.operands[j], observations[j]) &&
                  errorPieces[j] ==
                  Spec.ErrorPieceSpec(cmd.operands[j], observations[j])
      invariant |outputCuts| == i + 1
      invariant forall j: nat | j <= i ::
                  outputCuts[j] == |Core.PrefixOutputCore(cmd, preFs, preStreams, j)|
      invariant |errorCuts| == i + 1
      invariant forall j: nat | j <= i ::
                  errorCuts[j] == |Core.PrefixErrorsCore(cmd, preFs, preStreams, j)|
      decreases |cmd.operands| - i
    {
      ghost var result := Core.ReadResultCore(cmd, preFs, preStreams, i);
      ghost var outputPiece := Spec.OutputPieceSpec(cmd.operands[i], result);
      ghost var errorPiece := Spec.ErrorPieceSpec(cmd.operands[i], result);

      observations := observations[i := result];
      outputPieces := outputPieces + [outputPiece];
      errorPieces := errorPieces + [errorPiece];
      outputCuts := outputCuts + [|Core.PrefixOutputCore(cmd, preFs, preStreams, i + 1)|];
      errorCuts := errorCuts + [|Core.PrefixErrorsCore(cmd, preFs, preStreams, i + 1)|];
      forall j: nat | j <= i + 1
        ensures outputCuts[j] == |Core.PrefixOutputCore(cmd, preFs, preStreams, j)|
        ensures errorCuts[j] == |Core.PrefixErrorsCore(cmd, preFs, preStreams, j)|
      {
        if j <= i {
          assert j < |outputCuts| - 1;
          assert j < |errorCuts| - 1;
        } else {
          assert j == i + 1;
        }
      }
      i := i + 1;
    }
    OutputEvidence(cmd, preFs, preStreams, outputPieces, outputCuts);
    ErrorEvidence(cmd, preFs, preStreams, errorPieces, errorCuts);
  }

  lemma HadErrorExists(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    count: nat
  )
    requires count <= |cmd.operands|
    ensures Core.PrefixHadErrorCore(cmd, preFs, preStreams, count) <==>
            (exists i: nat ::
               i < count && Core.ReadResultCore(cmd, preFs, preStreams, i).Err?)
    decreases count
  {
    if count > 0 {
      HadErrorExists(cmd, preFs, preStreams, count - 1);
    }
  }

  lemma RunWitnessRefines(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    observations: map<nat, BenchWorld.IOResult<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorCuts: seq<nat>,
    exit: int
  )
    requires Spec.FileObservationRelation(cmd, preFs, preStreams, observations)
    requires Spec.PieceSequencesRelation(cmd, observations, outputPieces, errorPieces)
    requires Spec.FragmentsConcatenate(
               outputPieces,
               Core.PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|),
               outputCuts
             )
    requires Spec.FragmentsConcatenate(
               errorPieces,
               Core.PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|),
               errorCuts
             )
    requires exit ==
             (if Core.PrefixHadErrorCore(cmd, preFs, preStreams, |cmd.operands|) then 1 else 0)
    ensures Spec.RunRelation(
              cmd,
              preFs, preStreams,
              Core.PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|),
              Core.PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|),
              exit
            )
  {
    HadErrorExists(cmd, preFs, preStreams, |cmd.operands|);
    assert forall i: nat | i < |cmd.operands| ::
        observations[i] == Core.ReadResultCore(cmd, preFs, preStreams, i);
    assert (exists i: nat ::
              i < |cmd.operands| && observations[i].Err?) <==>
           (exists i: nat ::
              i < |cmd.operands| && Core.ReadResultCore(cmd, preFs, preStreams, i).Err?);
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.DuCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun {
      ghost var observations, outputPieces, outputCuts, errorPieces, errorCuts :=
        BuildRunWitness(cmd, old(io.fs()), old(io.trustedStreams()));
      RunWitnessRefines(
        cmd,
        old(io.fs()), old(io.trustedStreams()),
        observations,
        outputPieces,
        outputCuts,
        errorPieces,
        errorCuts,
        exit
      );
    }
  }
}
