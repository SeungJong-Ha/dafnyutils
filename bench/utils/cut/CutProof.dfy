include "../../core/World.dfy"
include "CutSchema.dfy"
include "CutCore.dfy"
include "CutSpec.dfy"

module CutProof {
  import Result = Results
  import BenchIO
  import BenchWorld
  import Schema = CutSchema
  import Core = CutCore
  import Spec = CutSpec

  lemma InputReadCoreRefines(
    command: Schema.CutCmdRaw,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    index: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires index < |command.inputs|
    requires Core.InputReadCore(
               command, preFs, preStdin, index, result,
               preStreams
             )
    ensures Spec.InputReadRelation(
              command, preFs, preStdin, index, result,
              preStreams
            )
  {
    reveal Core.InputReadCore();
    reveal Spec.InputReadRelation();
  }

  lemma OutputPieceRefines(
    command: Schema.CutCmdRaw,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    ensures match result
            case Ok(data) =>
              Spec.DataSelectionRelation(
                command, data, Core.OutputPiece(command, result)
              )
            case Err(_) =>
              Core.OutputPiece(command, result) == []
  {
    match result
    case Ok(data) =>
      Core.DataSelectionSatisfiesRelation(command, data);
    case Err(_) =>
  }

  twostate lemma {:isolate_assertions} InputTraceCoreRefines(
    command: Schema.CutCmdRaw,
    io: BenchIO.IO,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
    requires Core.InputTraceCore(
               command, old(io.fs()), old(io.stdin()), |command.inputs|,
               readResults, stdoutFragments, stderrFragments,
               old(io.trustedStreams())
             )
    ensures Spec.InputTraceRelation(
              command,
              io,
              readResults,
              Core.JoinFragments(stdoutFragments),
              Core.JoinFragments(stderrFragments),
              exists i: nat | i < |command.inputs| ::
                command.inputs[i].File? && readResults[i].Err?
            )
  {
    reveal Core.InputTraceCore();
    assert forall i: nat :: i < |command.inputs| ==>
                              Spec.InputReadRelation(
                                command, old(io.fs()), old(io.stdin()), i, readResults[i],
                                old(io.trustedStreams())
                              ) &&
                              match command.inputs[i]
                              case Stdin =>
                                (match readResults[i]
                                 case Ok(data) =>
                                   Spec.DataSelectionRelation(
                                     command, data, stdoutFragments[i]
                                   ) &&
                                   stderrFragments[i] == []
                                 case Err(_) => false)
                              case File(path) =>
                                (match readResults[i]
                                 case Ok(data) =>
                                   Spec.DataSelectionRelation(
                                     command, data, stdoutFragments[i]
                                   ) &&
                                   stderrFragments[i] == []
                                 case Err(readError) =>
                                   stdoutFragments[i] == [] &&
                                   stderrFragments[i] ==
                                   Spec.ErrorMessage(path, readError)) by {
      forall i: nat | i < |command.inputs|
        ensures
          Spec.InputReadRelation(
            command, old(io.fs()), old(io.stdin()), i, readResults[i],
            old(io.trustedStreams())
          ) &&
          match command.inputs[i]
          case Stdin =>
            (match readResults[i]
             case Ok(data) =>
               Spec.DataSelectionRelation(
                 command, data, stdoutFragments[i]
               ) &&
               stderrFragments[i] == []
             case Err(_) => false)
          case File(path) =>
            (match readResults[i]
             case Ok(data) =>
               Spec.DataSelectionRelation(
                 command, data, stdoutFragments[i]
               ) &&
               stderrFragments[i] == []
             case Err(readError) =>
               stdoutFragments[i] == [] &&
               stderrFragments[i] ==
               Spec.ErrorMessage(path, readError))
      {
        InputReadCoreRefines(
          command, old(io.fs()), old(io.stdin()), i, readResults[i],
          old(io.trustedStreams())
        );
        OutputPieceRefines(command, readResults[i]);
        match command.inputs[i]
        case Stdin =>
          reveal Core.InputReadCore();
        case File(_) =>
      }
    }

    Core.FragmentCutsSatisfyRelation(stdoutFragments);
    Core.FragmentCutsSatisfyRelation(stderrFragments);
    reveal Spec.InputTraceRelation();
  }

  twostate lemma {:isolate_assertions} CoreSummaryImpliesSpec(
    raw: Schema.CutCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    reveal Spec.Spec();

    if raw.mode == Schema.ModeRun {
      ghost var readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
                stdoutFragments: seq<BenchWorld.Bytes>,
                stderrFragments: seq<BenchWorld.Bytes> :|
        Core.InputTraceCore(
          raw, old(io.fs()), old(io.stdin()), |raw.inputs|,
          readResults, stdoutFragments, stderrFragments,
          old(io.trustedStreams())
        ) &&
        io.stdin() ==
        (if exists i ::
              0 <= i < |raw.inputs| && raw.inputs[i].Stdin?
         then []
         else old(io.stdin())) &&
        io.stdout() ==
        old(io.stdout()) + Core.JoinFragments(stdoutFragments) &&
        io.stderr() ==
        old(io.stderr()) + Core.JoinFragments(stderrFragments) &&
        exit ==
        (if (exists i: nat | i < |raw.inputs| :: raw.inputs[i].File? && readResults[i].Err?)
         then 1
         else 0);
      InputTraceCoreRefines(
        raw, io, readResults, stdoutFragments, stderrFragments
      );
    }
  }
}
