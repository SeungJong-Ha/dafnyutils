include "../../core/World.dfy"
include "../../core/IO.dfy"
include "StatSchema.dfy"
include "StatSpec.dfy"
include "StatCore.dfy"

module StatProof {
  import Result = Results
  import BenchWorld
  import BenchIO
  import IOContract
  import Schema = StatSchema
  import Spec = StatSpec
  import Core = StatCore

  ghost function CapturedObservationProvider(
    captured: seq<Spec.CapturedStatus>
  ): BenchWorld.StatusTimeObservations
  {
    (ordinal: nat, fs: BenchWorld.FileSystem,
     path: BenchWorld.Path, followSymlink: bool) =>
      if ordinal < |captured| then
        match captured[ordinal]
        case CapturedStatusOk(_, _, status) => status.times
        case CapturedStatusErr(_, _, _) => BenchWorld.DEFAULT_FILE_TIMES
      else BenchWorld.DEFAULT_FILE_TIMES
  }

  lemma CapturedStatusSuccessMatchesObserved(
    cmd: Schema.StatCmd,
    fs: BenchWorld.FileSystem,
    captured: seq<Spec.CapturedStatus>,
    index: nat,
    status: BenchWorld.FileStatus
  )
    requires cmd.mode == Schema.ModeRun
    requires Spec.CapturedStatusesStructureRelation(cmd, fs, captured)
    requires index < |captured|
    requires captured[index] == Spec.CapturedStatusOk(
      cmd.files[index], cmd.followSymlink, status)
    ensures IOContract.ObservedFileStatusResultFields(
              CapturedObservationProvider(captured), index, fs,
              cmd.files[index], cmd.followSymlink
            ) == Result.Ok(status)
  {
    reveal Spec.CapturedStatusesStructureRelation();
    reveal IOContract.FileStatusStructureContractFields();
    var expected := IOContract.GetFileStatusResultFields(
      fs, cmd.files[index], cmd.followSymlink
    );
    assert expected.Ok?;
    assert status.(times := expected.v.times) == expected.v;
    assert CapturedObservationProvider(captured)(
      index, fs, cmd.files[index], cmd.followSymlink) == status.times;
    assert expected.v.(times := status.times) == status;
  }

  lemma CapturedStatusFailureMatchesObserved(
    cmd: Schema.StatCmd,
    fs: BenchWorld.FileSystem,
    captured: seq<Spec.CapturedStatus>,
    index: nat,
    errno: int
  )
    requires cmd.mode == Schema.ModeRun
    requires Spec.CapturedStatusesStructureRelation(cmd, fs, captured)
    requires index < |captured|
    requires captured[index] == Spec.CapturedStatusErr(
      cmd.files[index], cmd.followSymlink, errno)
    ensures var result := IOContract.ObservedFileStatusResultFields(
                           CapturedObservationProvider(captured), index, fs,
                           cmd.files[index], cmd.followSymlink
                         );
            result.Err? && IOContract.IOErrorErrno(result.e) == errno
  {
    reveal Spec.CapturedStatusesStructureRelation();
    reveal IOContract.FileStatusStructureContractFields();
  }

  lemma {:isolate_assertions} ObservedResultsSpecImpliesObservedSpec(
    raw: Schema.StatCmdRaw,
    fs: BenchWorld.FileSystem,
    captured: seq<Spec.CapturedStatus>,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int
  )
    requires Spec.ObservedResultsSpec(
      raw, fs, captured, beforeStdout, afterStdout,
      beforeStderr, afterStderr, exit)
    ensures Spec.ObservedSpec(
      raw, fs, CapturedObservationProvider(captured), 0, |captured|,
      beforeStdout, afterStdout, beforeStderr, afterStderr, exit)
  {
    var cmd := Schema.Command(raw);
    reveal Spec.ObservedResultsSpec();
    reveal Spec.CapturedOutputSpec();
    if cmd.mode == Schema.ModeRun {
      var hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes :|
        Spec.RunCapturedFilesRelation(cmd, captured, hadError, out, errOut) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + errOut &&
        exit == (if hadError then 1 else 0);
      reveal Spec.RunCapturedFilesRelation();
      var stdoutFragments: seq<BenchWorld.Bytes>,
          stderrFragments: seq<BenchWorld.Bytes> :|
        |stdoutFragments| == |captured| &&
        |stderrFragments| == |captured| &&
        (forall i: nat | i < |captured| ::
           match captured[i]
           case CapturedStatusOk(_, _, status) =>
             exists rendered: BenchWorld.Bytes ::
               Spec.FormatRenderingRelation(cmd.format, status, rendered) &&
               stdoutFragments[i] == rendered + "\n" && stderrFragments[i] == ""
           case CapturedStatusErr(_, _, errno) =>
             stdoutFragments[i] == "" &&
             stderrFragments[i] == Spec.ErrorMessageSpec(cmd.files[i], errno)) &&
        hadError == (exists i: nat :: i < |captured| && captured[i].CapturedStatusErr?) &&
        out == Spec.ConcatPiecesSpec(stdoutFragments) &&
        errOut == Spec.ConcatPiecesSpec(stderrFragments);
      ghost var observedCmd := Schema.WithStatusObservations(
        cmd, CapturedObservationProvider(captured), 0);
      assert |captured| == |cmd.files|;
      assert forall i: nat | i < |cmd.files| ::
        Spec.FileFragmentRelation(
          observedCmd.format,
          cmd.files[i],
          Spec.StatusResultSpec(observedCmd, fs, i, cmd.files[i]),
          stdoutFragments[i], stderrFragments[i]) by {
        forall i: nat | i < |cmd.files|
          ensures Spec.FileFragmentRelation(
            observedCmd.format,
            cmd.files[i],
            Spec.StatusResultSpec(observedCmd, fs, i, cmd.files[i]),
            stdoutFragments[i], stderrFragments[i])
        {
          match captured[i]
          case CapturedStatusOk(path, followSymlink, status) =>
            assert path == cmd.files[i] && followSymlink == cmd.followSymlink;
            CapturedStatusSuccessMatchesObserved(cmd, fs, captured, i, status);
          case CapturedStatusErr(path, followSymlink, errno) =>
            assert path == cmd.files[i] && followSymlink == cmd.followSymlink;
            CapturedStatusFailureMatchesObserved(cmd, fs, captured, i, errno);
        }
      }
      assert ((exists i: nat :: i < |cmd.files| && Spec.StatusResultSpec(observedCmd, fs, i, cmd.files[i]).Err?) <==>
        (exists i: nat :: i < |captured| && captured[i].CapturedStatusErr?)) by {
        if exists i: nat :: i < |cmd.files| &&
            Spec.StatusResultSpec(observedCmd, fs, i, cmd.files[i]).Err? {
          var i: nat :| i < |cmd.files| &&
            Spec.StatusResultSpec(observedCmd, fs, i, cmd.files[i]).Err?;
          match captured[i]
          case CapturedStatusOk(path, followSymlink, status) =>
            assert path == cmd.files[i] && followSymlink == cmd.followSymlink;
            CapturedStatusSuccessMatchesObserved(cmd, fs, captured, i, status);
          case CapturedStatusErr(_, _, _) =>
        }
        if exists i: nat :: i < |captured| && captured[i].CapturedStatusErr? {
          var i: nat :| i < |captured| && captured[i].CapturedStatusErr?;
          match captured[i]
          case CapturedStatusOk(_, _, _) =>
          case CapturedStatusErr(path, followSymlink, errno) =>
            assert path == cmd.files[i] && followSymlink == cmd.followSymlink;
            CapturedStatusFailureMatchesObserved(cmd, fs, captured, i, errno);
        }
      }
      assert Spec.RunFilesRelation(
        observedCmd, cmd.files, fs, hadError, out, errOut);
    }
  }

  lemma FileStepSummaryImpliesFragment(
    cmd: Schema.StatCmd,
    index: nat,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.FileStepSummaryFields(
      cmd, index, path, fs, hadError, out, errOut
    )
    ensures Spec.FileFragmentRelation(
              cmd.format,
              path,
              Spec.StatusResultSpec(cmd, fs, index, path),
              out,
              errOut
            )
    ensures hadError == Spec.StatusResultSpec(cmd, fs, index, path).Err?
  {
    match Spec.StatusResultSpec(cmd, fs, index, path)
    case Ok(_) =>
    case Err(_) =>
  }

  lemma OutputFragmentCutsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>,
    fragment: BenchWorld.Bytes
  )
    requires Spec.OutputFragmentCutsRelation(fragments, output, cuts)
    ensures Spec.OutputFragmentCutsRelation(
              fragments + [fragment], output + fragment, cuts + [|output + fragment|]
            )
  {
    assert forall i: nat {:trigger (cuts + [|output + fragment|])[i],
        (cuts + [|output + fragment|])[i + 1]}
        | i < |fragments + [fragment]| ::
        (cuts + [|output + fragment|])[i] <=
        (cuts + [|output + fragment|])[i + 1] <= |output + fragment| &&
        (output + fragment)[
        (cuts + [|output + fragment|])[i]..
        (cuts + [|output + fragment|])[i + 1]
        ] == (fragments + [fragment])[i] by {
      forall i: nat
        {:trigger (cuts + [|output + fragment|])[i],
        (cuts + [|output + fragment|])[i + 1]}
    | i < |fragments + [fragment]|
        ensures
          (cuts + [|output + fragment|])[i] <=
          (cuts + [|output + fragment|])[i + 1] <= |output + fragment| &&
          (output + fragment)[
          (cuts + [|output + fragment|])[i]..
          (cuts + [|output + fragment|])[i + 1]
          ] == (fragments + [fragment])[i]
      {
        if i < |fragments| {
          assert cuts[i] <= cuts[i + 1] <= |output| &&
                 output[cuts[i]..cuts[i + 1]] == fragments[i];
          assert (output + fragment)[cuts[i]..cuts[i + 1]] ==
                 output[cuts[i]..cuts[i + 1]];
        } else {
          assert i == |fragments|;
          assert cuts[i] == |output|;
          assert (output + fragment)[|output|..|output + fragment|] == fragment;
        }
      }
    }
  }

  lemma ConcatPiecesSnoc(
    pieces: seq<BenchWorld.Bytes>,
    piece: BenchWorld.Bytes
  )
    ensures Spec.ConcatPiecesSpec(pieces + [piece]) ==
            Spec.ConcatPiecesSpec(pieces) + piece
    decreases |pieces|
  {
    if |pieces| > 0 {
      ConcatPiecesSnoc(pieces[1..], piece);
      assert pieces + [piece] == [pieces[0]] + (pieces[1..] + [piece]);
    }
  }

  lemma ErrorExistsSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    prefixError: bool,
    stepError: bool
  )
    requires prefixError == (exists i: nat ::
                               i < |prefix| &&
                               Spec.StatusResultSpec(cmd, fs, i, prefix[i]).Err?)
    requires stepError == Spec.StatusResultSpec(cmd, fs, |prefix|, path).Err?
    ensures (prefixError || stepError) == (exists i: nat ::
                                             i < |prefix + [path]| &&
                                             Spec.StatusResultSpec(
                                               cmd, fs, i, (prefix + [path])[i]
                                             ).Err?)
  {
    if prefixError || stepError {
      if prefixError {
        var i: nat :|
          i < |prefix| &&
          Spec.StatusResultSpec(cmd, fs, i, prefix[i]).Err?;
        assert (prefix + [path])[i] == prefix[i];
      } else {
        assert (prefix + [path])[|prefix|] == path;
      }
    }
    if (exists i: nat ::
          i < |prefix + [path]| &&
          Spec.StatusResultSpec(cmd, fs, i, (prefix + [path])[i]).Err?)
    {
      var i: nat :|
        i < |prefix + [path]| &&
        Spec.StatusResultSpec(cmd, fs, i, (prefix + [path])[i]).Err?;
      if i < |prefix| {
        assert exists j: nat ::
            j < |prefix| &&
            Spec.StatusResultSpec(cmd, fs, j, prefix[j]).Err?;
      } else {
        assert i == |prefix|;
        assert (prefix + [path])[i] == path;
      }
    }
  }

  lemma FileFragmentsSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires |stdoutFragments| == |prefix|
    requires |stderrFragments| == |prefix|
    requires forall i: nat | i < |prefix| ::
               Spec.FileFragmentRelation(
                 cmd.format,
                 prefix[i],
                 Spec.StatusResultSpec(cmd, fs, i, prefix[i]),
                 stdoutFragments[i],
                 stderrFragments[i]
               )
    requires Spec.FileFragmentRelation(
               cmd.format,
               path,
               Spec.StatusResultSpec(cmd, fs, |prefix|, path),
               stepOut,
               stepErrOut
             )
    ensures forall i: nat | i < |prefix + [path]| ::
              Spec.FileFragmentRelation(
                cmd.format,
                (prefix + [path])[i],
                Spec.StatusResultSpec(cmd, fs, i, (prefix + [path])[i]),
                (stdoutFragments + [stepOut])[i],
                (stderrFragments + [stepErrOut])[i]
              )
  {
    forall i: nat | i < |prefix + [path]|
      ensures Spec.FileFragmentRelation(
                cmd.format,
                (prefix + [path])[i],
                Spec.StatusResultSpec(cmd, fs, i, (prefix + [path])[i]),
                (stdoutFragments + [stepOut])[i],
                (stderrFragments + [stepErrOut])[i]
              )
    {
      if i < |prefix| {
        assert (prefix + [path])[i] == prefix[i];
      } else {
        assert i == |prefix|;
        assert (prefix + [path])[i] == path;
      }
    }
  }

  lemma {:induction false} RunFilesRelationSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    prefixError: bool,
    prefixOut: BenchWorld.Bytes,
    prefixErrOut: BenchWorld.Bytes,
    stepError: bool,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires Spec.RunFilesRelation(cmd, prefix, fs, prefixError, prefixOut, prefixErrOut)
    requires Core.FileStepSummaryFields(
      cmd, |prefix|, path, fs, stepError, stepOut, stepErrOut
    )
    ensures Spec.RunFilesRelation(
              cmd,
              prefix + [path],
              fs,
              prefixError || stepError,
              prefixOut + stepOut,
              prefixErrOut + stepErrOut
            )
  {
    var stdoutFragments: seq<BenchWorld.Bytes>,
        stderrFragments: seq<BenchWorld.Bytes> :|
      |stdoutFragments| == |prefix| &&
      |stderrFragments| == |prefix| &&
      (forall i: nat | i < |prefix| ::
         Spec.FileFragmentRelation(
           cmd.format,
           prefix[i],
           Spec.StatusResultSpec(cmd, fs, i, prefix[i]),
           stdoutFragments[i], stderrFragments[i]
         )) &&
      prefixError == (exists i: nat ::
                        i < |prefix| &&
                        Spec.StatusResultSpec(cmd, fs, i, prefix[i]).Err?) &&
      prefixOut == Spec.ConcatPiecesSpec(stdoutFragments) &&
      prefixErrOut == Spec.ConcatPiecesSpec(stderrFragments);

    var observation := Spec.StatusResultSpec(cmd, fs, |prefix|, path);
    FileStepSummaryImpliesFragment(
      cmd, |prefix|, path, fs, stepError, stepOut, stepErrOut
    );
    ConcatPiecesSnoc(stdoutFragments, stepOut);
    ConcatPiecesSnoc(stderrFragments, stepErrOut);
    ErrorExistsSnoc(cmd, prefix, path, fs, prefixError, stepError);
    FileFragmentsSnoc(
      cmd,
      prefix,
      path,
      fs,
      stdoutFragments,
      stderrFragments,
      stepOut,
      stepErrOut
    );
    assert Spec.RunFilesRelation(
      cmd, prefix + [path], fs, prefixError || stepError,
      prefixOut + stepOut, prefixErrOut + stepErrOut
    ) by {
      assert |stdoutFragments + [stepOut]| == |prefix + [path]|;
      assert |stderrFragments + [stepErrOut]| == |prefix + [path]|;
    }
  }

  lemma {:isolate_assertions} RunFilesSummaryImpliesRelation(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.RunFilesSummaryFields(cmd, files, fs, hadError, out, errOut)
    ensures Spec.RunFilesRelation(cmd, files, fs, hadError, out, errOut)
    decreases |files|
  {
    if |files| == 0 {
      assert Spec.ConcatPiecesSpec([]) == [];
    } else {
      var prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes,
          stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ) &&
        Core.FileStepSummaryFields(
          cmd, |files| - 1, files[|files| - 1], fs,
          stepError, stepOut, stepErrOut
        ) &&
        hadError == (prefixError || stepError) &&
        out == prefixOut + stepOut && errOut == prefixErrOut + stepErrOut;

      RunFilesSummaryImpliesRelation(
        cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
      );
      var path := files[|files| - 1];
      RunFilesRelationSnoc(
        cmd,
        files[..|files| - 1],
        path,
        fs,
        prefixError,
        prefixOut,
        prefixErrOut,
        stepError,
        stepOut,
        stepErrOut
      );
      assert files[|files| - 1..] == [path];
      calc {
         files;
      == files[..|files| - 1] + files[|files| - 1..];
      == files[..|files| - 1] + [path];
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.StatCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.WithStatusObservations(
      Schema.Command(raw), io.statusObservations(), old(io.statusCursor())
    );
    if cmd.mode == Schema.ModeRun {
      var hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(cmd, cmd.files, old(io.fs()), hadError, out, errOut) &&
        io.stdout() == old(io.stdout()) + out && io.stderr() == old(io.stderr()) + errOut &&
        exit == (if hadError then 1 else 0);
      RunFilesSummaryImpliesRelation(cmd, cmd.files, old(io.fs()), hadError, out, errOut);
    }
  }
}
