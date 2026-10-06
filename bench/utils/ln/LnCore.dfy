include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"
include "LnSpec.dfy"

module LnCore {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LnSchema
  import Spec = LnSpec

  function LinkNameIsDirectoryFs(
    fs: BenchWorld.FileSystem, path: BenchWorld.Path
  ): bool
  {
    match IOContract.ResolvePathForMetadataFields(fs, path, true)
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      (match BenchWorld.FsNodeAt(fs, resolved)
       case Directory(_, _, _) => true
       case _ => false)
    case Err(_) => false
  }

  function CoreDestination(
    fs: BenchWorld.FileSystem, operands: seq<string>
  ): string
    requires 1 <= |operands| <= 2
  {
    if |operands| == 1 then Spec.InDirectory(".", operands[0])
    else if operands[0] == "" then operands[1]
    else if LinkNameIsDirectoryFs(fs, operands[1]) then
      Spec.InDirectory(operands[1], operands[0])
    else operands[1]
  }

  lemma DirectoryProbeMatchesCore(
    fs: BenchWorld.FileSystem, path: BenchWorld.Path,
    ok: bool, isDir: bool, err: int
  )
    requires IOContract.IsDirectoryStrictContractFields(fs, path, true, ok, isDir, err)
    ensures (ok && isDir) == LinkNameIsDirectoryFs(fs, path)
  {
    match IOContract.ResolvePathForMetadataFields(fs, path, true)
    case Ok(resolved) =>
      assert ok;
      assert BenchWorld.FsContainsPath(fs, resolved);
    case Err(_) =>
      assert !ok;
  }

  ghost predicate CoreStepSummary(
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
  {
    if symbolic then
      exists ok: bool, err: int ::
        IOContract.CreateSymlinkContractFields(
          beforeFs, now, destination, source, ok, err, afterFs) &&
        diagnostic == (if ok then [] else
          Spec.CreateSymlinkErrorMessageSpec(destination, source, err)) &&
        success == ok
    else
      exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
        IOContract.IsDirectoryStrictContractFields(
          beforeFs, source, false, sourceOk, sourceIsDir, sourceErr) &&
        (if !sourceOk then
           afterFs == beforeFs &&
           diagnostic == Spec.FailedAccessMessageSpec(source, sourceErr) &&
           !success
         else if sourceIsDir then
           afterFs == beforeFs &&
           diagnostic == Spec.HardDirectoryMessageSpec(source) &&
           !success
         else
           exists ok: bool, err: int ::
             IOContract.CreateHardLinkSpec(
               beforeFs, now, trustedFilesystem, afterFs,
               source, destination, ok, err) &&
             diagnostic == (if ok then [] else
               Spec.CreateHardLinkErrorMessageSpec(source, destination, err)) &&
             success == ok)
  }

  ghost predicate CoreBatchSummary(
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
  {
    exists states: seq<BenchWorld.FileSystem>,
           diagnostics: seq<BenchWorld.Bytes>,
           results: seq<bool>,
           pieces: seq<BenchWorld.Bytes>,
           stepResults: seq<bool> ::
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
          CoreStepSummary(
            states[i], states[i + 1], now, trustedFilesystem,
            sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
            pieces[i], stepResults[i]) &&
          diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
          results[i + 1] == (results[i] && stepResults[i]))
  }

  lemma AppendAssociative<T>(left: seq<T>, middle: seq<T>, right: seq<T>)
    ensures (left + middle) + right == left + (middle + right)
  {
  }

  twostate predicate CoreSummary(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() && exit == 1
    else if |cmd.operands| > 2 then
      var target := cmd.operands[|cmd.operands| - 1];
      io.stdout() == old(io.stdout()) &&
      (exists targetOk: bool, targetIsDir: bool, targetErr: int ::
        IOContract.IsDirectoryStrictContractFields(
          old(io.fs()), target, true, targetOk, targetIsDir, targetErr) &&
        (if !(targetOk && targetIsDir) then
           io.fs() == old(io.fs()) &&
           io.stderr() == old(io.stderr()) +
             Spec.TargetDirectoryErrorMessageSpec(target, if targetOk then 20 else targetErr) &&
           exit == 1
         else
           exists diagnostic: BenchWorld.Bytes, success: bool
             {:trigger CoreBatchSummary(old(io.fs()), io.fs(), old(io.now()),
               old(io.trustedFilesystem()), cmd.operands[..|cmd.operands| - 1],
               target, cmd.symbolic, diagnostic, success)} ::
             CoreBatchSummary(
               old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
               cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
               diagnostic, success) &&
             io.stderr() == old(io.stderr()) + diagnostic &&
             exit == (if success then 0 else 1)))
    else
      var source := cmd.operands[0];
      var destination := CoreDestination(old(io.fs()), cmd.operands);
      io.stdout() == old(io.stdout()) &&
      (exists diagnostic: BenchWorld.Bytes, success: bool
        {:trigger CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
          old(io.trustedFilesystem()), source, destination, cmd.symbolic,
          diagnostic, success)} ::
        CoreStepSummary(
          old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
          source, destination, cmd.symbolic, diagnostic, success) &&
        io.stderr() == old(io.stderr()) + diagnostic &&
        exit == (if success then 0 else 1))
  }

  method {:isolate_assertions} RunBatch(
    sources: seq<string>, target: string, symbolic: bool, io: BenchIO.IO
  ) returns (diagnostic: BenchWorld.Bytes, allOk: bool)
    modifies io.fsRegion, io.stderrRegion, io.statusObservationsRegion
    ensures CoreBatchSummary(
      old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
      sources, target, symbolic, diagnostic, allOk)
    ensures io.stderr() == old(io.stderr()) + diagnostic
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preTrusted := io.trustedFilesystem();
    ghost var preStderr := io.stderr();
    ghost var states := [io.fs()];
    ghost var diagnostics: seq<BenchWorld.Bytes> := [[]];
    ghost var results := [true];
    ghost var pieces: seq<BenchWorld.Bytes> := [];
    ghost var stepResults: seq<bool> := [];
    diagnostic := [];
    allOk := true;
    var i := 0;
    while i < |sources|
      invariant 0 <= i <= |sources|
      invariant |states| == i + 1 && states[0] == preFs && states[i] == io.fs()
      invariant |diagnostics| == i + 1 && diagnostics[0] == []
      invariant diagnostics[i] == diagnostic
      invariant io.stderr() == preStderr + diagnostic
      invariant |results| == i + 1 && results[0] && results[i] == allOk
      invariant |pieces| == i && |stepResults| == i
      invariant io.now() == preNow && io.trustedFilesystem() == preTrusted
      invariant forall j: nat :: j < i ==>
          CoreStepSummary(
            states[j], states[j + 1], preNow, preTrusted,
            sources[j], Spec.InDirectory(target, sources[j]), symbolic,
            pieces[j], stepResults[j]) &&
          diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
          results[j + 1] == (results[j] && stepResults[j])
      decreases |sources| - i
    {
      var source := sources[i];
      var destination := Spec.InDirectory(target, source);
      ghost var beforeStepFs := io.fs();
      var piece: BenchWorld.Bytes := [];
      var stepOk := false;
      if symbolic {
        var createSymlinkResult := io.CreateSymlink(destination, source);
        var ok := createSymlinkResult.Ok?;
        var err := IOContract.ResultErrno(createSymlinkResult);
        stepOk := ok;
        if !ok {
          piece := Spec.CreateSymlinkErrorMessageSpec(destination, source, err);
          var _ := io.WriteStderr(piece, BenchWorld.ThrowOnError);
        }
        assert CoreStepSummary(
          beforeStepFs, io.fs(), preNow, preTrusted,
          source, destination, symbolic, piece, stepOk);
      } else {
        var getFileStatusResult := io.GetFileStatus(source, false);
        var sourceOk := getFileStatusResult.Ok?;
        var sourceStatus := IOContract.ResultValue(getFileStatusResult, BenchWorld.DEFAULT_FILE_STATUS);
        var sourceErr := IOContract.ResultErrno(getFileStatusResult);
        var sourceIsDir := sourceStatus.kind == BenchWorld.DirectoryKind;
        IOContract.FileStatusStructureImpliesMetadata(
          beforeStepFs, source, false, sourceOk, sourceStatus, sourceErr);
        if !sourceOk {
          piece := Spec.FailedAccessMessageSpec(source, sourceErr);
          var _ := io.WriteStderr(piece, BenchWorld.ThrowOnError);
        } else if sourceIsDir {
          piece := Spec.HardDirectoryMessageSpec(source);
          var _ := io.WriteStderr(piece, BenchWorld.ThrowOnError);
        } else {
          var createHardLinkResult := io.CreateHardLink(source, destination);
          var ok := createHardLinkResult.Ok?;
          var err := IOContract.ResultErrno(createHardLinkResult);
          stepOk := ok;
          if !ok {
            piece := Spec.CreateHardLinkErrorMessageSpec(source, destination, err);
            var _ := io.WriteStderr(piece, BenchWorld.ThrowOnError);
          }
          assert IOContract.CreateHardLinkSpec(
            beforeStepFs, preNow, preTrusted,
            io.fs(), source, destination, ok, err);
        }
        assert IOContract.IsDirectoryStrictContractFields(
          beforeStepFs, source, false, sourceOk, sourceIsDir, sourceErr);
        assert CoreStepSummary(
          beforeStepFs, io.fs(), preNow, preTrusted,
          source, destination, symbolic, piece, stepOk);
      }
      assert io.stderr() == (preStderr + diagnostic) + piece;
      AppendAssociative(preStderr, diagnostic, piece);
      assert io.stderr() == preStderr + (diagnostic + piece);
      states := states + [io.fs()];
      diagnostics := diagnostics + [diagnostics[i] + piece];
      results := results + [results[i] && stepOk];
      pieces := pieces + [piece];
      stepResults := stepResults + [stepOk];
      diagnostic := diagnostic + piece;
      allOk := allOk && stepOk;
      assert forall j: nat :: j < i + 1 ==>
          CoreStepSummary(
            states[j], states[j + 1], preNow, preTrusted,
            sources[j], Spec.InDirectory(target, sources[j]), symbolic,
            pieces[j], stepResults[j]) &&
          diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
          results[j + 1] == (results[j] && stepResults[j]) by {
        forall j: nat | j < i + 1
          ensures
            CoreStepSummary(
              states[j], states[j + 1], preNow, preTrusted,
              sources[j], Spec.InDirectory(target, sources[j]), symbolic,
              pieces[j], stepResults[j]) &&
            diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
            results[j + 1] == (results[j] && stepResults[j])
        {
        }
      }
      i := i + 1;
    }
    assert CoreBatchSummary(
      preFs, io.fs(), preNow, preTrusted, sources, target,
      symbolic, diagnostic, allOk);
  }

  method {:isolate_assertions} RunCore(raw: Schema.LnCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preTrusted := io.trustedFilesystem();
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
    if |cmd.operands| == 0 {
      var _ := io.WriteStderr(Spec.MissingOperandMessageSpec(), BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if |cmd.operands| > 2 {
      var target := cmd.operands[|cmd.operands| - 1];
      var getFileStatusResult2 := io.GetFileStatus(target, true);
      var targetOk := getFileStatusResult2.Ok?;
      var targetStatus := IOContract.ResultValue(getFileStatusResult2, BenchWorld.DEFAULT_FILE_STATUS);
      var targetErr := IOContract.ResultErrno(getFileStatusResult2);
      var targetIsDir := targetStatus.kind == BenchWorld.DirectoryKind;
      IOContract.FileStatusStructureImpliesMetadata(
        preFs, target, true, targetOk, targetStatus, targetErr);
      if !(targetOk && targetIsDir) {
        var _ := io.WriteStderr(Spec.TargetDirectoryErrorMessageSpec(
          target, if targetOk then 20 else targetErr), BenchWorld.ThrowOnError);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      }
      var sources := cmd.operands[..|cmd.operands| - 1];
      var diagnostic, allOk := RunBatch(sources, target, cmd.symbolic, io);
      exit := if allOk then 0 else 1;
      assert io.stdout() == preStdout;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var source := cmd.operands[0];
    var destination: string;
    var dirOk := false;
    var dirIsDir := false;
    var dirErr := 0;
    if |cmd.operands| == 1 {
      destination := Spec.InDirectory(".", source);
    } else if source == "" {
      destination := cmd.operands[1];
    } else {
      var status: BenchWorld.FileStatus;
      var getFileStatusResult3 := io.GetFileStatus(cmd.operands[1], true);
      dirOk := getFileStatusResult3.Ok?;
      status := IOContract.ResultValue(getFileStatusResult3, BenchWorld.DEFAULT_FILE_STATUS);
      dirErr := IOContract.ResultErrno(getFileStatusResult3);
      dirIsDir := status.kind == BenchWorld.DirectoryKind;
      IOContract.FileStatusStructureImpliesMetadata(
        preFs, cmd.operands[1], true, dirOk, status, dirErr);
      DirectoryProbeMatchesCore(preFs, cmd.operands[1], dirOk, dirIsDir, dirErr);
      destination := if dirOk && dirIsDir then
        Spec.InDirectory(cmd.operands[1], source) else cmd.operands[1];
    }
    assert destination == CoreDestination(preFs, cmd.operands);

    if cmd.symbolic {
      var createSymlinkResult2 := io.CreateSymlink(destination, source);
      var ok := createSymlinkResult2.Ok?;
      var err := IOContract.ResultErrno(createSymlinkResult2);
      var diagnostic: BenchWorld.Bytes := [];
      if ok {
        exit := 0;
      } else {
        diagnostic := Spec.CreateSymlinkErrorMessageSpec(destination, source, err);
        var _ := io.WriteStderr(diagnostic, BenchWorld.ThrowOnError);
        exit := 1;
      }
      assert IOContract.CreateSymlinkContractFields(
        preFs, preNow, destination, source, ok, err, io.fs());
      assert io.stdout() == preStdout;
      assert CoreStepSummary(
        preFs, io.fs(), preNow, preTrusted, source, destination,
        cmd.symbolic, diagnostic, ok);
      assert io.stderr() == preStderr + diagnostic;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var diagnostic: BenchWorld.Bytes := [];
    var success := false;
    var getFileStatusResult4 := io.GetFileStatus(source, false);
    var sourceOk := getFileStatusResult4.Ok?;
    var sourceStatus := IOContract.ResultValue(getFileStatusResult4, BenchWorld.DEFAULT_FILE_STATUS);
    var sourceErr := IOContract.ResultErrno(getFileStatusResult4);
    var sourceIsDir := sourceStatus.kind == BenchWorld.DirectoryKind;
    IOContract.FileStatusStructureImpliesMetadata(
      preFs, source, false, sourceOk, sourceStatus, sourceErr);
    if !sourceOk {
      diagnostic := Spec.FailedAccessMessageSpec(source, sourceErr);
      var _ := io.WriteStderr(diagnostic, BenchWorld.ThrowOnError);
      exit := 1;
    } else if sourceIsDir {
      diagnostic := Spec.HardDirectoryMessageSpec(source);
      var _ := io.WriteStderr(diagnostic, BenchWorld.ThrowOnError);
      exit := 1;
    } else {
      var createHardLinkResult2 := io.CreateHardLink(source, destination);
      var ok := createHardLinkResult2.Ok?;
      var err := IOContract.ResultErrno(createHardLinkResult2);
      assert IOContract.CreateHardLinkSpec(
        preFs, preNow, preTrusted, io.fs(), source, destination, ok, err) by {
      }
      success := ok;
      if ok {
        exit := 0;
      } else {
        diagnostic := Spec.CreateHardLinkErrorMessageSpec(source, destination, err);
        var _ := io.WriteStderr(diagnostic, BenchWorld.ThrowOnError);
        exit := 1;
      }
    }
    assert IOContract.IsDirectoryStrictContractFields(
      preFs, source, false, sourceOk, sourceIsDir, sourceErr);
    assert io.stdout() == preStdout;
    assert CoreStepSummary(
      preFs, io.fs(), preNow, preTrusted, source, destination,
      cmd.symbolic, diagnostic, success);
    assert io.stderr() == preStderr + diagnostic;
    assert CoreSummary(raw, io, exit);
  }
}
