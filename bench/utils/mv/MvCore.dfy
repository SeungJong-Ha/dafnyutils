include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "MvPathCore.dfy"
include "MvSchema.dfy"
include "MvSpec.dfy"

module MvCore {
  import Errno = Errnos
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import BasenameCore = MvPathCore
  import DirnameCore = MvPathCore
  import Schema = MvSchema
  import Spec = MvSpec


  ghost function ShowActionMessage(verbose: bool, debug: bool): bool
  {
    verbose || debug
  }

  ghost function SkipStdout(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then Spec.DebugSkipMessageSpec(target) else []
  }

  function SourceRenameDiagnosticErr(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  ): int
  {
    if target == "" then
      if sourceIsDir then Errno.EBUSY else Errno.EISDIR
    else
      renameErr
  }

  function SourceLeafName(source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    if leaf == "" then source else leaf
  } by method {
    var leaf := BenchWorld.LeafName(source);
    return if leaf == "" then source else leaf;
  }

  lemma AllSlashesFalseAt(text: string, i: nat, j: nat)
    requires i <= j < |text|
    requires forall k :: i <= k < j ==> text[k] == '/'
    requires text[j] != '/'
    ensures !AllSlashes(text, i)
    decreases j - i
  {
    if i < j {
      AllSlashesFalseAt(text, i + 1, j);
    }
  }

  lemma AllSlashesTrueFrom(text: string, i: nat)
    requires i <= |text|
    requires forall k :: i <= k < |text| ==> text[k] == '/'
    ensures AllSlashes(text, i)
    decreases |text| - i
  {
    if i < |text| {
      AllSlashesTrueFrom(text, i + 1);
    }
  }

  function AllSlashes(text: string, i: nat): bool
    decreases |text| - i
  {
    if i >= |text| then
      true
    else if text[i] != '/' then
      false
    else
      AllSlashes(text, i + 1)
  } by method {
    if i >= |text| {
      return true;
    }
    var j := i;
    while j < |text|
      invariant i <= j <= |text|
      invariant forall k | i <= k < j :: text[k] == '/'
      decreases |text| - j
    {
      if text[j] != '/' {
        AllSlashesFalseAt(text, i, j);
        return false;
      }
      j := j + 1;
    }
    AllSlashesTrueFrom(text, i);
    return true;
  }

  lemma TrimTrailingSlashesLoop(text: string, end: nat, i: nat)
    requires i <= end <= |text|
    requires forall k :: i <= k < end ==> text[k] == '/'
    requires i == 0 || text[i - 1] != '/'
    ensures TrimTrailingSlashes(text, end) == text[..i]
    decreases end - i
  {
    if end == i {
    } else {
      TrimTrailingSlashesLoop(text, end - 1, i);
    }
  }

  function TrimTrailingSlashes(text: string, end: nat): string
    requires end <= |text|
    decreases end
  {
    if end == 0 then
      ""
    else if text[end - 1] == '/' then
      TrimTrailingSlashes(text, end - 1)
    else
      text[..end]
  } by method {
    var i: nat := end;
    while i > 0 && text[i - 1] == '/'
      invariant i <= end <= |text|
      invariant forall k | i <= k < end :: text[k] == '/'
      decreases i
    {
      i := i - 1;
    }
    TrimTrailingSlashesLoop(text, end, i);
    return text[..i];
  }

  function NormalizeSource(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes then
      source
    else if source == "" then
      source
    else if AllSlashes(source, 0) then
      "/"
    else
      TrimTrailingSlashes(source, |source|)
  } by method {
    if !stripTrailingSlashes {
      return source;
    }
    if source == "" {
      return source;
    }
    if AllSlashes(source, 0) {
      return "/";
    }
    return TrimTrailingSlashes(source, |source|);
  }

  function TargetInDirectory(directory: string, source: string): string
  {
    BenchWorld.AppendPath(directory, SourceLeafName(source))
  } by method {
    return BenchWorld.AppendPath(directory, SourceLeafName(source));
  }

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
  } by method {
    if d == 0 {
      return '0';
    }
    if d == 1 {
      return '1';
    }
    if d == 2 {
      return '2';
    }
    if d == 3 {
      return '3';
    }
    if d == 4 {
      return '4';
    }
    if d == 5 {
      return '5';
    }
    if d == 6 {
      return '6';
    }
    if d == 7 {
      return '7';
    }
    if d == 8 {
      return '8';
    }
    return '9';
  }

  function DecimalNat(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      DecimalNat(n / 10) + [DigitChar(n % 10)]
  } by method {
    var remaining: nat := n;
    var suffix: string := [];
    while remaining >= 10
      invariant DecimalNat(n) == DecimalNat(remaining) + suffix
      decreases remaining
    {
      assert 0 <= remaining % 10;
      assert remaining % 10 < 10;
      suffix := [DigitChar(remaining % 10)] + suffix;
      assert 0 <= remaining / 10;
      remaining := remaining / 10;
    }
    assert remaining < 10;
    return [DigitChar(remaining)] + suffix;
  }

  function NumberedBackupPath(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNat(index) + "~"
  } by method {
    return target + ".~" + DecimalNat(index) + "~";
  }

  function SimpleBackupPath(target: string, suffix: string): string
  {
    target + suffix
  } by method {
    return target + suffix;
  }

  function SourceNewer(
    srcSec: int, srcNsec: int, dstSec: int, dstNsec: int
  ): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  } by method {
    return srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec);
  }

  ghost function TargetDirectoryErr(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk then
      if !isDir then Errno.ENOTDIR else statErr
    else
      statErr
  }

  ghost function StepSuccessStdout(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !ShowActionMessage(verbose, debug) then
      []
    else if backupPath == "" then
      Spec.VerboseRenameMessageSpec(source, target)
    else
      Spec.VerboseRenameWithBackupMessageSpec(source, target, backupPath)
  }

  datatype BackupCheckEvidence = BackupCheckEvidence(
    candidate: string,
    found: bool,
    err: int
  )

  ghost predicate StatusCallsFor(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
  {
    Spec.StatusCallsFor(observations, first, calls)
  }

  lemma StatusCallsConcat(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>
  )
    requires StatusCallsFor(observations, first, left)
    requires StatusCallsFor(observations, first + |left|, right)
    ensures StatusCallsFor(observations, first, left + right)
  {
    forall i: nat | i < |left + right|
      ensures IOContract.ObservedFileStatusContractFields(
        observations, first + i, (left + right)[i].fs,
        (left + right)[i].path, (left + right)[i].followSymlink,
        (left + right)[i].ok, (left + right)[i].status,
        (left + right)[i].err
      )
    {
      if i >= |left| {
        assert first + i == first + |left| + (i - |left|);
      }
    }
  }

  lemma StatusCallsSnoc(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    call: Spec.StatusCallEvidence
  )
    requires StatusCallsFor(observations, first, calls)
    requires IOContract.ObservedFileStatusContractFields(
      observations, first + |calls|, call.fs, call.path,
      call.followSymlink, call.ok, call.status, call.err
    )
    ensures StatusCallsFor(observations, first, calls + [call])
  {
    StatusCallsConcat(observations, first, calls, [call]);
  }

  lemma StatusCallsAcrossEqualObservations(
    before: BenchWorld.StatusTimeObservations,
    after: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires before == after
    requires StatusCallsFor(before, first, calls)
    ensures StatusCallsFor(after, first, calls)
  {
    hide StatusCallsFor;
  }

  lemma StatusCallsAtEqualOrdinal(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    equalFirst: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires first == equalFirst
    requires StatusCallsFor(observations, first, calls)
    ensures StatusCallsFor(observations, equalFirst, calls)
  {
    hide StatusCallsFor;
  }

  lemma {:isolate_assertions} StatusCallsAppendObservedStep(
    before: BenchWorld.StatusTimeObservations,
    after: BenchWorld.StatusTimeObservations,
    first: nat,
    prefix: seq<Spec.StatusCallEvidence>,
    step: StepEvidence
  )
    requires before == after
    requires StatusCallsFor(before, first, prefix)
    requires step.firstStatus == first + |prefix|
    requires StatusCallsFor(after, step.firstStatus, step.statusCalls)
    ensures StatusCallsFor(after, first, prefix + step.statusCalls)
  {
    StatusCallsAcrossEqualObservations(before, after, first, prefix);
    StatusCallsAtEqualOrdinal(
      after, step.firstStatus, first + |prefix|, step.statusCalls);
    StatusCallsConcat(after, first, prefix, step.statusCalls);
  }

  lemma StatusCallPrefixSlice(
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>,
    lo: nat,
    hi: nat
  )
    requires lo <= hi <= |left|
    ensures (left + right)[lo..hi] == left[lo..hi]
  {
  }

  lemma StatusCallTail(
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>
  )
    ensures (left + right)[|left|..] == right
  {
  }

  lemma StatusCallConsIndex(
    first: Spec.StatusCallEvidence,
    tail: seq<Spec.StatusCallEvidence>,
    i: nat
  )
    requires 1 <= i <= |tail|
    ensures ([first] + tail)[i] == tail[i - 1]
  {
    StatusCallTail([first], tail);
  }

  lemma {:isolate_assertions} StatusBoundsSnoc(
    first: nat,
    prefixCalls: seq<Spec.StatusCallEvidence>,
    prefixBounds: seq<nat>,
    prefixSteps: seq<StepEvidence>,
    step: StepEvidence,
    nextCalls: seq<Spec.StatusCallEvidence>,
    nextBounds: seq<nat>,
    nextSteps: seq<StepEvidence>
  )
    requires |prefixBounds| == |prefixSteps| + 1
    requires prefixBounds[|prefixSteps|] == first + |prefixCalls|
    requires forall j: nat {:trigger prefixBounds[j]} | j < |prefixSteps| ::
      first <= prefixBounds[j] <= prefixBounds[j + 1] <=
        first + |prefixCalls| &&
      prefixSteps[j].firstStatus == prefixBounds[j] &&
      prefixBounds[j + 1] ==
        prefixBounds[j] + |prefixSteps[j].statusCalls| &&
      prefixCalls[prefixBounds[j] - first ..
                  prefixBounds[j + 1] - first] ==
        prefixSteps[j].statusCalls
    requires step.firstStatus == first + |prefixCalls|
    requires nextCalls == prefixCalls + step.statusCalls
    requires nextBounds == prefixBounds + [first + |nextCalls|]
    requires nextSteps == prefixSteps + [step]
    ensures forall j: nat {:trigger nextBounds[j]} | j < |nextSteps| ::
      first <= nextBounds[j] <= nextBounds[j + 1] <=
        first + |nextCalls| &&
      nextSteps[j].firstStatus == nextBounds[j] &&
      nextBounds[j + 1] ==
        nextBounds[j] + |nextSteps[j].statusCalls| &&
      nextCalls[nextBounds[j] - first ..
                nextBounds[j + 1] - first] ==
        nextSteps[j].statusCalls
  {
    StatusCallTail(prefixCalls, step.statusCalls);
    forall j: nat {:trigger nextBounds[j]} | j < |nextSteps|
      ensures first <= nextBounds[j] <= nextBounds[j + 1] <=
                first + |nextCalls| &&
              nextSteps[j].firstStatus == nextBounds[j] &&
              nextBounds[j + 1] ==
                nextBounds[j] + |nextSteps[j].statusCalls| &&
              nextCalls[nextBounds[j] - first ..
                        nextBounds[j + 1] - first] ==
                nextSteps[j].statusCalls
    {
      if j < |prefixSteps| {
        assert nextBounds[j] == prefixBounds[j];
        assert nextBounds[j + 1] == prefixBounds[j + 1];
        assert nextSteps[j] == prefixSteps[j];
        assert prefixBounds[j + 1] <= first + |prefixCalls|;
        StatusCallPrefixSlice(
          prefixCalls, step.statusCalls,
          prefixBounds[j] - first,
          prefixBounds[j + 1] - first);
      } else {
        assert j == |prefixSteps|;
        assert nextBounds[j] == first + |prefixCalls|;
        assert nextCalls[|prefixCalls|..] == step.statusCalls;
      }
    }
  }

  lemma StatusCallsSlice(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    lo: nat,
    hi: nat
  )
    requires StatusCallsFor(observations, first, calls)
    requires lo <= hi <= |calls|
    ensures StatusCallsFor(observations, first + lo, calls[lo..hi])
  {
    forall i: nat | i < |calls[lo..hi]|
      ensures IOContract.ObservedFileStatusContractFields(
        observations, first + lo + i,
        calls[lo..hi][i].fs, calls[lo..hi][i].path,
        calls[lo..hi][i].followSymlink,
        calls[lo..hi][i].ok, calls[lo..hi][i].status,
        calls[lo..hi][i].err)
    {
      assert calls[lo..hi][i] == calls[lo + i];
    }
  }

  ghost function MetadataStatusCall(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  ): Spec.StatusCallEvidence
  {
    Spec.StatusCallEvidence(
      fs, path, followSymlink, evidence.ok, evidence.rawStatus, evidence.err
    )
  }

  datatype MetadataEvidence = MetadataEvidence(
    ghost ordinal: nat,
    ghost rawStatus: BenchWorld.FileStatus,
    ok: bool,
    key: BenchWorld.HostInodeKey,
    links: BenchWorld.LinkCountObservation,
    isDir: bool,
    isSymlink: bool,
    times: BenchWorld.FileTimes,
    err: int
  )

  datatype EntryNameEvidence = EntryNameEvidence(
    parent: string,
    leaf: string,
    parentMetadata: MetadataEvidence
  )

  datatype OptionalMetadataEvidence =
    | NoMetadataEvidence
    | SomeMetadataEvidence(value: MetadataEvidence)

  datatype OptionalEntryNameEvidence =
    | NoEntryNameEvidence
    | FailedEntryNameEvidence(err: int)
    | SomeEntryNameEvidence(
        resolvedPath: string,
        value: EntryNameEvidence
      )

  datatype BackupCollisionEvidence =
    | NoBackupCollisionCheck
    | CheckedBackupCollision(
        sourceNoFollow: MetadataEvidence,
        simpleCandidateFollowed: MetadataEvidence
      )

  datatype SameFileEvidence =
    | NoSameFileCheck
    | CheckedSameFile(
        source: MetadataEvidence,
        target: MetadataEvidence,
        sourceFollowed: OptionalMetadataEvidence,
        sourceEntry: EntryNameEvidence,
        targetEntry: EntryNameEvidence,
        sourceReferentEntry: OptionalEntryNameEvidence,
        backupCollision: BackupCollisionEvidence,
        decision: Spec.SameFileDecision
      )

  datatype BackupSelectionEvidence =
    | NoBackupSelection
    | SelectedBackup(
        backupPath: string,
        checks: seq<BackupCheckEvidence>,
        existingFirstCheckCalled: bool,
        existingFirstFound: bool,
        existingFirstErr: int
      )

  datatype RenameCallEvidence = RenameCallEvidence(
    ok: bool,
    err: int,
    afterFs: BenchWorld.FileSystem
  )

  datatype StepEvidence = StepEvidence(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    sourceOk: bool,
    sourceIsDir: bool,
    sourceErr: int,
    targetExistsCalled: bool,
    targetFound: bool,
    targetExistsErr: int,
    sameFile: SameFileEvidence,
    backup: BackupSelectionEvidence,
    renames: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem,
    ghost firstStatus: nat,
    ghost statusCalls: seq<Spec.StatusCallEvidence>
  )

  datatype BatchEvidence = BatchEvidence(
    steps: seq<StepEvidence>,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    ghost firstStatus: nat,
    ghost statusCalls: seq<Spec.StatusCallEvidence>,
    ghost statusBounds: seq<nat>
  )

  datatype DirectoryStatusEvidence =
    | FailedDirectoryStatus(call: Spec.StatusCallEvidence)
    | SuccessfulDirectoryStatus(
        call: Spec.StatusCallEvidence,
        batch: BatchEvidence
      )

  datatype RunStatusEvidence =
    | NoRunStatus
    | DirectoryRunStatus(value: DirectoryStatusEvidence)
    | DirectMoveStatus(step: StepEvidence)
    | ProbedMoveStatus(call: Spec.StatusCallEvidence, step: StepEvidence)

  datatype StatusTranscript = StatusTranscript(
    first: nat,
    calls: seq<Spec.StatusCallEvidence>
  )

  ghost predicate BatchStatusEvidenceFor(
    observations: BenchWorld.StatusTimeObservations,
    evidence: BatchEvidence
  )
  {
    |evidence.statusBounds| == |evidence.steps| + 1 &&
    evidence.statusBounds[0] == evidence.firstStatus &&
    evidence.statusBounds[|evidence.steps|] ==
      evidence.firstStatus + |evidence.statusCalls| &&
    StatusCallsFor(observations, evidence.firstStatus, evidence.statusCalls) &&
    forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
      evidence.firstStatus <= evidence.statusBounds[i] <=
        evidence.statusBounds[i + 1] <=
        evidence.firstStatus + |evidence.statusCalls| &&
      evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
      evidence.statusBounds[i + 1] ==
        evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
      evidence.statusCalls[
        evidence.statusBounds[i] - evidence.firstStatus ..
        evidence.statusBounds[i + 1] - evidence.firstStatus
      ] == evidence.steps[i].statusCalls
  }

  lemma PackageBatchStatusEvidence(
    observations: BenchWorld.StatusTimeObservations,
    evidence: BatchEvidence
  )
    requires |evidence.statusBounds| == |evidence.steps| + 1
    requires evidence.statusBounds[0] == evidence.firstStatus
    requires evidence.statusBounds[|evidence.steps|] ==
             evidence.firstStatus + |evidence.statusCalls|
    requires StatusCallsFor(observations, evidence.firstStatus,
                            evidence.statusCalls)
    requires forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
      evidence.firstStatus <= evidence.statusBounds[i] <=
        evidence.statusBounds[i + 1] <=
          evidence.firstStatus + |evidence.statusCalls| &&
      evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
      evidence.statusBounds[i + 1] ==
        evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
      evidence.statusCalls[
        evidence.statusBounds[i] - evidence.firstStatus ..
        evidence.statusBounds[i + 1] - evidence.firstStatus
      ] == evidence.steps[i].statusCalls
    ensures BatchStatusEvidenceFor(observations, evidence)
  {
  }

  lemma {:induction false} BatchStatusEvidenceFromParts(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>,
    steps: seq<StepEvidence>,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
    requires |bounds| == |steps| + 1
    requires bounds[0] == first
    requires bounds[|steps|] == first + |calls|
    requires StatusCallsFor(observations, first, calls)
    requires forall i: nat {:trigger bounds[i]} | i < |steps| ::
      first <= bounds[i] <= bounds[i + 1] <= first + |calls| &&
      steps[i].firstStatus == bounds[i] &&
      bounds[i + 1] == bounds[i] + |steps[i].statusCalls| &&
      calls[bounds[i] - first .. bounds[i + 1] - first] ==
        steps[i].statusCalls
    ensures BatchStatusEvidenceFor(
      observations,
      BatchEvidence(steps, fsBounds, outcomes, stdoutFragments,
                    stderrFragments, first, calls, bounds))
  {
    var evidence := BatchEvidence(steps, fsBounds, outcomes,
      stdoutFragments, stderrFragments, first, calls, bounds);
    assert forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
      evidence.firstStatus <= evidence.statusBounds[i] <=
        evidence.statusBounds[i + 1] <=
          evidence.firstStatus + |evidence.statusCalls| &&
      evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
      evidence.statusBounds[i + 1] ==
        evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
      evidence.statusCalls[
        evidence.statusBounds[i] - evidence.firstStatus ..
        evidence.statusBounds[i + 1] - evidence.firstStatus
      ] == evidence.steps[i].statusCalls by {
      forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps|
        ensures evidence.firstStatus <= evidence.statusBounds[i] <=
                  evidence.statusBounds[i + 1] <=
                    evidence.firstStatus + |evidence.statusCalls| &&
                evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
                evidence.statusBounds[i + 1] ==
                  evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
                evidence.statusCalls[
                  evidence.statusBounds[i] - evidence.firstStatus ..
                  evidence.statusBounds[i + 1] - evidence.firstStatus
                ] == evidence.steps[i].statusCalls
      {
        assert bounds[i] == evidence.statusBounds[i];
        assert bounds[i + 1] == evidence.statusBounds[i + 1];
        assert steps[i] == evidence.steps[i];
        assert calls[bounds[i] - first .. bounds[i + 1] - first] ==
          steps[i].statusCalls;
      }
    }
    PackageBatchStatusEvidence(observations, evidence);
  }

  ghost predicate BatchMoveStatusEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    observations: BenchWorld.StatusTimeObservations,
    evidence: BatchEvidence
  )
  {
    BatchStatusEvidenceFor(observations, evidence) &&
    |evidence.steps| == |sources| &&
    (forall i: nat | i < |sources| ::
      var normalizedSource :=
        NormalizeSource(sources[i], cmd.stripTrailingSlashes);
      StepStatusEvidenceFor(
        normalizedSource,
        TargetInDirectory(directory, normalizedSource),
        cmd,
        evidence.steps[i]
      ))
  }

  ghost function MakeStepEvidence(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    failed: bool,
    sourceOk: bool,
    sourceIsDir: bool,
    sourceErr: int,
    targetExistsCalled: bool,
    targetFound: bool,
    targetExistsErr: int,
    sameFile: SameFileEvidence,
    backup: BackupSelectionEvidence,
    renames: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem,
    transcript: StatusTranscript
  ): StepEvidence
  {
    StepEvidence(
      beforeFs,
      afterFs,
      Spec.MoveOutcome(out, err, failed),
      sourceOk,
      sourceIsDir,
      sourceErr,
      targetExistsCalled,
      targetFound,
      targetExistsErr,
      sameFile,
      backup,
      renames,
      backupFs,
      transcript.first,
      transcript.calls
    )
  }

  ghost function MetadataLinkCountValue(
    evidence: MetadataEvidence
  ): int
  {
    match evidence.links
    case LinkCountKnown(count) => count
    case LinkCountUnknown => 0
  }

  ghost predicate MetadataEvidenceFor(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  )
  {
    evidence.times.atimeSec == evidence.rawStatus.times.atimeSec &&
    evidence.times.atimeNsec == evidence.rawStatus.times.atimeNsec &&
    evidence.times.mtimeSec == evidence.rawStatus.times.mtimeSec &&
    evidence.times.mtimeNsec == evidence.rawStatus.times.mtimeNsec &&
    (evidence.ok ==>
      evidence.key == evidence.rawStatus.hostKey &&
      evidence.isDir == (evidence.rawStatus.kind == BenchWorld.DirectoryKind) &&
      evidence.isSymlink == (evidence.rawStatus.kind == BenchWorld.SymlinkKind) &&
      MetadataLinkCountValue(evidence) == evidence.rawStatus.linkCount) &&
    match IOContract.GetFileStatusResultFields(fs, path, followSymlink)
    case Ok(expected) =>
      evidence.ok && evidence.err == 0 &&
      evidence.key == expected.hostKey &&
      evidence.links.LinkCountKnown? &&
      MetadataLinkCountValue(evidence) == expected.linkCount &&
      evidence.isDir == (expected.kind == BenchWorld.DirectoryKind) &&
      evidence.isSymlink == (expected.kind == BenchWorld.SymlinkKind)
    case Err(error) =>
      !evidence.ok && evidence.err == IOContract.IOErrorErrno(error)
  }

  ghost predicate ObservedMetadataEvidenceFor(
    observations: BenchWorld.StatusTimeObservations,
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  )
  {
    MetadataEvidenceFor(fs, path, followSymlink, evidence) &&
    var status := evidence.rawStatus;
    IOContract.ObservedFileStatusContractFields(
      observations, evidence.ordinal, fs, path, followSymlink,
      evidence.ok, status, evidence.err
    ) &&
      (evidence.ok ==>
        evidence.key == status.hostKey &&
        evidence.isDir == (status.kind == BenchWorld.DirectoryKind) &&
        evidence.isSymlink == (status.kind == BenchWorld.SymlinkKind) &&
        MetadataLinkCountValue(evidence) == status.linkCount &&
        evidence.times.atimeSec == status.times.atimeSec &&
        evidence.times.atimeNsec == status.times.atimeNsec &&
        evidence.times.mtimeSec == status.times.mtimeSec &&
        evidence.times.mtimeNsec == status.times.mtimeNsec)
  }

  ghost predicate EntryNameEvidenceFor(
    fs: BenchWorld.FileSystem,
    path: string,
    evidence: EntryNameEvidence
  )
  {
    BasenameCore.BasenameValueSummary(path, evidence.leaf) &&
    DirnameCore.DirnameValueSummary(path, evidence.parent) &&
    MetadataEvidenceFor(
      fs, evidence.parent, false, evidence.parentMetadata
    )
  }

  ghost predicate EvidenceNamesSame(
    left: EntryNameEvidence,
    right: EntryNameEvidence
  )
  {
    left.parentMetadata.ok &&
    right.parentMetadata.ok &&
    left.parentMetadata.key == right.parentMetadata.key &&
    left.leaf == right.leaf
  }

  ghost predicate ReferentEvidenceNamesTarget(
    referent: OptionalEntryNameEvidence,
    target: EntryNameEvidence
  )
  {
    match referent
    case SomeEntryNameEvidence(_, value) =>
      EvidenceNamesSame(value, target)
    case _ => false
  }

  opaque ghost predicate SameFileEvidenceFor(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: string,
    target: string,
    evidence: SameFileEvidence
  )
  {
    match evidence
    case NoSameFileCheck => false
    case CheckedSameFile(
      sourceMetadata,
      targetMetadata,
      sourceFollowed,
      sourceEntry,
      targetEntry,
      sourceReferentEntry,
      _,
      decision
      ) =>
      MetadataEvidenceFor(fs, source, false, sourceMetadata) &&
      MetadataEvidenceFor(fs, target, false, targetMetadata) &&
      sourceMetadata.ok &&
      targetMetadata.ok &&
      EntryNameEvidenceFor(fs, source, sourceEntry) &&
      EntryNameEvidenceFor(fs, target, targetEntry) &&
      (if sourceMetadata.isSymlink then
         (match sourceFollowed
          case SomeMetadataEvidence(value) =>
            MetadataEvidenceFor(fs, source, true, value)
          case NoMetadataEvidence => false) &&
         (match sourceReferentEntry
          case NoEntryNameEvidence => false
          case FailedEntryNameEvidence(resolveErr) =>
            IOContract.ResolvePathIdentityContractFields(
              fs, preCwd, source, false, "", resolveErr
            )
          case SomeEntryNameEvidence(resolvedPath, value) =>
            IOContract.ResolvePathIdentityContractFields(
              fs, preCwd, source, true, resolvedPath, 0
            ) &&
            EntryNameEvidenceFor(fs, resolvedPath, value))
       else
         sourceFollowed == NoMetadataEvidence &&
         sourceReferentEntry == NoEntryNameEvidence) &&
      decision ==
      if EvidenceNamesSame(sourceEntry, targetEntry) ||
         (cmd.backupMode == Schema.BackupOff &&
          ((sourceMetadata.ok &&
            targetMetadata.ok &&
            sourceMetadata.key == targetMetadata.key) ||
           ReferentEvidenceNamesTarget(
             sourceReferentEntry, targetEntry
           )))
      then Spec.RejectSameFile
      else Spec.ContinueMove
  }

  lemma PackageSameFileEvidence(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: string,
    target: string,
    sourceMetadata: MetadataEvidence,
    targetMetadata: MetadataEvidence,
    sourceFollowed: OptionalMetadataEvidence,
    sourceEntry: EntryNameEvidence,
    targetEntry: EntryNameEvidence,
    sourceReferentEntry: OptionalEntryNameEvidence,
    collision: BackupCollisionEvidence,
    decision: Spec.SameFileDecision
  )
    requires MetadataEvidenceFor(
               fs, source, false, sourceMetadata
             )
    requires MetadataEvidenceFor(
               fs, target, false, targetMetadata
             )
    requires sourceMetadata.ok && targetMetadata.ok
    requires EntryNameEvidenceFor(fs, source, sourceEntry)
    requires EntryNameEvidenceFor(fs, target, targetEntry)
    requires if sourceMetadata.isSymlink then
               (match sourceFollowed
                case SomeMetadataEvidence(value) =>
                  MetadataEvidenceFor(fs, source, true, value)
                case NoMetadataEvidence => false) &&
               (match sourceReferentEntry
                case NoEntryNameEvidence => false
                case FailedEntryNameEvidence(resolveErr) =>
                  IOContract.ResolvePathIdentityContractFields(
                    fs, preCwd, source, false, "", resolveErr
                  )
                case SomeEntryNameEvidence(resolvedPath, value) =>
                  IOContract.ResolvePathIdentityContractFields(
                    fs, preCwd, source, true, resolvedPath, 0
                  ) &&
                  EntryNameEvidenceFor(fs, resolvedPath, value))
             else
               sourceFollowed == NoMetadataEvidence &&
               sourceReferentEntry == NoEntryNameEvidence
    requires decision ==
             if EvidenceNamesSame(sourceEntry, targetEntry) ||
                (cmd.backupMode == Schema.BackupOff &&
                 ((sourceMetadata.ok &&
                   targetMetadata.ok &&
                   sourceMetadata.key == targetMetadata.key) ||
                  ReferentEvidenceNamesTarget(
                    sourceReferentEntry, targetEntry
                  )))
             then Spec.RejectSameFile
             else Spec.ContinueMove
    ensures SameFileEvidenceFor(
              cmd,
              fs,
              preCwd,
              source,
              target,
              CheckedSameFile(
                sourceMetadata,
                targetMetadata,
                sourceFollowed,
                sourceEntry,
                targetEntry,
                sourceReferentEntry,
                collision,
                decision
              )
            )
  {
    reveal SameFileEvidenceFor();
  }

  ghost predicate BackupCollisionEvidenceFor(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string,
    sourceMetadata: MetadataEvidence,
    sourceEntry: EntryNameEvidence,
    targetEntry: EntryNameEvidence,
    evidence: BackupCollisionEvidence
  )
  {
    var needsCheck :=
      (cmd.backupMode == Schema.BackupSimple ||
       cmd.backupMode == Schema.BackupExisting) &&
      sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
    if !needsCheck then
      evidence == NoBackupCollisionCheck
    else
      match evidence
      case NoBackupCollisionCheck => false
      case CheckedBackupCollision(sourceNoFollow, candidateFollowed) =>
        sourceNoFollow == sourceMetadata &&
        MetadataEvidenceFor(
          fs,
          SimpleBackupPath(target, cmd.backupSuffix),
          true,
          candidateFollowed
        )
  }

  ghost predicate BackupCollisionDetected(
    evidence: BackupCollisionEvidence
  )
  {
    match evidence
    case NoBackupCollisionCheck => false
    case CheckedBackupCollision(source, candidate) =>
      source.ok && candidate.ok && source.key == candidate.key
  }

  ghost predicate BackupChecksFor(
    target: string,
    start: nat,
    fs: BenchWorld.FileSystem,
    checks: seq<BackupCheckEvidence>
  )
  {
    start >= 1 &&
    |checks| > 0 &&
    (forall i: nat | i < |checks| ::
       checks[i].candidate == NumberedBackupPath(target, start + i) &&
       IOContract.PathExistsContractFields(
         fs,
         checks[i].candidate,
         false,
         checks[i].found,
         checks[i].err
       )) &&
    (forall i: nat | i + 1 < |checks| :: checks[i].found) &&
    !checks[|checks| - 1].found
  }

  ghost predicate BackupStatusSuffixFor(
    backupMode: Schema.BackupMode,
    fs: BenchWorld.FileSystem,
    target: string,
    calls: seq<Spec.StatusCallEvidence>
  )
  {
    if backupMode == Schema.BackupOff || backupMode == Schema.BackupSimple then
      |calls| == 0
    else if backupMode == Schema.BackupExisting then
      |calls| >= 1 &&
      Spec.StatusRequest(calls[0], fs, NumberedBackupPath(target, 1), false) &&
      (if !calls[0].ok then
         |calls| == 1
       else
         |calls| >= 2 &&
         (forall i: nat | 1 <= i < |calls| ::
            Spec.StatusRequest(calls[i], fs, NumberedBackupPath(target, i), false)) &&
         (forall i: nat | 1 <= i + 1 < |calls| :: calls[i].ok) &&
         !calls[|calls| - 1].ok)
    else
      |calls| >= 1 &&
      (forall i: nat | i < |calls| ::
        Spec.StatusRequest(calls[i], fs, NumberedBackupPath(target, i + 1), false)) &&
      (forall i: nat | i + 1 < |calls| :: calls[i].ok) &&
      !calls[|calls| - 1].ok
  }

  ghost predicate BackupSelectionEvidenceFor(
    target: string,
    backupMode: Schema.BackupMode,
    suffix: string,
    fs: BenchWorld.FileSystem,
    evidence: BackupSelectionEvidence
  )
  {
    match evidence
    case NoBackupSelection =>
      backupMode == Schema.BackupOff
    case SelectedBackup(
      backupPath,
      checks,
      existingFirstCheckCalled,
      existingFirstFound,
      existingFirstErr
      ) =>
      if backupMode == Schema.BackupSimple then
        backupPath == SimpleBackupPath(target, suffix) &&
        |checks| == 0 &&
        !existingFirstCheckCalled
      else if backupMode == Schema.BackupExisting then
        existingFirstCheckCalled &&
        IOContract.PathExistsContractFields(
          fs,
          NumberedBackupPath(target, 1),
          false,
          existingFirstFound,
          existingFirstErr
        ) &&
        if existingFirstFound then
          BackupChecksFor(target, 1, fs, checks) &&
          backupPath == checks[|checks| - 1].candidate
        else
          |checks| == 0 &&
          backupPath == SimpleBackupPath(target, suffix)
      else
        backupMode == Schema.BackupNumbered &&
        !existingFirstCheckCalled &&
        BackupChecksFor(target, 1, fs, checks) &&
        backupPath == checks[|checks| - 1].candidate
  }

  ghost predicate RenameEvidenceFor(
    source: string,
    target: string,
    sourceIsDir: bool,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    calls: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem
  )
  {
    (exists sourceStatErr: int ::
       IOContract.IsDirectoryStrictContractFields(
         beforeFs,
         source,
         false,
         true,
         sourceIsDir,
         sourceStatErr
       )) &&
    |calls| <= 2 &&
    if backupPath == "" then
      |calls| == 1 &&
      IOContract.RenamePathContractFields(
        beforeFs,
        source,
        target,
        calls[0].ok,
        calls[0].err,
        calls[0].afterFs
      ) &&
      afterFs == calls[0].afterFs &&
      if calls[0].ok then
        outcome == Spec.MoveOutcome(
          StepSuccessStdout(source, target, "", verbose, debug), [], false
        )
      else
        outcome == Spec.MoveOutcome(
          [],
          Spec.SourceRenameFailureMessageSpec(
            source,
            target,
            SourceRenameDiagnosticErr(
              target, sourceIsDir, calls[0].err
            ),
            sourceIsDir && IOContract.PathExistsContractFields(
              beforeFs, target, false, true, 0)
          ),
          true
        )
    else
      |calls| >= 1 &&
      IOContract.RenamePathContractFields(
        beforeFs,
        target,
        backupPath,
        calls[0].ok,
        calls[0].err,
        calls[0].afterFs
      ) &&
      if !calls[0].ok then
        |calls| == 1 &&
        afterFs == calls[0].afterFs &&
        outcome == Spec.MoveOutcome(
          [],
          Spec.RenameFailureMessageSpec(source, target, calls[0].err),
          true
        )
      else
        |calls| == 2 &&
        backupFs == calls[0].afterFs &&
        IOContract.RenamePathContractFields(
          backupFs,
          source,
          target,
          calls[1].ok,
          calls[1].err,
          calls[1].afterFs
        ) &&
        afterFs == calls[1].afterFs &&
        if calls[1].ok then
          outcome == Spec.MoveOutcome(
            StepSuccessStdout(
              source, target, backupPath, verbose, debug
            ),
            [],
            false
          )
        else
          outcome == Spec.MoveOutcome(
            [],
            Spec.SourceRenameFailureMessageSpec(
              source,
              target,
              SourceRenameDiagnosticErr(
                target, sourceIsDir, calls[1].err
              ),
              false
            ),
            true
          )
  }

  ghost predicate ExistingTargetRenameEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
  {
    SameFileEvidenceFor(
      cmd,
      evidence.beforeFs,
      preCwd,
      source,
      target,
      evidence.sameFile
    ) &&
    match evidence.sameFile
    case NoSameFileCheck => false
    case CheckedSameFile(
      sourceMetadata,
      _,
      _,
      sourceEntry,
      targetEntry,
      _,
      collision,
      _
      ) =>
      BackupCollisionEvidenceFor(
        cmd,
        evidence.beforeFs,
        source,
        target,
        sourceMetadata,
        sourceEntry,
        targetEntry,
        collision
      ) &&
      if BackupCollisionDetected(collision) then
        evidence.backup == NoBackupSelection &&
        |evidence.renames| == 0 &&
        evidence.afterFs == evidence.beforeFs &&
        evidence.outcome == Spec.MoveOutcome(
          [],
          Spec.BackupWouldDestroySourceMessageSpec(source, target),
          true
        )
      else if cmd.backupMode == Schema.BackupOff then
        evidence.backup == NoBackupSelection &&
        RenameEvidenceFor(
          source,
          target,
          evidence.sourceIsDir,
          "",
          cmd.verbose,
          cmd.debug,
          evidence.beforeFs,
          preCwd,
          evidence.afterFs,
          evidence.outcome,
          evidence.renames,
          evidence.backupFs
        )
      else
        BackupSelectionEvidenceFor(
          target,
          cmd.backupMode,
          cmd.backupSuffix,
          evidence.beforeFs,
          evidence.backup
        ) &&
        RenameEvidenceFor(
          source,
          target,
          evidence.sourceIsDir,
          evidence.backup.backupPath,
          cmd.verbose,
          cmd.debug,
          evidence.beforeFs,
          preCwd,
          evidence.afterFs,
          evidence.outcome,
          evidence.renames,
          evidence.backupFs
        )
  }

  opaque ghost predicate StepEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
  {
    IOContract.IsDirectoryStrictContractFields(
      evidence.beforeFs,
      source,
      false,
      evidence.sourceOk,
      evidence.sourceIsDir,
      evidence.sourceErr
    ) &&
    |evidence.renames| <= 2 &&
    if !evidence.sourceOk then
      !evidence.targetExistsCalled &&
      evidence.sameFile == NoSameFileCheck &&
      evidence.backup == NoBackupSelection &&
      |evidence.renames| == 0 &&
      evidence.afterFs == evidence.beforeFs &&
      evidence.outcome == Spec.MoveOutcome(
        [],
        Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr),
        true
      )
    else
      evidence.targetExistsCalled &&
      IOContract.PathExistsContractFields(
        evidence.beforeFs,
        target,
        false,
        evidence.targetFound,
        evidence.targetExistsErr
      ) &&
      (if !evidence.targetFound then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         RenameEvidenceFor(
           source,
           target,
           evidence.sourceIsDir,
           "",
           cmd.verbose,
           cmd.debug,
           evidence.beforeFs,
           preCwd,
           evidence.afterFs,
           evidence.outcome,
           evidence.renames,
           evidence.backupFs
         )
       else if cmd.overwriteMode == Schema.OverwriteSkip then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
       else if cmd.updateMode == Schema.UpdateNone then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
       else if cmd.updateMode == Schema.UpdateNoneFail then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true)
       else
         SameFileEvidenceFor(
           cmd,
           evidence.beforeFs,
           preCwd,
           source,
           target,
           evidence.sameFile
         ) &&
         match evidence.sameFile
         case NoSameFileCheck => false
         case CheckedSameFile(
           sourceMetadata,
           targetMetadata,
           _,
           _,
           _,
           _,
           _,
           decision
           ) =>
           if decision == Spec.RejectSameFile then
             evidence.backup == NoBackupSelection &&
             |evidence.renames| == 0 &&
             evidence.afterFs == evidence.beforeFs &&
             evidence.outcome == Spec.MoveOutcome(
               [], Spec.SameFileMessageSpec(source, target), true
             )
           else if cmd.updateMode == Schema.UpdateOlder then
             if !SourceNewer(
                  sourceMetadata.times.mtimeSec,
                  sourceMetadata.times.mtimeNsec,
                  targetMetadata.times.mtimeSec,
                  targetMetadata.times.mtimeNsec
                ) then
               evidence.backup == NoBackupSelection &&
               |evidence.renames| == 0 &&
               evidence.afterFs == evidence.beforeFs &&
               evidence.outcome ==
               Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
             else
               ExistingTargetRenameEvidenceFor(
                 source, target, cmd, preCwd, evidence
               )
           else
             ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             ))
  }

  ghost predicate StepStatusEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    evidence: StepEvidence
  )
  {
    var fs := evidence.beforeFs;
    var calls := evidence.statusCalls;
    |calls| >= 1 &&
    Spec.StatusRequest(calls[0], fs, source, false) &&
    calls[0].ok == evidence.sourceOk &&
    calls[0].err == evidence.sourceErr &&
    (if !evidence.sourceOk then
       |calls| == 1
     else
       |calls| >= 2 &&
       Spec.StatusRequest(calls[1], fs, target, false) &&
       calls[1].ok == evidence.targetFound &&
       calls[1].err == evidence.targetExistsErr &&
       (if !evidence.targetFound ||
           cmd.overwriteMode == Schema.OverwriteSkip ||
           cmd.updateMode == Schema.UpdateNone ||
           cmd.updateMode == Schema.UpdateNoneFail then
          |calls| == 2
        else
          match evidence.sameFile
          case NoSameFileCheck => false
          case CheckedSameFile(
            sourceMetadata, targetMetadata, sourceFollowed,
            sourceEntry, targetEntry, sourceReferentEntry,
            collision, decision
          ) =>
            |calls| >= 6 &&
            calls[2] == MetadataStatusCall(fs, source, false, sourceMetadata) &&
            calls[3] == MetadataStatusCall(fs, target, false, targetMetadata) &&
            calls[4] == MetadataStatusCall(
              fs, sourceEntry.parent, false, sourceEntry.parentMetadata
            ) &&
            calls[5] == MetadataStatusCall(
              fs, targetEntry.parent, false, targetEntry.parentMetadata
            ) &&
            var afterEntries :=
              if sourceMetadata.isSymlink then
                (if sourceReferentEntry.SomeEntryNameEvidence? then 8 else 7)
              else 6;
              (if sourceMetadata.isSymlink then
                 |calls| >= 7 &&
                 (match sourceFollowed
                  case SomeMetadataEvidence(followed) =>
                    calls[6] == MetadataStatusCall(fs, source, true, followed)
                  case _ => false) &&
                 (match sourceReferentEntry
                  case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
                    |calls| >= 8 &&
                    calls[7] == MetadataStatusCall(
                      fs, referentEntry.parent, false,
                      referentEntry.parentMetadata
                    )
                  case FailedEntryNameEvidence(_) => true
                  case NoEntryNameEvidence => false)
               else
                 true) &&
              (if decision == Spec.RejectSameFile ||
                  (cmd.updateMode == Schema.UpdateOlder &&
                   !SourceNewer(
                     sourceMetadata.times.mtimeSec,
                     sourceMetadata.times.mtimeNsec,
                     targetMetadata.times.mtimeSec,
                     targetMetadata.times.mtimeNsec
                   )) then
                 |calls| == afterEntries
               else
                 var collisionNeeded :=
                   (cmd.backupMode == Schema.BackupSimple ||
                    cmd.backupMode == Schema.BackupExisting) &&
                   sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
                 var afterCollision := afterEntries +
                   (if collisionNeeded then 1 else 0);
                 afterCollision <= |calls| &&
                 (collisionNeeded ==>
                   (match collision
                    case CheckedBackupCollision(_, candidate) =>
                      calls[afterEntries] == MetadataStatusCall(
                        fs, SimpleBackupPath(target, cmd.backupSuffix),
                        true, candidate
                      )
                    case _ => false)) &&
                 (if BackupCollisionDetected(collision) then
                    |calls| == afterCollision
                  else
                    BackupStatusSuffixFor(
                      cmd.backupMode, fs, target, calls[afterCollision..]
                    )))))
  }

  lemma StepStatusEvidenceTransfer(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    from: StepEvidence,
    to: StepEvidence
  )
    requires StepStatusEvidenceFor(source, target, cmd, from)
    requires to.beforeFs == from.beforeFs
    requires to.sourceOk == from.sourceOk
    requires to.sourceErr == from.sourceErr
    requires to.targetFound == from.targetFound
    requires to.targetExistsErr == from.targetExistsErr
    requires to.sameFile == from.sameFile
    requires to.statusCalls == from.statusCalls
    ensures StepStatusEvidenceFor(source, target, cmd, to)
  {
  }

  lemma PackageSourceFailureStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires !evidence.sourceOk
    requires !evidence.targetExistsCalled
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome == Spec.MoveOutcome(
                                   [],
                                   Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr),
                                   true
                                 )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageMissingTargetStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               evidence.targetFound,
               evidence.targetExistsErr
             )
    requires !evidence.targetFound
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires RenameEvidenceFor(
               source,
               target,
               evidence.sourceIsDir,
               "",
               cmd.verbose,
               cmd.debug,
               evidence.beforeFs,
               preCwd,
               evidence.afterFs,
               evidence.outcome,
               evidence.renames,
               evidence.backupFs
             )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageOverwriteSkipStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode == Schema.OverwriteSkip
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateNoneStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateNone
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateNoneFailStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateNoneFail
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageSameFileRejectStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode != Schema.UpdateNone
    requires cmd.updateMode != Schema.UpdateNoneFail
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.RejectSameFile
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateOlderSkipStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateOlder
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.ContinueMove
    requires !SourceNewer(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageExistingTargetRenameStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode != Schema.UpdateNone
    requires cmd.updateMode != Schema.UpdateNoneFail
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.ContinueMove
    requires cmd.updateMode != Schema.UpdateOlder ||
             SourceNewer(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  opaque ghost predicate BatchStepEvidenceFor(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    step: StepEvidence
  )
  {
    var normalizedSource :=
      NormalizeSource(source, cmd.stripTrailingSlashes);
    StepEvidenceFor(
      normalizedSource,
      TargetInDirectory(directory, normalizedSource),
      cmd,
      preCwd,
      step
    ) &&
    beforeFs == step.beforeFs &&
    afterFs == step.afterFs &&
    outcome == step.outcome &&
    stdoutFragment == outcome.stdoutFragment &&
    stderrFragment == outcome.stderrFragment
  }

  ghost predicate BatchEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    evidence: BatchEvidence
  )
  {
    |evidence.steps| == |sources| &&
    |evidence.fsBounds| == |sources| + 1 &&
    |evidence.outcomes| == |sources| &&
    |evidence.stdoutFragments| == |sources| &&
    |evidence.stderrFragments| == |sources| &&
    evidence.fsBounds[0] == beforeFs &&
    evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs &&
    (forall i: nat | i < |sources| ::
       BatchStepEvidenceFor(
         sources[i],
         directory,
         cmd,
         evidence.fsBounds[i],
         preCwd,
         evidence.fsBounds[i + 1],
         evidence.outcomes[i],
         evidence.stdoutFragments[i],
         evidence.stderrFragments[i],
         evidence.steps[i]
       )) &&
    Spec.ConcatenateFragments(evidence.stdoutFragments) == out &&
    Spec.ConcatenateFragments(evidence.stderrFragments) == err &&
    (hadError <==>
     exists i: nat ::
       i < |evidence.outcomes| && evidence.outcomes[i].failed)
  }

  lemma {:isolate_assertions} PackageBatchEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    evidence: BatchEvidence
  )
    requires |evidence.steps| == |sources|
    requires |evidence.fsBounds| == |sources| + 1
    requires |evidence.outcomes| == |sources|
    requires |evidence.stdoutFragments| == |sources|
    requires |evidence.stderrFragments| == |sources|
    requires evidence.fsBounds[0] == beforeFs
    requires evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs
    requires forall i: nat | i < |sources| ::
      BatchStepEvidenceFor(
        sources[i], directory, cmd,
        evidence.fsBounds[i], preCwd, evidence.fsBounds[i + 1],
        evidence.outcomes[i], evidence.stdoutFragments[i],
        evidence.stderrFragments[i], evidence.steps[i])
    requires Spec.ConcatenateFragments(evidence.stdoutFragments) == out
    requires Spec.ConcatenateFragments(evidence.stderrFragments) == err
    requires hadError <==>
      exists i: nat ::
        i < |evidence.outcomes| && evidence.outcomes[i].failed
    ensures BatchEvidenceFor(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, evidence)
  {
  }

  lemma ConcatenateFragmentsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    fragment: BenchWorld.Bytes
  )
    ensures Spec.ConcatenateFragments(fragments + [fragment]) ==
            Spec.ConcatenateFragments(fragments) + fragment
    decreases |fragments|
  {
    if |fragments| > 0 {
      ConcatenateFragmentsSnoc(fragments[1..], fragment);
      assert (fragments + [fragment])[0] == fragments[0];
      assert (fragments + [fragment])[1..] ==
             fragments[1..] + [fragment];
    }
  }

  lemma FailureExistsSnoc(
    outcomes: seq<Spec.MoveOutcome>,
    outcome: Spec.MoveOutcome,
    prefixFailed: bool
  )
    requires prefixFailed <==>
             exists i: nat :: i < |outcomes| && outcomes[i].failed
    ensures prefixFailed || outcome.failed <==>
            exists i: nat ::
              i < |outcomes + [outcome]| &&
              (outcomes + [outcome])[i].failed
  {
    if prefixFailed {
      var i: nat :| i < |outcomes| && outcomes[i].failed;
      assert (outcomes + [outcome])[i] == outcomes[i];
    }
    if outcome.failed {
      assert (outcomes + [outcome])[|outcomes|] == outcome;
    }
    if exists i: nat ::
        i < |outcomes + [outcome]| &&
        (outcomes + [outcome])[i].failed {
      var i: nat :|
        i < |outcomes + [outcome]| &&
        (outcomes + [outcome])[i].failed;
      if i < |outcomes| {
        assert (outcomes + [outcome])[i] == outcomes[i];
        assert exists j: nat ::
            j < |outcomes| && outcomes[j].failed;
      } else {
        assert i == |outcomes|;
        assert (outcomes + [outcome])[i] == outcome;
      }
    }
  }

  method GetErrnoText(err: int) returns (out: string)
    ensures out == Spec.ErrnoTextSpec(err)
  {
    out := Spec.ErrnoTextSpec(err);
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetMissingFileOperandMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.MissingFileOperandMessageSpec()
  {
    out := Spec.MissingFileOperandMessageSpec();
  }

  method GetMissingDestinationMessage(source: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.MissingDestinationMessageSpec(source)
  {
    out := Spec.MissingDestinationMessageSpec(source);
  }

  method GetExtraOperandMessage(operand: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.ExtraOperandMessageSpec(operand)
  {
    out := Spec.ExtraOperandMessageSpec(operand);
  }

  method GetTargetDirectoryConflictMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.TargetDirectoryConflictMessageSpec()
  {
    out := Spec.TargetDirectoryConflictMessageSpec();
  }

  method GetInvalidBackupArgumentMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidBackupArgumentMessageSpec(value)
  {
    out := Spec.InvalidBackupArgumentMessageSpec(value);
  }

  method GetInvalidUpdateArgumentMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidUpdateArgumentMessageSpec(value)
  {
    out := Spec.InvalidUpdateArgumentMessageSpec(value);
  }

  method GetTargetFailureMessage(path: string, explicitTargetDirectory: bool, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.TargetFailureMessageSpec(path, explicitTargetDirectory, err)
  {
    out := Spec.TargetFailureMessageSpec(path, explicitTargetDirectory, err);
  }

  method GetSourceStatFailureMessage(source: string, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.SourceStatFailureMessageSpec(source, err)
  {
    out := Spec.SourceStatFailureMessageSpec(source, err);
  }

  method GetRenameFailureMessage(source: string, target: string, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.RenameFailureMessageSpec(source, target, err)
  {
    out := Spec.RenameFailureMessageSpec(source, target, err);
  }

  method GetSourceRenameFailureMessage(
    source: string,
    target: string,
    sourceIsDir: bool,
    targetFound: bool,
    err: int
  ) returns (out: BenchWorld.Bytes)
    ensures out ==
            Spec.SourceRenameFailureMessageSpec(
              source,
              target,
              SourceRenameDiagnosticErr(target, sourceIsDir, err),
              sourceIsDir && targetFound
            )
  {
    out := Spec.SourceRenameFailureMessageSpec(
      source,
      target,
      SourceRenameDiagnosticErr(target, sourceIsDir, err),
      sourceIsDir && targetFound
    );
  }

  method GetSameFileMessage(
    source: string,
    target: string
  ) returns (out: BenchWorld.Bytes)
    ensures out == Spec.SameFileMessageSpec(source, target)
  {
    out := Spec.SameFileMessageSpec(source, target);
  }

  method GetBackupWouldDestroySourceMessage(
    source: string,
    target: string
  ) returns (out: BenchWorld.Bytes)
    ensures out == Spec.BackupWouldDestroySourceMessageSpec(source, target)
  {
    out := Spec.BackupWouldDestroySourceMessageSpec(source, target);
  }

  method GetVerboseRenameMessage(source: string, target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.VerboseRenameMessageSpec(source, target)
  {
    out := Spec.VerboseRenameMessageSpec(source, target);
  }

  method GetVerboseRenameWithBackupMessage(source: string, target: string, backup: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.VerboseRenameWithBackupMessageSpec(source, target, backup)
  {
    out := Spec.VerboseRenameWithBackupMessageSpec(source, target, backup);
  }

  method GetDebugSkipMessage(target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.DebugSkipMessageSpec(target)
  {
    out := Spec.DebugSkipMessageSpec(target);
  }

  method GetNotReplacingMessage(target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.NotReplacingMessageSpec(target)
  {
    out := Spec.NotReplacingMessageSpec(target);
  }

  method FindUnusedNumberedBackupPath(
    target: string,
    index: nat,
    io: BenchIO.IO
  ) returns (path: string, ghost checks: seq<BackupCheckEvidence>, ghost calls: seq<Spec.StatusCallEvidence>)
    requires index >= 1
    modifies io.statusObservationsRegion
    ensures BackupChecksFor(target, index, old(io.fs()), checks)
    ensures path == checks[|checks| - 1].candidate
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(io.statusObservations(), old(io.statusCursor()), calls)
    ensures |calls| == |checks|
    ensures forall i: nat | i < |calls| ::
              Spec.StatusRequest(
                calls[i], old(io.fs()), NumberedBackupPath(target, index + i), false
              ) &&
              calls[i].ok == checks[i].found &&
              calls[i].err == checks[i].err
    decreases *
  {
    ghost var firstStatus := io.statusCursor();
    var candidate := NumberedBackupPath(target, index);
    var getFileStatusResult := io.GetFileStatus(candidate, false);
    var rawMetadataOk6 := getFileStatusResult.Ok?;
    var rawMetadataStatus6 := IOContract.ResultValue(getFileStatusResult, BenchWorld.DEFAULT_FILE_STATUS);
    var rawMetadataErr6 := IOContract.ResultErrno(getFileStatusResult);
    IOContract.FileStatusStructureImpliesMetadata(io.fs(), candidate, false, rawMetadataOk6, rawMetadataStatus6, rawMetadataErr6);
    var found := rawMetadataOk6;
    var err := rawMetadataErr6;
    ghost var check := BackupCheckEvidence(candidate, found, err);
    ghost var call := Spec.StatusCallEvidence(old(io.fs()), candidate, false,
                                         rawMetadataOk6, rawMetadataStatus6, rawMetadataErr6);
    if found {
      ghost var tail: seq<BackupCheckEvidence>;
      ghost var tailCalls: seq<Spec.StatusCallEvidence>;
      path, tail, tailCalls := FindUnusedNumberedBackupPath(
        target, index + 1, io
      );
      checks := [check] + tail;
      calls := [call] + tailCalls;
      StatusCallsConcat(io.statusObservations(), firstStatus, [call], tailCalls);
      assert IOContract.PathExistsContractFields(
          old(io.fs()), candidate, false, true, err
        );
      assert forall i: nat | i < |checks| ::
          checks[i].candidate == NumberedBackupPath(target, index + i) &&
          IOContract.PathExistsContractFields(
            old(io.fs()),
            checks[i].candidate,
            false,
            checks[i].found,
            checks[i].err
          ) by {
        forall i: nat | i < |checks|
          ensures
            checks[i].candidate ==
            NumberedBackupPath(target, index + i) &&
            IOContract.PathExistsContractFields(
              old(io.fs()),
              checks[i].candidate,
              false,
              checks[i].found,
              checks[i].err
            )
        {
          if i > 0 {
            assert index + i == index + 1 + (i - 1);
          }
        }
      }
      assert forall i: nat | i + 1 < |checks| :: checks[i].found by {
        forall i: nat | i + 1 < |checks|
          ensures checks[i].found
        {
          if i > 0 {
            assert i - 1 + 1 < |tail|;
          }
        }
      }
    } else {
      path := candidate;
      checks := [check];
      calls := [call];
      assert IOContract.PathExistsContractFields(old(io.fs()), candidate, false, false, err);
    }
    assert BackupChecksFor(target, index, old(io.fs()), checks);
  }

  method {:isolate_assertions} PickBackupPath(
    target: string,
    backupMode: Schema.BackupMode,
    suffix: string,
    io: BenchIO.IO
  ) returns (path: string, ghost evidence: BackupSelectionEvidence,
             ghost calls: seq<Spec.StatusCallEvidence>)
    modifies io.statusObservationsRegion
    ensures BackupSelectionEvidenceFor(
              target, backupMode, suffix, old(io.fs()), evidence
            )
    ensures backupMode != Schema.BackupOff ==>
              evidence.SelectedBackup? &&
              evidence.backupPath == path
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(io.statusObservations(), old(io.statusCursor()), calls)
    ensures BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls)
    decreases *
  {
    ghost var firstStatus := io.statusCursor();
    if backupMode == Schema.BackupOff {
      path := "";
      evidence := NoBackupSelection;
      calls := [];
      return;
    }
    if backupMode == Schema.BackupSimple {
      path := SimpleBackupPath(target, suffix);
      evidence := SelectedBackup(path, [], false, false, 0);
      calls := [];
      return;
    }
    if backupMode == Schema.BackupExisting {
      var numberedSeed := NumberedBackupPath(target, 1);
      var getFileStatusResult2 := io.GetFileStatus(numberedSeed, false);
      var rawMetadataOk5 := getFileStatusResult2.Ok?;
      var rawMetadataStatus5 := IOContract.ResultValue(getFileStatusResult2, BenchWorld.DEFAULT_FILE_STATUS);
      var rawMetadataErr5 := IOContract.ResultErrno(getFileStatusResult2);
      IOContract.FileStatusStructureImpliesMetadata(io.fs(), numberedSeed, false, rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5);
      var found := rawMetadataOk5;
      var err := rawMetadataErr5;
      ghost var seedCall := Spec.StatusCallEvidence(old(io.fs()), numberedSeed, false,
                                               rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5);
      assert Spec.StatusRequest(seedCall, old(io.fs()), numberedSeed, false);
      if !found {
        path := SimpleBackupPath(target, suffix);
        evidence := SelectedBackup(path, [], true, found, err);
        calls := [seedCall];
        assert IOContract.PathExistsContractFields(old(io.fs()), numberedSeed, false, false, err);
        return;
      }
      ghost var checks: seq<BackupCheckEvidence>;
      ghost var numberedCalls: seq<Spec.StatusCallEvidence>;
      path, checks, numberedCalls := FindUnusedNumberedBackupPath(target, 1, io);
      evidence := SelectedBackup(path, checks, true, found, err);
      calls := [seedCall] + numberedCalls;
      StatusCallsConcat(io.statusObservations(), firstStatus, [seedCall], numberedCalls);
      assert IOContract.PathExistsContractFields(
          old(io.fs()), numberedSeed, false, true, err
        );
      assert BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls) by {
        forall i: nat | 1 <= i < |calls|
          ensures Spec.StatusRequest(calls[i], old(io.fs()), NumberedBackupPath(target, i), false)
        {
          StatusCallConsIndex(seedCall, numberedCalls, i);
          assert calls[i] == numberedCalls[i - 1];
        }
        forall i: nat | 1 <= i + 1 < |calls|
          ensures calls[i].ok
        {
          if i == 0 {
            assert calls[i] == seedCall;
          } else {
            StatusCallConsIndex(seedCall, numberedCalls, i);
            assert calls[i] == numberedCalls[i - 1];
            assert checks[i - 1].found;
          }
        }
        assert calls[|calls| - 1] == numberedCalls[|numberedCalls| - 1];
      }
      return;
    }
    ghost var checks: seq<BackupCheckEvidence>;
    path, checks, calls := FindUnusedNumberedBackupPath(target, 1, io);
    evidence := SelectedBackup(path, checks, false, false, 0);
    assert BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls) by {
      forall i: nat | i + 1 < |calls|
        ensures calls[i].ok
      {
        assert checks[i].found;
      }
    }
  }

  method CaptureMetadata(
    path: string,
    followSymlink: bool,
    io: BenchIO.IO
  ) returns (evidence: MetadataEvidence)
    modifies io.statusObservationsRegion
    ensures MetadataEvidenceFor(
              old(io.fs()), path, followSymlink, evidence
            )
    ensures ObservedMetadataEvidenceFor(
              io.statusObservations(), old(io.fs()), path, followSymlink, evidence
            )
    ensures evidence.ordinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + 1
  {
    ghost var ordinal := io.statusCursor();
    var getFileStatusResult3 := io.GetFileStatus(path, followSymlink);
    var ok := getFileStatusResult3.Ok?;
    var status := IOContract.ResultValue(getFileStatusResult3, BenchWorld.DEFAULT_FILE_STATUS);
    var err := IOContract.ResultErrno(getFileStatusResult3);
    IOContract.FileStatusStructureImpliesMetadata(io.fs(), path, followSymlink, ok, status, err);
    var atimeSec := status.times.atimeSec;
    var atimeNsec := status.times.atimeNsec;
    var mtimeSec := status.times.mtimeSec;
    var mtimeNsec := status.times.mtimeNsec;
    var isDir := status.kind == BenchWorld.DirectoryKind;
    var isSymlink := status.kind == BenchWorld.SymlinkKind;
    var device := status.hostKey.device;
    var inode := status.hostKey.inode;
    var linkCount := status.linkCount;
    var links := BenchWorld.LinkCountUnknown;
    if ok && 0 <= linkCount {
      links := BenchWorld.LinkCountKnown(linkCount as nat);
    }
    evidence := MetadataEvidence(
      ordinal,
      status,
      ok,
      BenchWorld.HostInodeKey(device, inode),
      links,
      isDir,
      isSymlink,
      BenchWorld.FileTimes(
        atimeSec, atimeNsec, mtimeSec, mtimeNsec, 0, 0
      ),
      err
    );
  }

  method CaptureEntryName(
    path: string,
    io: BenchIO.IO
  ) returns (evidence: EntryNameEvidence)
    modifies io.statusObservationsRegion
    ensures EntryNameEvidenceFor(old(io.fs()), path, evidence)
    ensures io.statusCursor() == old(io.statusCursor()) + 1
    ensures evidence.parentMetadata.ordinal == old(io.statusCursor())
    ensures ObservedMetadataEvidenceFor(
              io.statusObservations(), old(io.fs()), evidence.parent,
              false, evidence.parentMetadata)
    decreases *
  {
    var leaf := BasenameCore.ComputeBasenameValue(path);
    var parent := DirnameCore.ComputeDirnameValue(path);
    var parentMetadata := CaptureMetadata(parent, false, io);
    evidence := EntryNameEvidence(parent, leaf, parentMetadata);
  }

  lemma StrictMetadataSuccess(
    fs: BenchWorld.FileSystem,
    path: string,
    isDir: bool,
    statErr: int,
    evidence: MetadataEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               fs, path, false, true, isDir, statErr
             )
    requires MetadataEvidenceFor(fs, path, false, evidence)
    ensures evidence.ok
  {
  }

  lemma ExistingMetadataSuccess(
    fs: BenchWorld.FileSystem,
    path: string,
    existsErr: int,
    evidence: MetadataEvidence
  )
    requires IOContract.PathExistsContractFields(
               fs, path, false, true, existsErr
             )
    requires MetadataEvidenceFor(fs, path, false, evidence)
    ensures evidence.ok
  {
  }

  ghost predicate TargetDirectoryCheckSummaryFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, true, statErr) &&
       ok == true &&
       err == TargetDirectoryErr(true, true, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, false, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(true, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, false, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(false, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, true, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(false, true, statErr))
  }

  ghost predicate RunIntoDirectoryEvidenceFields(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    (exists
       hadError: bool,
       out: BenchWorld.Bytes,
       err: BenchWorld.Bytes,
       batch: BatchEvidence
       ::
         TargetDirectoryCheckSummaryFields(
           directory, beforeFs, true, 0
         ) &&
         BatchEvidenceFor(
           sources,
           directory,
           cmd,
           beforeFs,
           preCwd,
           afterFs,
           hadError,
           out,
           err,
           batch
         ) &&
         exit == (if hadError then 1 else 0) &&
         stdout2 == preStdout + out &&
         stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSummaryFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       Spec.TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate RunTwoOperandEvidenceFields(
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
  {
    var source :=
      NormalizeSource(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists step: StepEvidence ::
        StepEvidenceFor(source, destination, cmd, preCwd, step) &&
        step.beforeFs == beforeFs &&
        step.afterFs == afterFs &&
        exit == (if step.outcome.failed then 1 else 0) &&
        stdout2 == preStdout + step.outcome.stdoutFragment &&
        stderr2 == preStderr + step.outcome.stderrFragment
    else
      (exists
         directoryErr: int,
         batch: BatchEvidence,
         outcome: Spec.MoveOutcome
         ::
           IOContract.IsDirectoryContractFields(
             beforeFs, destination, true, true, true, directoryErr
           ) &&
           BatchEvidenceFor(
             [cmd.operands[0]],
             destination,
             cmd,
             beforeFs,
             preCwd,
             afterFs,
             outcome.failed,
             outcome.stdoutFragment,
             outcome.stderrFragment,
             batch
           ) &&
           exit == (if outcome.failed then 1 else 0) &&
           stdout2 == preStdout + outcome.stdoutFragment &&
           stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment)
  }

  ghost predicate DirectoryStatusEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: BenchWorld.StatusTimeObservations,
    firstStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: DirectoryStatusEvidence
  )
  {
    match evidence
    case FailedDirectoryStatus(call) =>
      calls == [call] &&
      Spec.StatusRequest(call, beforeFs, directory, true) &&
      (!call.ok || call.status.kind != BenchWorld.DirectoryKind) &&
      afterFs == beforeFs &&
      afterStdout == beforeStdout && exit == 1
    case SuccessfulDirectoryStatus(call, batch) =>
      calls == [call] + batch.statusCalls &&
      Spec.StatusRequest(call, beforeFs, directory, true) &&
      call.ok && call.status.kind == BenchWorld.DirectoryKind &&
      batch.firstStatus == firstStatus + 1 &&
      BatchMoveStatusEvidenceFor(
        sources, directory, cmd, observations, batch
      ) &&
      exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
        BatchEvidenceFor(
          sources, directory, cmd, beforeFs, cwd, afterFs,
          hadError, out, err, batch
        ) &&
        exit == (if hadError then 1 else 0) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + err
  }

  ghost predicate RunStatusEvidenceFor(
    raw: Schema.MvCmdRaw,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: BenchWorld.StatusTimeObservations,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: RunStatusEvidence
  )
  {
    var cmd := Schema.Command(raw);
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
        |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
         |cmd.operands| > 2) then
       evidence == NoRunStatus && |calls| == 0
     else if cmd.targetDirectory != "" then
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           cmd.operands, cmd.targetDirectory, cmd,
           beforeFs, cwd, afterFs,
           beforeStdout, afterStdout, beforeStderr, afterStderr,
           exit, observations, firstStatus, calls, directoryEvidence
         )
       case _ => false
     else if |cmd.operands| == 2 then
       var source := NormalizeSource(
         cmd.operands[0], cmd.stripTrailingSlashes
       );
       var destination := cmd.operands[1];
       if cmd.noTargetDirectory then
         match evidence
         case DirectMoveStatus(step) =>
           calls == step.statusCalls &&
           step.firstStatus == firstStatus &&
           step.beforeFs == beforeFs && step.afterFs == afterFs &&
           StepEvidenceFor(source, destination, cmd, cwd, step) &&
           StepStatusEvidenceFor(source, destination, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           afterStdout == beforeStdout + step.outcome.stdoutFragment &&
           afterStderr == beforeStderr + step.outcome.stderrFragment
         case _ => false
       else
         match evidence
         case ProbedMoveStatus(call, step) =>
           calls == [call] + step.statusCalls &&
           Spec.StatusRequest(call, beforeFs, destination, true) &&
           step.firstStatus == firstStatus + 1 &&
           step.beforeFs == beforeFs && step.afterFs == afterFs &&
           var target :=
             if call.ok && call.status.kind == BenchWorld.DirectoryKind then
               TargetInDirectory(destination, source)
             else destination;
           StepEvidenceFor(source, target, cmd, cwd, step) &&
           StepStatusEvidenceFor(source, target, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           afterStdout == beforeStdout + step.outcome.stdoutFragment &&
           afterStderr == beforeStderr + step.outcome.stderrFragment
         case _ => false
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           sources, directory, cmd,
           beforeFs, cwd, afterFs,
           beforeStdout, afterStdout, beforeStderr, afterStderr,
           exit, observations, firstStatus, calls, directoryEvidence
         )
       case _ => false)
  }

  ghost predicate CoreSummaryIO(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + Spec.HelpTextSpec() &&
      io.stderr() == preStderr
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + Spec.VersionTextSpec() &&
      io.stderr() == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      RunIntoDirectoryEvidenceFields(cmd.operands, cmd.targetDirectory, true, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
    else if |cmd.operands| == 1 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      RunTwoOperandEvidenceFields(cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
    else
      RunIntoDirectoryEvidenceFields(cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], false, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
  }

  twostate predicate CoreSummary(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    CoreSummaryIO(
      raw,
      old(io.fs()),
      old(io.cwd()),
      old(io.stdout()),
      old(io.stderr()),
      io,
      exit
    ) &&
    exists calls: seq<Spec.StatusCallEvidence> ::
      io.statusCursor() == old(io.statusCursor()) + |calls| &&
      StatusCallsFor(io.statusObservations(), old(io.statusCursor()), calls)
  }

  method {:isolate_assertions} RunCore(
    raw: Schema.MvCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int, ghost calls: seq<Spec.StatusCallEvidence>,
             ghost runEvidence: RunStatusEvidence)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit)
    ensures CoreSummaryIO(
              raw,
              old(io.fs()),
              old(io.cwd()),
              old(io.stdout()),
              old(io.stderr()),
              io,
              exit
            )
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(io.statusObservations(), old(io.statusCursor()), calls)
    ensures RunStatusEvidenceFor(
              raw, old(io.fs()), old(io.cwd()), io.fs(),
              old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
              exit, io.statusObservations(), old(io.statusCursor()),
              io.statusCursor(), calls, runEvidence)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var firstStatus := io.statusCursor();
    calls := [];
    runEvidence := NoRunStatus;
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup {
      var err := GetInvalidBackupArgumentMessage(cmd.invalidBackupArg);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeInvalidUpdate {
      var err := GetInvalidUpdateArgumentMessage(cmd.invalidUpdateArg);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.targetDirectory != "" && cmd.noTargetDirectory {
      var err := GetTargetDirectoryConflictMessage();
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if |cmd.operands| == 0 {
      var err := GetMissingFileOperandMessage();
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.targetDirectory != "" {
      ghost var directoryEvidence: DirectoryStatusEvidence;
      exit, calls, directoryEvidence := RunIntoDirectory(
        cmd.operands, cmd.targetDirectory, true, cmd, io
      );
      runEvidence := DirectoryRunStatus(directoryEvidence);
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      assert cmd.mode == Schema.ModeRun;
      assert !cmd.noTargetDirectory;
      assert |cmd.operands| > 0;
      assert io.statusCursor() == firstStatus + |calls|;
      assert StatusCallsFor(
        io.statusObservations(), firstStatus, calls
      );
      assert DirectoryStatusEvidenceFor(
        cmd.operands, cmd.targetDirectory, cmd,
        preFs, preCwd, io.fs(),
        preStdout, io.stdout(), preStderr, io.stderr(),
        exit, io.statusObservations(), firstStatus,
        calls, directoryEvidence
      );
      assert RunStatusEvidenceFor(
        raw, preFs, preCwd, io.fs(),
        preStdout, io.stdout(), preStderr, io.stderr(),
        exit, io.statusObservations(), firstStatus,
        io.statusCursor(), calls, runEvidence
      );
      assert CoreSummary(raw, io, exit);
      return;
    }

    if |cmd.operands| == 1 {
      var err := GetMissingDestinationMessage(cmd.operands[0]);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.noTargetDirectory && |cmd.operands| > 2 {
      var err := GetExtraOperandMessage(cmd.operands[2]);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if |cmd.operands| == 2 {
      var source := NormalizeSource(cmd.operands[0], cmd.stripTrailingSlashes);
      var dest := cmd.operands[1];
      var target := dest;
      var dirOk := false;
      var isDir := false;
      var dirErr := 0;
      ghost var directoryCall := Spec.StatusCallEvidence(
        preFs, dest, true, false, BenchWorld.DEFAULT_FILE_STATUS, 0
      );
      if !cmd.noTargetDirectory {
        var getFileStatusResult4 := io.GetFileStatus(dest, true);
        var rawMetadataOk4 := getFileStatusResult4.Ok?;
        var rawMetadataStatus4 := IOContract.ResultValue(getFileStatusResult4, BenchWorld.DEFAULT_FILE_STATUS);
        var rawMetadataErr4 := IOContract.ResultErrno(getFileStatusResult4);
        directoryCall := Spec.StatusCallEvidence(preFs, dest, true,
          rawMetadataOk4, rawMetadataStatus4, rawMetadataErr4);
        calls := [directoryCall];
        IOContract.FileStatusStructureImpliesMetadata(io.fs(), dest, true, rawMetadataOk4, rawMetadataStatus4, rawMetadataErr4);
        dirOk := rawMetadataOk4;
        isDir := rawMetadataStatus4.kind == BenchWorld.DirectoryKind;
        dirErr := rawMetadataErr4;
        if dirOk && isDir {
          target := TargetInDirectory(dest, source);
        }
      }
      ghost var preMoveFs := io.fs();
      var hadError, out, errOut, step := MoveOne(
        source, target, cmd, io
      );
      assert StatusCallsFor(io.statusObservations(), firstStatus, calls);
      assert step.firstStatus == firstStatus + |calls|;
      assert StatusCallsFor(
        io.statusObservations(), firstStatus + |calls|,
        step.statusCalls
      );
      StatusCallsConcat(io.statusObservations(), firstStatus,
                        calls, step.statusCalls);
      calls := calls + step.statusCalls;
      runEvidence :=
        if cmd.noTargetDirectory then DirectMoveStatus(step)
        else ProbedMoveStatus(directoryCall, step);
      ghost var movedFs := io.fs();
      var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
      var _ := io.WriteStderr(errOut, BenchWorld.ThrowOnError);
      exit := if hadError then 1 else 0;
      assert preMoveFs == preFs;
      assert (exit == 1) == hadError;
      assert step.beforeFs == preFs;
      assert step.afterFs == movedFs;
      assert step.outcome == Spec.MoveOutcome(out, errOut, hadError);
      assert io.fs() == movedFs;
      assert io.stdout() == preStdout + out;
      assert io.stderr() == preStderr + errOut;
      if !cmd.noTargetDirectory {
        if dirOk && isDir {
          assert target == TargetInDirectory(dest, source);
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, true, true, dirErr);
          ghost var batch := BatchEvidence(
            [step],
            [preFs, movedFs],
            [step.outcome],
            [step.outcome.stdoutFragment],
            [step.outcome.stderrFragment],
            step.firstStatus,
            step.statusCalls,
            [step.firstStatus, step.firstStatus + |step.statusCalls|]
          );
          assert Spec.ConcatenateFragments(
              [step.outcome.stdoutFragment]
            ) == out;
          assert Spec.ConcatenateFragments(
              [step.outcome.stderrFragment]
            ) == errOut;
          reveal BatchStepEvidenceFor();
          assert BatchStepEvidenceFor(
              cmd.operands[0],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              step.outcome,
              step.outcome.stdoutFragment,
              step.outcome.stderrFragment,
              step
            );
          hide BatchStepEvidenceFor();
          assert forall i: nat | i < 1 ::
            BatchStepEvidenceFor(
              [cmd.operands[0]][i], dest, cmd,
              batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
              batch.outcomes[i], batch.stdoutFragments[i],
              batch.stderrFragments[i], batch.steps[i]
            );
          assert step.outcome.failed == hadError;
          assert |batch.outcomes| == 1;
          assert batch.outcomes[0] == step.outcome;
          assert (exists i: nat :: i < |batch.outcomes| &&
            batch.outcomes[i].failed) <==> batch.outcomes[0].failed by {
            if exists i: nat :: i < |batch.outcomes| &&
              batch.outcomes[i].failed {
              var i: nat :| i < |batch.outcomes| &&
                batch.outcomes[i].failed;
              assert i == 0;
            } else if batch.outcomes[0].failed {
              assert 0 < |batch.outcomes|;
            }
          }
          assert hadError <==>
            exists i: nat :: i < |batch.outcomes| &&
              batch.outcomes[i].failed;
          PackageBatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              hadError,
              out,
              errOut,
              batch
            );
          ghost var batchOutcome := step.outcome;
          assert batchOutcome.failed == hadError;
          assert batchOutcome.stdoutFragment == out;
          assert batchOutcome.stderrFragment == errOut;
          assert BatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              batchOutcome.failed,
              batchOutcome.stdoutFragment,
              batchOutcome.stderrFragment,
              batch
            );
          assert exit == (if batchOutcome.failed then 1 else 0);
          assert io.stdout() ==
                 preStdout + batchOutcome.stdoutFragment;
          assert io.stderr() ==
                 preStderr + batchOutcome.stderrFragment;
          assert
            IOContract.IsDirectoryContractFields(
              preFs, dest, true, true, true, dirErr
            ) &&
            BatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              batchOutcome.failed,
              batchOutcome.stdoutFragment,
              batchOutcome.stderrFragment,
              batch
            ) &&
            exit == (if batchOutcome.failed then 1 else 0) &&
            io.stdout() ==
            preStdout + batchOutcome.stdoutFragment &&
            io.stderr() ==
            preStderr + batchOutcome.stderrFragment;
          assert exists
              directoryErr0: int,
              batch0: BatchEvidence,
              outcome0: Spec.MoveOutcome
              ::
                IOContract.IsDirectoryContractFields(
                  preFs, dest, true, true, true, directoryErr0
                ) &&
                BatchEvidenceFor(
                  [cmd.operands[0]],
                  dest,
                  cmd,
                  preFs,
                  preCwd,
                  movedFs,
                  outcome0.failed,
                  outcome0.stdoutFragment,
                  outcome0.stderrFragment,
                  batch0
                ) &&
                exit == (if outcome0.failed then 1 else 0) &&
                io.stdout() == preStdout + outcome0.stdoutFragment &&
                io.stderr() == preStderr + outcome0.stderrFragment;
        } else if dirOk && !isDir {
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, true, false, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, true, false, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        } else if !dirOk && !isDir {
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, false, false, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, false, false, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        } else {
          assert !dirOk && isDir;
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, false, true, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, false, true, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        }
      } else {
        assert target == dest;
        assert exists step0: StepEvidence ::
            StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
            step0.beforeFs == preFs &&
            step0.afterFs == movedFs &&
            exit == (if step0.outcome.failed then 1 else 0) &&
            io.stdout() == preStdout + step0.outcome.stdoutFragment &&
            io.stderr() == preStderr + step0.outcome.stderrFragment;
      }
      assert RunTwoOperandEvidenceFields(
          cmd, preFs, preCwd, io.fs(),
          preStdout, preStderr, io.stdout(), io.stderr(), exit
        );
      hide RunTwoOperandEvidenceFields();
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      assert io.statusCursor() == firstStatus + |calls|;
      assert StatusCallsFor(
        io.statusObservations(), firstStatus, calls
      );
      if cmd.noTargetDirectory {
        assert calls == step.statusCalls;
        assert step.firstStatus == firstStatus;
        assert step.beforeFs == preFs && step.afterFs == io.fs();
      } else {
        assert calls == [directoryCall] + step.statusCalls;
        assert Spec.StatusRequest(
          directoryCall, preFs, dest, true
        );
        assert step.firstStatus == firstStatus + 1;
        assert step.beforeFs == preFs && step.afterFs == io.fs();
      }
      assert RunStatusEvidenceFor(
        raw, preFs, preCwd, io.fs(),
        preStdout, io.stdout(), preStderr, io.stderr(),
        exit, io.statusObservations(), firstStatus,
        io.statusCursor(), calls, runEvidence
      );
      assert CoreSummary(raw, io, exit);
      return;
    }

    var directory := cmd.operands[|cmd.operands| - 1];
    var sources := cmd.operands[..|cmd.operands| - 1];
    ghost var directoryEvidence: DirectoryStatusEvidence;
    exit, calls, directoryEvidence := RunIntoDirectory(
      sources, directory, false, cmd, io
    );
    runEvidence := DirectoryRunStatus(directoryEvidence);
    assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
    assert RunStatusEvidenceFor(
      raw, preFs, preCwd, io.fs(),
      preStdout, io.stdout(), preStderr, io.stderr(),
      exit, io.statusObservations(), firstStatus,
      io.statusCursor(), calls, runEvidence
    );
    assert CoreSummary(raw, io, exit);
  }

  method CheckTargetDirectory(directory: string, io: BenchIO.IO)
    returns (ok: bool, err: int, ghost call: Spec.StatusCallEvidence)
    modifies io.statusObservationsRegion
    ensures TargetDirectoryCheckSummaryFields(directory, old(io.fs()), ok, err)
    ensures Spec.StatusRequest(call, old(io.fs()), directory, true)
    ensures ok == (call.ok && call.status.kind == BenchWorld.DirectoryKind)
    ensures io.statusCursor() == old(io.statusCursor()) + 1
    ensures StatusCallsFor(io.statusObservations(), old(io.statusCursor()), [call])
  {
    var getFileStatusResult5 := io.GetFileStatus(directory, true);
    var rawMetadataOk3 := getFileStatusResult5.Ok?;
    var rawMetadataStatus3 := IOContract.ResultValue(getFileStatusResult5, BenchWorld.DEFAULT_FILE_STATUS);
    var rawMetadataErr3 := IOContract.ResultErrno(getFileStatusResult5);
    call := Spec.StatusCallEvidence(old(io.fs()), directory, true,
      rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3);
    IOContract.FileStatusStructureImpliesMetadata(io.fs(), directory, true, rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3);
    var statOk := rawMetadataOk3;
    var isDir := rawMetadataStatus3.kind == BenchWorld.DirectoryKind;
    var statErr := rawMetadataErr3;
    ok := statOk && isDir;
    if statOk && !isDir {
      err := Errno.ENOTDIR;
    } else {
      err := statErr;
    }
  }

  method {:isolate_assertions} RunIntoDirectory(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (exit: int, ghost calls: seq<Spec.StatusCallEvidence>,
             ghost evidence: DirectoryStatusEvidence)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion
    ensures RunIntoDirectoryEvidenceFields(
              sources,
              directory,
              explicitTargetDirectory,
              cmd,
              old(io.fs()),
              old(io.cwd()),
              io.fs(),
              old(io.stdout()),
              old(io.stderr()),
              io.stdout(),
              io.stderr(),
              exit
            )
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(io.statusObservations(), old(io.statusCursor()), calls)
    ensures DirectoryStatusEvidenceFor(
              sources, directory, cmd,
              old(io.fs()), old(io.cwd()), io.fs(),
              old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
              exit, io.statusObservations(), old(io.statusCursor()),
              calls, evidence)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var firstStatus := io.statusCursor();
    var dirOk, dirErr, dirCall := CheckTargetDirectory(directory, io);
    calls := [dirCall];
    if !dirOk {
      evidence := FailedDirectoryStatus(dirCall);
      var err := GetTargetFailureMessage(directory, explicitTargetDirectory, dirErr);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := 1;
      assert TargetDirectoryCheckSummaryFields(directory, preFs, false, dirErr);
      assert RunIntoDirectoryEvidenceFields(
          sources, directory, explicitTargetDirectory, cmd,
          preFs, preCwd, io.fs(), preStdout, preStderr,
          io.stdout(), io.stderr(), exit
        );
      return;
    }

    var hadError, out, errOut, batch := MoveSourcesIntoDirectory(
      sources, directory, cmd, io
    );
    assert StatusCallsFor(io.statusObservations(), firstStatus, [dirCall]);
    assert batch.firstStatus == firstStatus + 1;
    assert StatusCallsFor(
      io.statusObservations(), firstStatus + 1, batch.statusCalls
    );
    StatusCallsConcat(io.statusObservations(), firstStatus,
                      [dirCall], batch.statusCalls);
    calls := [dirCall] + batch.statusCalls;
    evidence := SuccessfulDirectoryStatus(dirCall, batch);
    ghost var movedFs := io.fs();
    var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
    var _ := io.WriteStderr(errOut, BenchWorld.ThrowOnError);
    exit := if hadError then 1 else 0;
    assert dirErr == 0;
    assert (exit == 1) == hadError;
    assert TargetDirectoryCheckSummaryFields(directory, preFs, true, 0);
    assert io.fs() == movedFs;
    assert io.stdout() == preStdout + out;
    assert io.stderr() == preStderr + errOut;
    assert RunIntoDirectoryEvidenceFields(
        sources, directory, explicitTargetDirectory, cmd,
        preFs, preCwd, io.fs(), preStdout, preStderr,
        io.stdout(), io.stderr(), exit
      );
  }

  method {:isolate_assertions} MoveOne(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (
      hadError: bool,
      out: BenchWorld.Bytes,
      errOut: BenchWorld.Bytes,
      ghost step: StepEvidence
    )
    modifies io.fsRegion, io.statusObservationsRegion
    ensures StepEvidenceFor(source, target, cmd, old(io.cwd()), step)
    ensures StepStatusEvidenceFor(source, target, cmd, step)
    ensures step.beforeFs == old(io.fs())
    ensures step.afterFs == io.fs()
    ensures step.outcome == Spec.MoveOutcome(out, errOut, hadError)
    ensures step.firstStatus == old(io.statusCursor())
    ensures io.statusCursor() == step.firstStatus + |step.statusCalls|
    ensures StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var firstStatus := io.statusCursor();
    ghost var statusCalls: seq<Spec.StatusCallEvidence> := [];
    hadError := false;
    out := [];
    errOut := [];
    ghost var sameFileEvidence: SameFileEvidence := NoSameFileCheck;
    ghost var backupEvidence: BackupSelectionEvidence :=
      NoBackupSelection;
    ghost var renameCalls: seq<RenameCallEvidence> := [];
    ghost var backupFs := preFs;

    var getFileStatusResult6 := io.GetFileStatus(source, false);
    var rawMetadataOk2 := getFileStatusResult6.Ok?;
    var rawMetadataStatus2 := IOContract.ResultValue(getFileStatusResult6, BenchWorld.DEFAULT_FILE_STATUS);
    var rawMetadataErr2 := IOContract.ResultErrno(getFileStatusResult6);
    ghost var nextStatusCall := Spec.StatusCallEvidence(
      preFs, source, false,
      rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2
    );
    StatusCallsSnoc(io.statusObservations(), firstStatus,
                    statusCalls, nextStatusCall);
    statusCalls := statusCalls + [nextStatusCall];
    IOContract.FileStatusStructureImpliesMetadata(io.fs(), source, false, rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2);
    var sourceOk := rawMetadataOk2;
    var sourceIsDir := rawMetadataStatus2.kind == BenchWorld.DirectoryKind;
    var sourceErr := rawMetadataErr2;
    if !sourceOk {
      hadError := true;
      errOut := GetSourceStatFailureMessage(source, sourceErr);
      step := MakeStepEvidence(
        preFs, io.fs(), out, errOut, hadError,
        sourceOk, sourceIsDir, sourceErr,
        false, false, 0,
        sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
      );
      PackageSourceFailureStep(
        source, target, cmd, preCwd, step
      );
      assert StepStatusEvidenceFor(source, target, cmd, step);
      assert step.firstStatus == firstStatus;
      assert step.statusCalls == statusCalls;
      assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
      assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
      return;
    }

    var getFileStatusResult7 := io.GetFileStatus(target, false);
    var rawMetadataOk1 := getFileStatusResult7.Ok?;
    var rawMetadataStatus1 := IOContract.ResultValue(getFileStatusResult7, BenchWorld.DEFAULT_FILE_STATUS);
    var rawMetadataErr1 := IOContract.ResultErrno(getFileStatusResult7);
    nextStatusCall := Spec.StatusCallEvidence(
      preFs, target, false,
      rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1
    );
    StatusCallsSnoc(io.statusObservations(), firstStatus,
                    statusCalls, nextStatusCall);
    statusCalls := statusCalls + [nextStatusCall];
    IOContract.FileStatusStructureImpliesMetadata(io.fs(), target, false, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
    var found := rawMetadataOk1;
    var existsErr := rawMetadataErr1;
    assert found == IOContract.PathExistsContractFields(
      preFs, target, false, true, 0);
    if found {
      if cmd.overwriteMode == Schema.OverwriteSkip {
        if cmd.debug {
          out := GetDebugSkipMessage(target);
        }
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
        );
        PackageOverwriteSkipStep(
          source, target, cmd, preCwd, step
        );
        assert StepStatusEvidenceFor(source, target, cmd, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
        return;
      }

      if cmd.updateMode == Schema.UpdateNone {
        if cmd.debug {
          out := GetDebugSkipMessage(target);
        }
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
        );
        PackageUpdateNoneStep(
          source, target, cmd, preCwd, step
        );
        assert StepStatusEvidenceFor(source, target, cmd, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
        return;
      }

      if cmd.updateMode == Schema.UpdateNoneFail {
        hadError := true;
        errOut := GetNotReplacingMessage(target);
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
        );
        PackageUpdateNoneFailStep(
          source, target, cmd, preCwd, step
        );
        assert StepStatusEvidenceFor(source, target, cmd, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
        return;
      }

      var sourceMetadata := CaptureMetadata(source, false, io);
      nextStatusCall := MetadataStatusCall(preFs, source, false, sourceMetadata);
      StatusCallsSnoc(io.statusObservations(), firstStatus,
                      statusCalls, nextStatusCall);
      statusCalls := statusCalls + [nextStatusCall];
      var targetMetadata := CaptureMetadata(target, false, io);
      nextStatusCall := MetadataStatusCall(preFs, target, false, targetMetadata);
      StatusCallsSnoc(io.statusObservations(), firstStatus,
                      statusCalls, nextStatusCall);
      statusCalls := statusCalls + [nextStatusCall];
      assert io.statusCursor() == firstStatus + |statusCalls|;
      StrictMetadataSuccess(
        preFs, source, sourceIsDir, sourceErr, sourceMetadata
      );
      ExistingMetadataSuccess(
        preFs, target, existsErr, targetMetadata
      );
      var sourceEntry := CaptureEntryName(source, io);
      nextStatusCall := MetadataStatusCall(
        preFs, sourceEntry.parent, false, sourceEntry.parentMetadata);
      StatusCallsSnoc(io.statusObservations(), firstStatus,
                      statusCalls, nextStatusCall);
      statusCalls := statusCalls + [nextStatusCall];
      assert io.statusCursor() == firstStatus + |statusCalls|;
      var targetEntry := CaptureEntryName(target, io);
      nextStatusCall := MetadataStatusCall(
        preFs, targetEntry.parent, false, targetEntry.parentMetadata);
      StatusCallsSnoc(io.statusObservations(), firstStatus,
                      statusCalls, nextStatusCall);
      statusCalls := statusCalls + [nextStatusCall];
      assert io.statusCursor() == firstStatus + |statusCalls|;
      var sourceFollowed: OptionalMetadataEvidence :=
        NoMetadataEvidence;
      var sourceReferentEntry: OptionalEntryNameEvidence :=
        NoEntryNameEvidence;
      if sourceMetadata.isSymlink {
        assert io.fs() == preFs;
        var followed := CaptureMetadata(source, true, io);
        nextStatusCall := MetadataStatusCall(preFs, source, true, followed);
        StatusCallsSnoc(io.statusObservations(), firstStatus,
                        statusCalls, nextStatusCall);
        statusCalls := statusCalls + [nextStatusCall];
        assert io.statusCursor() == firstStatus + |statusCalls|;
        assert MetadataEvidenceFor(preFs, source, true, followed);
        sourceFollowed := SomeMetadataEvidence(followed);
        var resolvePathIdentityResult := io.ResolvePathIdentity(source);
        var resolveOk := resolvePathIdentityResult.Ok?;
        var resolvedSource := IOContract.ResultValue(resolvePathIdentityResult, "");
        var resolveErr := IOContract.ResultErrno(resolvePathIdentityResult);
        if resolveOk {
          assert IOContract.ResolvePathIdentityContractFields(
              preFs, preCwd, source, true, resolvedSource, 0
            );
          var referentEntry := CaptureEntryName(resolvedSource, io);
          nextStatusCall := MetadataStatusCall(
            preFs, referentEntry.parent, false,
            referentEntry.parentMetadata);
          StatusCallsSnoc(io.statusObservations(), firstStatus,
                          statusCalls, nextStatusCall);
          statusCalls := statusCalls + [nextStatusCall];
          sourceReferentEntry :=
            SomeEntryNameEvidence(resolvedSource, referentEntry);
        } else {
          assert IOContract.ResolvePathIdentityContractFields(
              preFs, preCwd, source, false, "", resolveErr
            );
          sourceReferentEntry :=
            FailedEntryNameEvidence(resolveErr);
        }
      }
      assert io.statusCursor() == firstStatus + |statusCalls|;
      ghost var afterEntries :=
        if sourceMetadata.isSymlink then
          (if sourceReferentEntry.SomeEntryNameEvidence? then 8 else 7)
        else 6;
      assert |statusCalls| == afterEntries;
      assert Spec.StatusRequest(statusCalls[0], preFs, source, false);
      assert Spec.StatusRequest(statusCalls[1], preFs, target, false);
      assert statusCalls[2] == MetadataStatusCall(
        preFs, source, false, sourceMetadata
      );
      assert statusCalls[3] == MetadataStatusCall(
        preFs, target, false, targetMetadata
      );
      assert statusCalls[4] == MetadataStatusCall(
        preFs, sourceEntry.parent, false, sourceEntry.parentMetadata
      );
      assert statusCalls[5] == MetadataStatusCall(
        preFs, targetEntry.parent, false, targetEntry.parentMetadata
      );
      if sourceMetadata.isSymlink {
        match sourceFollowed {
          case SomeMetadataEvidence(followed) =>
            assert statusCalls[6] == MetadataStatusCall(
              preFs, source, true, followed
            );
          case _ =>
        }
        match sourceReferentEntry {
          case SomeEntryNameEvidence(_, referentEntry) =>
            assert statusCalls[7] == MetadataStatusCall(
              preFs, referentEntry.parent, false,
              referentEntry.parentMetadata
            );
          case _ =>
        }
      }
      var sameEntry :=
        sourceEntry.parentMetadata.ok &&
        targetEntry.parentMetadata.ok &&
        sourceEntry.parentMetadata.key ==
        targetEntry.parentMetadata.key &&
        sourceEntry.leaf == targetEntry.leaf;
      var referentSameEntry := false;
      match sourceReferentEntry {
        case SomeEntryNameEvidence(_, referentEntry) =>
          referentSameEntry :=
            referentEntry.parentMetadata.ok &&
            targetEntry.parentMetadata.ok &&
            referentEntry.parentMetadata.key ==
            targetEntry.parentMetadata.key &&
            referentEntry.leaf == targetEntry.leaf;
        case _ =>
      }
      var rejectSameFile :=
        sameEntry ||
        (cmd.backupMode == Schema.BackupOff &&
         (sourceMetadata.key == targetMetadata.key ||
          referentSameEntry));
      var sameFileDecision :=
        if rejectSameFile
        then Spec.RejectSameFile
        else Spec.ContinueMove;
      assert sameFileDecision ==
             if EvidenceNamesSame(sourceEntry, targetEntry) ||
                (cmd.backupMode == Schema.BackupOff &&
                 ((sourceMetadata.ok &&
                   targetMetadata.ok &&
                   sourceMetadata.key == targetMetadata.key) ||
                  ReferentEvidenceNamesTarget(
                    sourceReferentEntry, targetEntry
                  )))
             then Spec.RejectSameFile
             else Spec.ContinueMove;
      sameFileEvidence := CheckedSameFile(
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        NoBackupCollisionCheck,
        sameFileDecision
      );
      PackageSameFileEvidence(
        cmd,
        preFs,
        preCwd,
        source,
        target,
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        NoBackupCollisionCheck,
        sameFileDecision
      );
      if sameFileDecision == Spec.RejectSameFile {
        hadError := true;
        errOut := GetSameFileMessage(source, target);
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
        );
        PackageSameFileRejectStep(
          source, target, cmd, preCwd, step
        );
        assert StepStatusEvidenceFor(source, target, cmd, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
        return;
      }
      assert sameFileDecision == Spec.ContinueMove;

      if cmd.updateMode == Schema.UpdateOlder {
        if !SourceNewer(
            sourceMetadata.times.mtimeSec,
            sourceMetadata.times.mtimeNsec,
            targetMetadata.times.mtimeSec,
            targetMetadata.times.mtimeNsec
          ) {
          if cmd.debug {
            out := GetDebugSkipMessage(target);
          }
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
          );
          PackageUpdateOlderSkipStep(
            source, target, cmd, preCwd, step
          );
          assert StepStatusEvidenceFor(source, target, cmd, step);
          assert step.firstStatus == firstStatus;
          assert step.statusCalls == statusCalls;
          assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
          assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
          return;
        }
      }

      ghost var collisionEvidence: BackupCollisionEvidence :=
        NoBackupCollisionCheck;
      if (cmd.backupMode == Schema.BackupSimple ||
          cmd.backupMode == Schema.BackupExisting) &&
         sourceEntry.leaf ==
         targetEntry.leaf + cmd.backupSuffix
      {
        var candidateMetadata := CaptureMetadata(
          SimpleBackupPath(target, cmd.backupSuffix), true, io
        );
        nextStatusCall := MetadataStatusCall(
          preFs, SimpleBackupPath(target, cmd.backupSuffix), true,
          candidateMetadata);
        StatusCallsSnoc(io.statusObservations(), firstStatus,
                        statusCalls, nextStatusCall);
        statusCalls := statusCalls + [nextStatusCall];
        assert io.statusCursor() == firstStatus + |statusCalls|;
        assert |statusCalls| == afterEntries + 1;
        assert statusCalls[afterEntries] == MetadataStatusCall(
          preFs, SimpleBackupPath(target, cmd.backupSuffix), true,
          candidateMetadata
        );
        collisionEvidence := CheckedBackupCollision(
          sourceMetadata, candidateMetadata
        );
        sameFileEvidence := CheckedSameFile(
          sourceMetadata,
          targetMetadata,
          sourceFollowed,
          sourceEntry,
          targetEntry,
          sourceReferentEntry,
          collisionEvidence,
          sameFileDecision
        );
        PackageSameFileEvidence(
          cmd,
          preFs,
          preCwd,
          source,
          target,
          sourceMetadata,
          targetMetadata,
          sourceFollowed,
          sourceEntry,
          targetEntry,
          sourceReferentEntry,
          collisionEvidence,
          sameFileDecision
        );
        if candidateMetadata.ok &&
           candidateMetadata.key == sourceMetadata.key
        {
          assert BackupCollisionDetected(collisionEvidence);
          assert statusCalls[afterEntries].ok;
          assert statusCalls[afterEntries].status.hostKey ==
            statusCalls[2].status.hostKey;
          hadError := true;
          errOut :=
            GetBackupWouldDestroySourceMessage(source, target);
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
          );
          PackageExistingTargetRenameStep(
            source, target, cmd, preCwd, step
          );
          assert StepStatusEvidenceFor(source, target, cmd, step);
          assert step.firstStatus == firstStatus;
          assert step.statusCalls == statusCalls;
          assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
          assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
          return;
        }
      }
      assert BackupCollisionEvidenceFor(
          cmd,
          preFs,
          source,
          target,
          sourceMetadata,
          sourceEntry,
          targetEntry,
          collisionEvidence
        );
      assert !BackupCollisionDetected(collisionEvidence);
      ghost var collisionNeeded :=
        (cmd.backupMode == Schema.BackupSimple ||
         cmd.backupMode == Schema.BackupExisting) &&
        sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
      ghost var afterCollision := afterEntries +
        (if collisionNeeded then 1 else 0);
      assert |statusCalls| == afterCollision;
      assert io.statusCursor() == firstStatus + |statusCalls|;
      assert io.fs() == preFs;

      if cmd.backupMode != Schema.BackupOff {
        ghost var fsBeforeBackup := io.fs();
        var backupPath, selectedBackup, backupCalls := PickBackupPath(
          target, cmd.backupMode, cmd.backupSuffix, io
        );
        StatusCallsConcat(io.statusObservations(), firstStatus,
                          statusCalls, backupCalls);
        statusCalls := statusCalls + backupCalls;
        assert io.statusCursor() == firstStatus + |statusCalls|;
        assert statusCalls[afterCollision..] == backupCalls;
        assert BackupStatusSuffixFor(
          cmd.backupMode, preFs, target, statusCalls[afterCollision..]
        );
        backupEvidence := selectedBackup;
        assert fsBeforeBackup == preFs;
        assert io.fs() == preFs;
        ghost var backupStatusTemplate := MakeStepEvidence(
          preFs, preFs, [], [], false,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, [], preFs,
          StatusTranscript(firstStatus, statusCalls)
        );
        assert StepStatusEvidenceFor(
          source, target, cmd, backupStatusTemplate);
        var renamePathResult := io.RenamePath(target, backupPath);
        var okBackup := renamePathResult.Ok?;
        var backupErr := IOContract.ResultErrno(renamePathResult);
        ghost var afterBackupFs := io.fs();
        backupFs := afterBackupFs;
        ghost var backupCall :=
          RenameCallEvidence(okBackup, backupErr, afterBackupFs);
        renameCalls := [backupCall];
        assert IOContract.RenamePathContractFields(
            preFs,
            target,
            backupPath,
            okBackup,
            backupErr,
            afterBackupFs
          );
        if !okBackup {
          hadError := true;
          errOut := GetRenameFailureMessage(source, target, backupErr);
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
          );
          assert step.firstStatus == firstStatus;
          assert step.statusCalls == statusCalls;
          assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
          PackageExistingTargetRenameStep(
            source, target, cmd, preCwd, step
          );
          StepStatusEvidenceTransfer(
            source, target, cmd, backupStatusTemplate, step);
          assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
          return;
        }

        var renamePathResult2 := io.RenamePath(source, target);
        var okRenameWithBackup := renamePathResult2.Ok?;
        var renameErrWithBackup := IOContract.ResultErrno(renamePathResult2);
        assert io.statusCursor() == firstStatus + |statusCalls|;
        ghost var afterRenameFs := io.fs();
        ghost var sourceCall := RenameCallEvidence(
          okRenameWithBackup,
          renameErrWithBackup,
          afterRenameFs
        );
        renameCalls := [backupCall, sourceCall];
        assert IOContract.RenamePathContractFields(
            afterBackupFs,
            source,
            target,
            okRenameWithBackup,
            renameErrWithBackup,
            afterRenameFs
          );
        hadError := !okRenameWithBackup;
        if okRenameWithBackup {
          if cmd.verbose || cmd.debug {
            out := GetVerboseRenameWithBackupMessage(source, target, backupPath);
          }
          assert out == StepSuccessStdout(source, target, backupPath, cmd.verbose, cmd.debug);
          assert errOut == [];
        } else {
          errOut := GetSourceRenameFailureMessage(
            source, target, sourceIsDir, false, renameErrWithBackup
          );
          assert out == [];
        }
        assert IOContract.PathExistsContractFields(preFs, target, false, true, existsErr);
        assert cmd.overwriteMode != Schema.OverwriteSkip;
        assert !(cmd.updateMode == Schema.UpdateNone || cmd.updateMode == Schema.UpdateNoneFail);
        assert RenameEvidenceFor(
            source,
            target,
            sourceIsDir,
            backupPath,
            cmd.verbose,
            cmd.debug,
            preFs,
            preCwd,
            io.fs(),
            Spec.MoveOutcome(out, errOut, hadError),
            renameCalls,
            backupFs
          );
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
        );
        PackageExistingTargetRenameStep(
          source, target, cmd, preCwd, step
        );
        StepStatusEvidenceTransfer(
          source, target, cmd, backupStatusTemplate, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
        return;
      }

      assert cmd.backupMode == Schema.BackupOff;
    }

    assert io.fs() == preFs;
    assert io.statusCursor() == firstStatus + |statusCalls|;
    var renamePathResult3 := io.RenamePath(source, target);
    var okRename := renamePathResult3.Ok?;
    var renameErr := IOContract.ResultErrno(renamePathResult3);
    assert io.statusCursor() == firstStatus + |statusCalls|;
    ghost var afterRenameFs := io.fs();
    assert IOContract.RenamePathContractFields(
        preFs,
        source,
        target,
        okRename,
        renameErr,
        afterRenameFs
      );
    renameCalls := [
      RenameCallEvidence(okRename, renameErr, afterRenameFs)
    ];
    hadError := !okRename;
    if okRename && (cmd.verbose || cmd.debug) {
      out := GetVerboseRenameMessage(source, target);
    }
    if !okRename {
      errOut := GetSourceRenameFailureMessage(
        source, target, sourceIsDir, found, renameErr
      );
      assert out == [];
    } else {
      assert out == StepSuccessStdout(source, target, "", cmd.verbose, cmd.debug);
      assert errOut == [];
    }
    if found {
      assert IOContract.PathExistsContractFields(preFs, target, false, true, existsErr);
      assert cmd.overwriteMode != Schema.OverwriteSkip;
      assert !(cmd.updateMode == Schema.UpdateNone || cmd.updateMode == Schema.UpdateNoneFail);
      assert cmd.backupMode == Schema.BackupOff;
    } else {
      assert IOContract.PathExistsContractFields(preFs, target, false, false, existsErr);
    }
    step := MakeStepEvidence(
      preFs, io.fs(), out, errOut, hadError,
      sourceOk, sourceIsDir, sourceErr,
      true, found, existsErr,
      sameFileEvidence, backupEvidence, renameCalls, backupFs,
        StatusTranscript(firstStatus, statusCalls)
    );
    assert step.firstStatus == firstStatus;
    assert step.statusCalls == statusCalls;
    assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
    if found {
      PackageExistingTargetRenameStep(
        source, target, cmd, preCwd, step
      );
    } else {
      PackageMissingTargetStep(
        source, target, cmd, preCwd, step
      );
    }
    assert StepStatusEvidenceFor(source, target, cmd, step);
    assert StatusCallsFor(io.statusObservations(), step.firstStatus, step.statusCalls);
  }

  method {:vcs_split_on_every_assert} MoveSourcesIntoDirectory(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (
      hadError: bool,
      out: BenchWorld.Bytes,
      errOut: BenchWorld.Bytes,
      ghost batch: BatchEvidence
    )
    modifies io.fsRegion, io.statusObservationsRegion
    ensures BatchEvidenceFor(
              sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
              hadError, out, errOut, batch
            )
    ensures batch.firstStatus == old(io.statusCursor())
    ensures io.statusCursor() == batch.firstStatus + |batch.statusCalls|
    ensures StatusCallsFor(io.statusObservations(), batch.firstStatus, batch.statusCalls)
    ensures BatchStatusEvidenceFor(io.statusObservations(), batch)
    ensures BatchMoveStatusEvidenceFor(
              sources, directory, cmd, io.statusObservations(), batch)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var firstStatus := io.statusCursor();
    ghost var statusCalls: seq<Spec.StatusCallEvidence> := [];
    ghost var statusBounds: seq<nat> := [firstStatus];
    ghost var steps: seq<StepEvidence> := [];
    ghost var fsBounds: seq<BenchWorld.FileSystem> := [preFs];
    ghost var outcomes: seq<Spec.MoveOutcome> := [];
    ghost var stdoutFragments: seq<BenchWorld.Bytes> := [];
    ghost var stderrFragments: seq<BenchWorld.Bytes> := [];
    hadError := false;
    out := [];
    errOut := [];
    var i := 0;
    while i < |sources|
      invariant 0 <= i <= |sources|
      invariant |steps| == i
      invariant |fsBounds| == |steps| + 1
      invariant |outcomes| == |steps|
      invariant |stdoutFragments| == |steps|
      invariant |stderrFragments| == |steps|
      invariant io.statusCursor() == firstStatus + |statusCalls|
      invariant StatusCallsFor(io.statusObservations(), firstStatus, statusCalls)
      invariant |statusBounds| == |steps| + 1
      invariant statusBounds[0] == firstStatus
      invariant statusBounds[|steps|] == firstStatus + |statusCalls|
      invariant forall j: nat {:trigger statusBounds[j]} | j < |steps| ::
                  firstStatus <= statusBounds[j] <=
                    statusBounds[j + 1] <= firstStatus + |statusCalls| &&
                  steps[j].firstStatus == statusBounds[j] &&
                  statusBounds[j + 1] ==
                    statusBounds[j] + |steps[j].statusCalls| &&
                  statusCalls[
                    statusBounds[j] - firstStatus ..
                    statusBounds[j + 1] - firstStatus
                  ] == steps[j].statusCalls
      invariant fsBounds[0] == preFs
      invariant fsBounds[|fsBounds| - 1] == io.fs()
      invariant forall j: nat | j < |steps| ::
                  BatchStepEvidenceFor(
                    sources[j],
                    directory,
                    cmd,
                    fsBounds[j],
                    preCwd,
                    fsBounds[j + 1],
                    outcomes[j],
                    stdoutFragments[j],
                    stderrFragments[j],
                    steps[j]
                  )
      invariant forall j: nat | j < |steps| ::
                  var normalizedSource :=
                    NormalizeSource(sources[j], cmd.stripTrailingSlashes);
                  StepStatusEvidenceFor(
                    normalizedSource,
                    TargetInDirectory(directory, normalizedSource),
                    cmd,
                    steps[j]
                  )
      invariant Spec.ConcatenateFragments(stdoutFragments) == out
      invariant Spec.ConcatenateFragments(stderrFragments) == errOut
      invariant hadError <==>
                exists j: nat :: j < |outcomes| && outcomes[j].failed
      decreases |sources| - i
    {
      var prefixError := hadError;
      var prefixOut := out;
      var prefixErr := errOut;
      ghost var prefixSteps := steps;
      ghost var prefixFsBounds := fsBounds;
      ghost var prefixOutcomes := outcomes;
      ghost var prefixStdoutFragments := stdoutFragments;
      ghost var prefixStderrFragments := stderrFragments;
      ghost var prefixStatusBounds := statusBounds;
      ghost var prefixStatusCalls := statusCalls;
      ghost var observationsBeforeStep := io.statusObservations();
      assert StatusCallsFor(
        observationsBeforeStep, firstStatus, statusCalls);
      ghost var fsBeforeStep := io.fs();
      var source := sources[i];
      var normalizedSource := NormalizeSource(source, cmd.stripTrailingSlashes);
      var target := TargetInDirectory(directory, normalizedSource);
      assert target == TargetInDirectory(directory, normalizedSource);
      var stepError, stepOut, stepErr, step := MoveOne(
        normalizedSource, target, cmd, io
      );
      assert io.statusObservations() == observationsBeforeStep;
      assert step.firstStatus == firstStatus + |statusCalls|;
      StatusCallsAppendObservedStep(
        observationsBeforeStep, io.statusObservations(),
        firstStatus, statusCalls, step);
      statusCalls := statusCalls + step.statusCalls;
      assert statusCalls == prefixStatusCalls + step.statusCalls;
      StatusCallTail(prefixStatusCalls, step.statusCalls);
      statusBounds := statusBounds + [firstStatus + |statusCalls|];
      ghost var nextOutcome := step.outcome;
      steps := steps + [step];
      StatusBoundsSnoc(firstStatus, prefixStatusCalls,
        prefixStatusBounds, prefixSteps, step,
        statusCalls, statusBounds, steps);
      fsBounds := fsBounds + [step.afterFs];
      outcomes := outcomes + [nextOutcome];
      stdoutFragments :=
        stdoutFragments + [nextOutcome.stdoutFragment];
      stderrFragments :=
        stderrFragments + [nextOutcome.stderrFragment];
      hadError := prefixError || stepError;
      out := prefixOut + stepOut;
      errOut := prefixErr + stepErr;
      ConcatenateFragmentsSnoc(
        stdoutFragments[..|stdoutFragments| - 1],
        nextOutcome.stdoutFragment
      );
      ConcatenateFragmentsSnoc(
        stderrFragments[..|stderrFragments| - 1],
        nextOutcome.stderrFragment
      );
      assert step.outcome ==
             Spec.MoveOutcome(stepOut, stepErr, stepError);
      FailureExistsSnoc(
        prefixOutcomes, nextOutcome, prefixError
      );
      assert hadError <==>
             exists j: nat :: j < |outcomes| && outcomes[j].failed;
      reveal BatchStepEvidenceFor();
      assert BatchStepEvidenceFor(
          source,
          directory,
          cmd,
          fsBeforeStep,
          preCwd,
          step.afterFs,
          step.outcome,
          step.outcome.stdoutFragment,
          step.outcome.stderrFragment,
          step
        );
      hide BatchStepEvidenceFor();
      assert forall j: nat | j < |steps| ::
          BatchStepEvidenceFor(
            sources[j],
            directory,
            cmd,
            fsBounds[j],
            preCwd,
            fsBounds[j + 1],
            outcomes[j],
            stdoutFragments[j],
            stderrFragments[j],
            steps[j]
          ) by {
        forall j: nat | j < |steps|
          ensures BatchStepEvidenceFor(
                    sources[j],
                    directory,
                    cmd,
                    fsBounds[j],
                    preCwd,
                    fsBounds[j + 1],
                    outcomes[j],
                    stdoutFragments[j],
                    stderrFragments[j],
                    steps[j]
                  )
        {
          if j < i {
            assert steps[j] == prefixSteps[j];
            assert fsBounds[j] == prefixFsBounds[j];
            assert fsBounds[j + 1] == prefixFsBounds[j + 1];
            assert outcomes[j] == prefixOutcomes[j];
            assert stdoutFragments[j] ==
                   prefixStdoutFragments[j];
            assert stderrFragments[j] ==
                   prefixStderrFragments[j];
          } else {
            assert j == i;
            assert sources[j] == source;
          }
        }
      }
      assert |steps| == i + 1;
      assert |fsBounds| == |steps| + 1;
      assert |outcomes| == |steps|;
      assert |stdoutFragments| == |steps|;
      assert |stderrFragments| == |steps|;
      assert fsBounds[0] == preFs;
      assert fsBounds[|fsBounds| - 1] == io.fs();
      assert Spec.ConcatenateFragments(
          stdoutFragments
        ) == out;
      assert Spec.ConcatenateFragments(
          stderrFragments
        ) == errOut;
      assert forall j: nat | j < |steps| ::
          var normalized := NormalizeSource(sources[j], cmd.stripTrailingSlashes);
          StepStatusEvidenceFor(normalized, TargetInDirectory(directory, normalized), cmd, steps[j]) by {
        forall j: nat | j < |steps|
          ensures
            var normalized := NormalizeSource(sources[j], cmd.stripTrailingSlashes);
            StepStatusEvidenceFor(normalized, TargetInDirectory(directory, normalized), cmd, steps[j])
        {
          if j < i {
            assert steps[j] == prefixSteps[j];
          } else {
            assert j == i;
            assert steps[j] == step;
          }
        }
      }
      i := i + 1;
    }
    assert sources[..i] == sources;
    BatchStatusEvidenceFromParts(io.statusObservations(), firstStatus,
      statusCalls, statusBounds, steps, fsBounds, outcomes,
      stdoutFragments, stderrFragments);
    batch := BatchEvidence(
      steps,
      fsBounds,
      outcomes,
      stdoutFragments,
      stderrFragments,
      firstStatus,
      statusCalls,
      statusBounds
    );
    assert batch.firstStatus == firstStatus;
    assert batch.statusCalls == statusCalls;
    assert batch.statusBounds == statusBounds;
    assert batch.steps == steps;
    assert |batch.statusBounds| == |batch.steps| + 1;
    assert batch.statusBounds[0] == batch.firstStatus;
    assert batch.statusBounds[|batch.steps|] ==
           batch.firstStatus + |batch.statusCalls|;
    assert StatusCallsFor(io.statusObservations(), batch.firstStatus,
                          batch.statusCalls);
    assert BatchStatusEvidenceFor(io.statusObservations(), batch);
    assert forall j: nat | j < |sources| ::
        BatchStepEvidenceFor(
          sources[j],
          directory,
          cmd,
          batch.fsBounds[j],
          preCwd,
          batch.fsBounds[j + 1],
          batch.outcomes[j],
          batch.stdoutFragments[j],
          batch.stderrFragments[j],
          batch.steps[j]
        );
    PackageBatchEvidenceFor(
      sources, directory, cmd, preFs, preCwd, io.fs(),
      hadError, out, errOut, batch);
  }
}
