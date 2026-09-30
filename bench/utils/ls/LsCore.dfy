include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LsSchema.dfy"
include "LsSpec.dfy"
include "LsTime.dfy"

module LsCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Spec = LsSpec
  import Time = LsTime

  function DigitCharCore(d: nat): char
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

  function NatTextCore(n: nat): string
    decreases n
  {
    if n < 10 then [DigitCharCore(n)]
    else NatTextCore(n / 10) + [DigitCharCore(n % 10)]
  }

  function IntTextCore(n: int): string
  {
    if n < 0 then "-" + NatTextCore((-n) as nat) else NatTextCore(n as nat)
  }

  function PermissionCharCore(mode: bv32, bit: bv32, present: char): char
  {
    if (mode & bit) != 0 as bv32 then present else '-'
  }

  function ExecuteCharCore(
    mode: bv32,
    executeBit: bv32,
    specialBit: bv32,
    specialExecute: char,
    specialNoExecute: char
  ): char
  {
    if (mode & specialBit) != 0 as bv32 then
      if (mode & executeBit) != 0 as bv32 then specialExecute else specialNoExecute
    else
      PermissionCharCore(mode, executeBit, 'x')
  }

  function KindCharCore(kind: BenchWorld.FileKind): char
  {
    match kind
    case RegularKind => '-'
    case DirectoryKind => 'd'
    case SymlinkKind => 'l'
    case BlockDeviceKind => 'b'
    case CharacterDeviceKind => 'c'
    case FifoKind => 'p'
    case SocketKind => 's'
  }

  function ModeTextCore(status: BenchWorld.FileStatus): string
  {
    [KindCharCore(status.kind),
     PermissionCharCore(status.mode, 256 as bv32, 'r'),
     PermissionCharCore(status.mode, 128 as bv32, 'w'),
     ExecuteCharCore(status.mode, 64 as bv32, 2048 as bv32, 's', 'S'),
     PermissionCharCore(status.mode, 32 as bv32, 'r'),
     PermissionCharCore(status.mode, 16 as bv32, 'w'),
     ExecuteCharCore(status.mode, 8 as bv32, 1024 as bv32, 's', 'S'),
     PermissionCharCore(status.mode, 4 as bv32, 'r'),
     PermissionCharCore(status.mode, 2 as bv32, 'w'),
     ExecuteCharCore(status.mode, 1 as bv32, 512 as bv32, 't', 'T')]
  }

  function RenderEntryCore(cmd: Schema.LsCmd, displayName: string, status: BenchWorld.FileStatus): BenchWorld.Bytes
  {
    RenderAlignedEntryCore(cmd, displayName, status, Spec.ColumnWidths(0, 0, 0, 0, 0))
  }

  function RenderAlignedEntryCore(
    cmd: Schema.LsCmd,
    displayName: string,
    status: BenchWorld.FileStatus,
    widths: Spec.ColumnWidths
  ): BenchWorld.Bytes
  {
    var blockPrefix := if cmd.showBlocks then
                         Spec.PadColumn(NatTextCore(Spec.DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize)), widths.blocks, true) + " "
                       else "";
    Utf8.Encode(blockPrefix + if !cmd.numericLong then
      displayName + "\n"
    else
      ModeTextCore(status) + " " +
      Spec.PadColumn(NatTextCore(status.linkCount), widths.links, true) + " " +
      Spec.PadColumn(NatTextCore(status.ownership.uid), widths.owner, true) + " " +
      Spec.PadColumn(NatTextCore(status.ownership.gid), widths.group, true) + " " +
      Spec.PadColumn(NatTextCore(Spec.DisplayedFileSizeSpec(
                    status.storage.size, cmd.fileSizeBlockSize)), widths.size, true) + " " +
      TimeTextCore(cmd, SelectedSecondsCore(cmd, status),
                   SelectedNanosecondsCore(cmd, status)) + " " +
      displayName + "\n")
  }

  function TimeTextCore(cmd: Schema.LsCmd, seconds: int, nanoseconds: int): string
  {
    match cmd.timeStyle
    case EpochSeconds => IntTextCore(seconds)
    case FullIso => Time.FullIso(seconds, nanoseconds)
    case LongIso => Time.LongIso(seconds)
    case Iso => Time.Iso(seconds, nanoseconds, cmd.referenceNow)
    case DefaultC => Time.DefaultC(seconds, nanoseconds, cmd.referenceNow)
  }

  function AllocatedBlocksSumCore(observations: seq<Spec.EntryObservation>): nat
    decreases |observations|
  {
    if |observations| == 0 then 0
    else
      (if observations[0].ok then observations[0].status.storage.allocatedBlocks else 0) +
      AllocatedBlocksSumCore(observations[1..])
  }

  function TotalLineCore(cmd: Schema.LsCmd, observations: seq<Spec.EntryObservation>): BenchWorld.Bytes
  {
    if cmd.numericLong || cmd.showBlocks then
      Utf8.Encode("total " + NatTextCore(
        Spec.DisplayedBlocksSpec(AllocatedBlocksSumCore(observations), cmd.cliBlockSize)) + "\n")
    else
      []
  }

  opaque function StringLessFromCore(left: string, right: string, i: nat): bool
    requires i <= |left| && i <= |right|
    decreases |left| + |right| - 2 * i
  {
    if i == |left| then i < |right|
    else if i == |right| then false
    else if left[i] == right[i] then StringLessFromCore(left, right, i + 1)
    else left[i] < right[i]
  }

  opaque function StringLessCore(left: string, right: string): bool
  {
    StringLessFromCore(left, right, 0)
  }

  function SelectedSecondsCore(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeSec
    case AccessTime => status.times.atimeSec
    case ChangeTime => status.times.ctimeSec
  }

  function SelectedNanosecondsCore(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeNsec
    case AccessTime => status.times.atimeNsec
    case ChangeTime => status.times.ctimeNsec
  }

  opaque function BaseEntryBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  ): bool
  {
    if cmd.sortMode == Schema.SortSize &&
            (if left.ok then left.status.storage.size else 0) != (if right.ok then right.status.storage.size else 0) then
      (if left.ok then left.status.storage.size else 0) > (if right.ok then right.status.storage.size else 0)
    else if cmd.sortMode == Schema.SortTime &&
            (if left.ok then SelectedSecondsCore(cmd, left.status) else 0) != (if right.ok then SelectedSecondsCore(cmd, right.status) else 0) then
      (if left.ok then SelectedSecondsCore(cmd, left.status) else 0) > (if right.ok then SelectedSecondsCore(cmd, right.status) else 0)
    else if cmd.sortMode == Schema.SortTime &&
            (if left.ok then SelectedNanosecondsCore(cmd, left.status) else 0) != (if right.ok then SelectedNanosecondsCore(cmd, right.status) else 0) then
      (if left.ok then SelectedNanosecondsCore(cmd, left.status) else 0) > (if right.ok then SelectedNanosecondsCore(cmd, right.status) else 0)
    else
      StringLessCore(left.displayName, right.displayName)
  }

  opaque function EntryBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  ): bool
  {
    if cmd.reverse then BaseEntryBeforeCore(cmd, right, left)
    else BaseEntryBeforeCore(cmd, left, right)
  }

  opaque function InsertSortedCore(
    cmd: Schema.LsCmd,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  ): seq<Spec.EntryObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [entry]
    else if EntryBeforeCore(cmd, entry, sorted[0]) then [entry] + sorted
    else [sorted[0]] + InsertSortedCore(cmd, entry, sorted[1..])
  }

  opaque function SortEntriesCore(
    cmd: Schema.LsCmd,
    entries: seq<Spec.EntryObservation>
  ): seq<Spec.EntryObservation>
    decreases |entries|
  {
    if |entries| == 0 then []
    else InsertSortedCore(cmd, entries[0], SortEntriesCore(cmd, entries[1..]))
  }

  opaque function OperandBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.OperandObservation,
    right: Spec.OperandObservation
  ): bool
  {
    if left.operandClass != right.operandClass then
      Spec.OperandClassRank(left.operandClass) <
      Spec.OperandClassRank(right.operandClass)
    else
      EntryBeforeCore(cmd, Spec.OperandAsEntry(left), Spec.OperandAsEntry(right))
  }

  opaque function InsertOperandSortedCore(
    cmd: Schema.LsCmd,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OperandObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [observation]
    else if OperandBeforeCore(cmd, observation, sorted[0]) then
      [observation] + sorted
    else
      [sorted[0]] + InsertOperandSortedCore(cmd, observation, sorted[1..])
  }

  opaque function SortOperandsCore(
    cmd: Schema.LsCmd,
    observations: seq<Spec.OperandObservation>
  ): seq<Spec.OperandObservation>
    decreases |observations|
  {
    if |observations| == 0 then []
    else InsertOperandSortedCore(
           cmd, observations[0], SortOperandsCore(cmd, observations[1..]))
  }

  function DirectPositionsCore(
    sorted: seq<Spec.OperandObservation>, i: nat
  ): seq<nat>
    requires i <= |sorted|
    ensures forall k: nat :: k < |DirectPositionsCore(sorted, i)| ==>
                               DirectPositionsCore(sorted, i)[k] < |sorted|
    decreases |sorted| - i
  {
    if i == |sorted| then []
    else ((if sorted[i].operandClass == Spec.DirectOperand then [i] else []) +
          DirectPositionsCore(sorted, i + 1))
  }

  function DirectoryPositionsCore(
    sorted: seq<Spec.OperandObservation>, i: nat
  ): seq<nat>
    requires i <= |sorted|
    ensures forall k: nat :: k < |DirectoryPositionsCore(sorted, i)| ==>
                               DirectoryPositionsCore(sorted, i)[k] < |sorted|
    decreases |sorted| - i
  {
    if i == |sorted| then []
    else
      (if sorted[i].operandClass == Spec.ExpandedDirectory &&
          sorted[i].sectionAvailable then [i] else []) +
      DirectoryPositionsCore(sorted, i + 1)
  }

  function RenderOperandCore(cmd: Schema.LsCmd, observations: seq<Spec.OperandObservation>, index: nat): BenchWorld.Bytes
    requires index < |observations|
  {
    RenderAlignedEntryCore(cmd, observations[index].renderName, observations[index].status,
                          Spec.OperandWidthsSpec(cmd, observations))
  }

  function BodiesAtPositionsCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>
  ): BenchWorld.Bytes
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
  {
    BodiesAtPositionsPrefixCore(cmd, sorted, positions, |positions|)
  }

  function BodiesFragmentsPrefixCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |BodiesFragmentsPrefixCore(cmd, sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               BodiesFragmentsPrefixCore(cmd, sorted, positions, processed)[k] ==
                               RenderOperandCore(cmd, sorted, positions[k])
    decreases processed
  {
    if processed == 0 then []
    else (BodiesFragmentsPrefixCore(cmd, sorted, positions, processed - 1) +
          [RenderOperandCore(cmd, sorted, positions[processed - 1])])
  }

  function OperandIndicesPrefixCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<nat>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |OperandIndicesPrefixCore(sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               OperandIndicesPrefixCore(sorted, positions, processed)[k] ==
                               sorted[positions[k]].index
    decreases processed
  {
    if processed == 0 then []
    else (OperandIndicesPrefixCore(sorted, positions, processed - 1) +
          [sorted[positions[processed - 1]].index])
  }

  function BodiesAtPositionsPrefixCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    decreases processed
  {
    if processed == 0 then []
    else (BodiesAtPositionsPrefixCore(cmd, sorted, positions, processed - 1) +
          RenderOperandCore(cmd, sorted, positions[processed - 1]))
  }

  function DirectoryGroupsCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>
  ): seq<Spec.OutputGroup>
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
  {
    DirectoryGroupsPrefixCore(sorted, positions, |positions|)
  }

  function DirectoryGroupsPrefixCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<Spec.OutputGroup>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    decreases processed
  {
    if processed == 0 then []
    else (DirectoryGroupsPrefixCore(sorted, positions, processed - 1) +
          [Spec.OutputGroup(
             [sorted[positions[processed - 1]].index],
             sorted[positions[processed - 1]].body, true)])
  }

  function HasQueuedDirectoryCore(sorted: seq<Spec.OperandObservation>): bool
  {
    exists i: nat :: i < |sorted| && sorted[i].operandClass == Spec.ExpandedDirectory
  }

  function OutputGroupsCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OutputGroup>
  {
    var directPositions := DirectPositionsCore(sorted, 0);
    var directoryPositions := DirectoryPositionsCore(sorted, 0);
    (if |directPositions| == 0 then []
     else [Spec.OutputGroup(
             OperandIndicesPrefixCore(sorted, directPositions, |directPositions|),
             BodiesAtPositionsCore(cmd, sorted, directPositions) +
               (if |directoryPositions| == 0 && HasQueuedDirectoryCore(sorted)
                then "\n" else []), false)]) +
    DirectoryGroupsCore(sorted, directoryPositions)
  }

  function JoinOutputGroupsCore(groups: seq<Spec.OutputGroup>): BenchWorld.Bytes
  {
    JoinOutputGroupsPrefixCore(groups, |groups|)
  }

  function GroupFragmentsPrefixCore(
    groups: seq<Spec.OutputGroup>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |groups|
    ensures |GroupFragmentsPrefixCore(groups, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               GroupFragmentsPrefixCore(groups, processed)[i] ==
                               (if i == 0 then [] else "\n") + groups[i].body
    decreases processed
  {
    if processed == 0 then []
    else (GroupFragmentsPrefixCore(groups, processed - 1) +
          [(if processed == 1 then [] else "\n") + groups[processed - 1].body])
  }

  function JoinOutputGroupsPrefixCore(
    groups: seq<Spec.OutputGroup>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |groups|
    decreases processed
  {
    if processed == 0 then []
    else (JoinOutputGroupsPrefixCore(groups, processed - 1) +
          (if processed == 1 then [] else "\n") + groups[processed - 1].body)
  }

  function AccessErrorsCore(
    observations: seq<Spec.OperandObservation>
  ): BenchWorld.Bytes
  {
    AccessErrorsPrefixCore(observations, |observations|)
  }

  function AccessErrorFragmentsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |observations|
    ensures |AccessErrorFragmentsPrefixCore(observations, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               AccessErrorFragmentsPrefixCore(observations, processed)[i] ==
                               observations[i].accessErrors
    decreases processed
  {
    if processed == 0 then []
    else (AccessErrorFragmentsPrefixCore(observations, processed - 1) +
          [observations[processed - 1].accessErrors])
  }

  function AccessErrorsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (AccessErrorsPrefixCore(observations, processed - 1) +
          observations[processed - 1].accessErrors)
  }

  function SectionErrorsCore(
    observations: seq<Spec.OperandObservation>
  ): BenchWorld.Bytes
  {
    SectionErrorsPrefixCore(observations, |observations|)
  }

  function SectionErrorFragmentsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |observations|
    ensures |SectionErrorFragmentsPrefixCore(observations, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               SectionErrorFragmentsPrefixCore(observations, processed)[i] ==
                               observations[i].sectionErrors
    decreases processed
  {
    if processed == 0 then []
    else (SectionErrorFragmentsPrefixCore(observations, processed - 1) +
          [observations[processed - 1].sectionErrors])
  }

  function SectionErrorsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (SectionErrorsPrefixCore(observations, processed - 1) +
          observations[processed - 1].sectionErrors)
  }

  ghost predicate RawObservationPiecesSummary(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    |errorFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then RenderEntryCore(cmd, observations[i].renderName, observations[i].status)
       else []) &&
      errorFragments[i] ==
      (if observations[i].ok
       then []
       else Spec.AccessErrorMessageSpec(observations[i].displayName, observations[i].err))
  }

  ghost predicate ObservationPiecesSummary(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then RenderAlignedEntryCore(cmd, observations[i].renderName, observations[i].status, Spec.ObservationWidthsSpec(cmd, observations))
       else Spec.RenderFailedEntrySpec(cmd, observations[i], Spec.ObservationWidthsSpec(cmd, observations)))
  }

  ghost opaque predicate DirectoryListingSummary(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    observations: seq<Spec.EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists rawObservations: seq<Spec.EntryObservation>,
      outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
      entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes ::
      Spec.DirectoryObservationRelation(cmd, fs, path, firstStatus, afterStatus,
                                        readErr == 0, rawObservations) &&
      observations == SortEntriesCore(cmd, rawObservations) &&
      ObservationPiecesSummary(cmd, observations, outputFragments) &&
      Spec.ObservationErrorsRelation(displayPath, rawObservations, errorFragments) &&
      Spec.FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == TotalLineCore(cmd, rawObservations) + entryOutput &&
      Spec.FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(path, readErr)) &&
      hadError == (readErr != 0 ||
                   exists i: nat :: i < |observations| && !observations[i].ok)
  }

  function RecursiveChildOutputPrefixCore(
    observations: seq<Spec.EntryObservation>,
    children: map<nat, Spec.RecursiveWitness>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (RecursiveChildOutputPrefixCore(
            observations, children, processed - 1) +
          (if processed - 1 in children &&
              Spec.RecursiveNodeListed(children[processed - 1])
           then "\n" + children[processed - 1].output
           else []))
  }

  function RecursiveChildErrorPrefixCore(
    displayPath: BenchWorld.Path, observations: seq<Spec.EntryObservation>,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (RecursiveChildErrorPrefixCore(
            displayPath, observations, children, cycles, processed - 1) +
          (if processed - 1 in cycles then
             Spec.RecursiveCycleMessageSpec(
               Spec.ChildDisplayPath(
                 displayPath, observations[processed - 1].displayName))
           else if processed - 1 in children
           then children[processed - 1].errors
           else []))
  }

  ghost opaque predicate RecursiveDirectorySummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: Spec.RecursiveWitness
  )
    decreases tree
  {
    cmd.statusContext.BoundStatusObservations? &&
    tree.openOk == (IOContract.OpenDirFailureErrFields(fs, accessPath) == 0) &&
    (if !tree.openOk then
       tree.openErr == IOContract.OpenDirFailureErrFields(fs, accessPath) &&
       tree.openErr > 0 && !tree.statusOk && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus &&
       tree.listingAfterStatus == tree.firstStatus &&
       tree.afterStatus == tree.firstStatus &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == Spec.OpenDirectoryErrorMessageSpec(displayPath, tree.openErr) &&
       tree.hadError
     else if !tree.statusOk then
       tree.openErr == 0 && tree.statusErr > 0 && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus &&
       tree.listingAfterStatus == tree.firstStatus &&
       tree.afterStatus == tree.firstStatus &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == Spec.DirectoryIdentityErrorMessageSpec(displayPath, tree.statusErr) &&
       tree.hadError
     else
       tree.openErr == 0 && tree.statusErr == 0 &&
       tree.listingFirstStatus == tree.firstStatus + 1 &&
       (exists resolved: BenchWorld.Path ::
         IOContract.ResolvePathForMetadataFields(fs, accessPath, true) == BenchWorld.Ok(resolved) &&
         IOContract.ObservedFileStatusContractFields(
           cmd.statusContext.observations, tree.firstStatus, fs, resolved,
           true, true, tree.openedStatus, 0)) &&
       (if tree.cycle then
          tree.openedStatus.hostKey in ancestors &&
          tree.listingAfterStatus == tree.listingFirstStatus &&
          tree.afterStatus == tree.listingFirstStatus &&
          tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
          tree.output == [] && tree.errors == Spec.RecursiveCycleMessageSpec(displayPath) &&
          tree.hadError
        else
          tree.openedStatus.hostKey !in ancestors &&
          DirectoryListingSummary(
            cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
            tree.listingAfterStatus,
            tree.observations, tree.readErr,
            tree.listingOutput, tree.listingErrors, tree.listingHadError) &&
          (exists statusCuts: seq<nat> ::
            |statusCuts| == |tree.observations| + 1 &&
            statusCuts[0] == tree.listingAfterStatus &&
            statusCuts[|tree.observations|] == tree.afterStatus &&
            (forall i: nat | i < |tree.observations| ::
              (if i in tree.children then
                 tree.children[i].firstStatus == statusCuts[i] &&
                 tree.children[i].afterStatus == statusCuts[i + 1]
               else statusCuts[i] == statusCuts[i + 1]))) &&
          tree.cycles <= tree.children.Keys &&
          (forall i: nat :: i < |tree.observations| ==>
            (i in tree.children <==> Spec.RecursiveEntryEligible(tree.observations[i])) &&
            (i in tree.cycles <==> i in tree.children && tree.children[i].cycle)) &&
          (forall i: nat :: i in tree.children ==>
            i < |tree.observations| &&
            RecursiveDirectorySummary(
              cmd, fs,
              Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
              tree.observations[i].accessPath,
              ancestors + {tree.openedStatus.hostKey}, tree.children[i])) &&
          tree.output == Spec.DirectoryHeaderSpec(displayPath) + tree.listingOutput +
            RecursiveChildOutputPrefixCore(
              tree.observations, tree.children, |tree.observations|) &&
          tree.errors == tree.listingErrors + RecursiveChildErrorPrefixCore(
            displayPath, tree.observations, tree.children, tree.cycles,
            |tree.observations|) &&
          tree.hadError ==
            (tree.listingHadError ||
             exists i: nat :: i in tree.children && tree.children[i].hadError)))
  }

  ghost opaque predicate OperandObservationSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: Spec.OperandObservation
  )
  {
    observation.index < |cmd.operands| &&
    observation.operand == cmd.operands[observation.index] &&
    observation.path == Spec.MakeAbsoluteSpec(cwd, observation.operand) &&
    observation.sectionAvailable ==
    (observation.operandClass == Spec.ExpandedDirectory &&
     IOContract.OpenDirFailureErrFields(fs, observation.path) == 0) &&
    match Spec.OperandStatusResultSpec(cmd, fs, observation.path, observation.firstStatus)
    case Err(error) =>
      !observation.ok &&
      observation.err == IOContract.IOErrorErrno(error) &&
      observation.operandClass == Spec.AccessFailure &&
      observation.afterStatus == observation.firstStatus +
        Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                        observation.firstStatus) &&
      observation.body == [] &&
      observation.accessErrors == Spec.AccessErrorMessageSpec(
        observation.operand, observation.err) &&
      observation.sectionErrors == [] && observation.failed && !observation.hasCycle
    case Ok(status) =>
      observation.ok && observation.status == status && observation.err == 0 &&
      observation.accessErrors == [] &&
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories then
        observation.operandClass == Spec.ExpandedDirectory &&
        if observation.sectionAvailable then
          if cmd.recursive then
            exists tree: Spec.RecursiveWitness ::
              RecursiveDirectorySummary(
                cmd, fs, observation.operand, observation.path,
                {}, tree) &&
              tree.firstStatus == observation.firstStatus +
                Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                                observation.firstStatus) &&
              tree.afterStatus == observation.afterStatus &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError &&
              observation.hasCycle == Spec.RecursiveHasCycle(tree)
          else
            !observation.hasCycle &&
            exists entries: seq<Spec.EntryObservation>, readErr: int,
              listingOutput: BenchWorld.Bytes
              {:trigger DirectoryListingSummary(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + Spec.OperandStatusCallCountSpec(
                  cmd, fs, observation.path, observation.firstStatus),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed)} ::
              DirectoryListingSummary(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + Spec.OperandStatusCallCountSpec(
                  cmd, fs, observation.path, observation.firstStatus),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed) &&
              observation.body ==
              (if |cmd.operands| > 1
               then Spec.DirectoryHeaderSpec(observation.operand)
               else []) + listingOutput
        else
          observation.afterStatus == observation.firstStatus +
            Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                            observation.firstStatus) &&
          observation.body == [] &&
          observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
            observation.operand,
            IOContract.OpenDirFailureErrFields(fs, observation.path)) &&
          observation.failed && !observation.hasCycle
      else
        observation.operandClass == Spec.DirectOperand &&
        observation.afterStatus == observation.firstStatus +
          Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                          observation.firstStatus) &&
        !observation.sectionAvailable &&
        observation.renderName == Spec.RenderNameSpec(
            fs, observation.operand, observation.path,
            Spec.ExplicitCommandLineFollowSpec(cmd), cmd.numericLong, status) &&
        observation.body == RenderEntryCore(cmd, observation.renderName, status) &&
        observation.sectionErrors == [] && !observation.failed && !observation.hasCycle
  }

  lemma ExpandedRecursiveOperandSummary(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    observation: Spec.OperandObservation, tree: Spec.RecursiveWitness
  )
    requires observation.index < |cmd.operands|
    requires observation.operand == cmd.operands[observation.index]
    requires observation.path == Spec.MakeAbsoluteSpec(cwd, observation.operand)
    requires observation.ok && observation.err == 0 &&
             observation.operandClass == Spec.ExpandedDirectory
    requires observation.status.kind == BenchWorld.DirectoryKind &&
             !cmd.listDirectories && cmd.recursive
    requires observation.accessErrors == []
    requires observation.sectionAvailable ==
             (IOContract.OpenDirFailureErrFields(fs, observation.path) == 0)
    requires Spec.OperandStatusResultSpec(
               cmd, fs, observation.path, observation.firstStatus) ==
             BenchWorld.Ok(observation.status)
    requires if observation.sectionAvailable then
      RecursiveDirectorySummary(
        cmd, fs, observation.operand, observation.path,
        {}, tree) &&
      tree.firstStatus == observation.firstStatus +
        Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                        observation.firstStatus) &&
      tree.afterStatus == observation.afterStatus &&
      observation.body == tree.output &&
      observation.sectionErrors == tree.errors &&
      observation.failed == tree.hadError &&
              observation.hasCycle == Spec.RecursiveHasCycle(tree)
    else
      observation.afterStatus == observation.firstStatus +
        Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                        observation.firstStatus) &&
      observation.body == [] &&
      observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
        observation.operand, IOContract.OpenDirFailureErrFields(fs, observation.path)) &&
      observation.failed && !observation.hasCycle
    ensures OperandObservationSummary(cmd, fs, cwd, observation)
  {
    reveal OperandObservationSummary();
  }

  lemma ExpandedFlatOperandSummary(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    observation: Spec.OperandObservation,
    entries: seq<Spec.EntryObservation>, readErr: int,
    listingOutput: BenchWorld.Bytes
  )
    requires observation.index < |cmd.operands|
    requires observation.operand == cmd.operands[observation.index]
    requires observation.path == Spec.MakeAbsoluteSpec(cwd, observation.operand)
    requires observation.ok && observation.err == 0 &&
             observation.operandClass == Spec.ExpandedDirectory
    requires observation.status.kind == BenchWorld.DirectoryKind &&
             !cmd.listDirectories && !cmd.recursive
    requires observation.accessErrors == []
    requires observation.sectionAvailable ==
             (IOContract.OpenDirFailureErrFields(fs, observation.path) == 0)
    requires Spec.OperandStatusResultSpec(
               cmd, fs, observation.path, observation.firstStatus) ==
             BenchWorld.Ok(observation.status)
    requires !observation.hasCycle
    requires if observation.sectionAvailable then
      DirectoryListingSummary(
        cmd, observation.operand, fs, observation.path,
        observation.firstStatus + Spec.OperandStatusCallCountSpec(
          cmd, fs, observation.path, observation.firstStatus),
        observation.afterStatus, entries, readErr,
        listingOutput, observation.sectionErrors, observation.failed) &&
      observation.body ==
        (if |cmd.operands| > 1 then Spec.DirectoryHeaderSpec(observation.operand)
         else []) + listingOutput
    else
      observation.afterStatus == observation.firstStatus +
        Spec.OperandStatusCallCountSpec(cmd, fs, observation.path,
                                        observation.firstStatus) &&
      observation.body == [] &&
      observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
        observation.operand, IOContract.OpenDirFailureErrFields(fs, observation.path)) &&
      observation.failed && !observation.hasCycle
    ensures OperandObservationSummary(cmd, fs, cwd, observation)
  {
    reveal OperandObservationSummary();
  }

  ghost predicate RunSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
  {
    exists observations: seq<Spec.OperandObservation>,
      sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup>,
      statusCuts: seq<nat> ::
      |observations| == |cmd.operands| &&
      |statusCuts| == |observations| + 1 &&
      statusCuts[0] == firstStatus &&
      statusCuts[|observations|] == afterStatus &&
      (forall i: nat | i < |observations| ::
        observations[i].firstStatus == statusCuts[i] &&
        observations[i].afterStatus == statusCuts[i + 1]) &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         OperandObservationSummary(cmd, fs, cwd, observations[i])) &&
      sorted == SortOperandsCore(cmd, observations) &&
      groups == OutputGroupsCore(cmd, sorted) &&
      output == JoinOutputGroupsCore(groups) &&
      errors == AccessErrorsCore(observations) + SectionErrorsCore(sorted) &&
      exit == Spec.OperandExitSpec(observations)
  }

  opaque twostate predicate CoreSummary(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.cwdRegion, io.envRegion, io.nowRegion,
          io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := Schema.WithStatusObservations(
      Spec.EffectiveCommandSpec(raw, old(io.env()), old(io.now())),
      io.statusObservations(), old(io.statusCursor()));
    (cmd.mode != Schema.ModeRun ==> io.statusCursor() == old(io.statusCursor())) &&
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode != Schema.ModeRun then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidModeMessageSpec(cmd.mode) &&
      exit == (if cmd.mode.ModeInvalidTime? then 1 else 2)
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunSummary(cmd, old(io.fs()), old(io.cwd()), old(io.statusCursor()),
                   io.statusCursor(), output, errors, exit) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors
  }

  lemma AppendFragment(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>,
    tail: BenchWorld.Bytes
  )
    requires Spec.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              fragments + [tail], combined + tail, cuts + [|combined + tail|])
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger (cuts + [|combined + tail|])[i]} |
      i < |fragments + [tail]|
      ensures (cuts + [|combined + tail|])[i] <=
              (cuts + [|combined + tail|])[i + 1] <= |combined + tail| &&
              (cuts + [|combined + tail|])[i + 1] ==
              (cuts + [|combined + tail|])[i] + |(fragments + [tail])[i]| &&
              (combined + tail)[
              (cuts + [|combined + tail|])[i]..
              (cuts + [|combined + tail|])[i + 1]
              ] == (fragments + [tail])[i]
    {
    }
  }

  lemma FailedOperandSnoc(
    observations: seq<Spec.OperandObservation>,
    observation: Spec.OperandObservation
  )
    ensures (exists j: nat ::
               j < |observations + [observation]| &&
               (observations + [observation])[j].failed) ==
            ((exists j: nat :: j < |observations| && observations[j].failed) ||
             observation.failed)
  {
    if exists j: nat ::
        j < |observations + [observation]| &&
        (observations + [observation])[j].failed {
      var j: nat :|
        j < |observations + [observation]| &&
        (observations + [observation])[j].failed;
      if j < |observations| {
        assert exists k: nat :: k < |observations| && observations[k].failed;
      } else {
        assert j == |observations|;
      }
    }
    if exists j: nat :: j < |observations| && observations[j].failed {
      var j: nat :| j < |observations| && observations[j].failed;
      assert (observations + [observation])[j] == observations[j];
    } else if observation.failed {
      assert (observations + [observation])[|observations|] == observation;
    }
  }

  method OperandExitCore(observations: seq<Spec.OperandObservation>) returns (exit: nat)
    ensures exit == Spec.OperandExitSpec(observations)
  {
    exit := 0;
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant forall j: nat | j < i :: Spec.OperandFailureExitSpec(observations[j]) <= exit
      invariant exit == 0 || exists j: nat :: j < i && Spec.OperandFailureExitSpec(observations[j]) == exit
      decreases |observations| - i
    {
      var severity := Spec.OperandFailureExitSpec(observations[i]);
      if severity > exit { exit := severity; }
      i := i + 1;
    }
    var values := set j: nat | j < |observations| :: Spec.OperandFailureExitSpec(observations[j]);
    var maximum := Spec.MaximumWidth(values);
    if values != {} {
      assert maximum in values;
      assert maximum <= exit;
      if exit != 0 { assert exit in values; }
      assert exit <= maximum;
    } else {
      if exit != 0 {
        ghost var j: nat :| j < |observations| && Spec.OperandFailureExitSpec(observations[j]) == exit;
        assert exit in values;
      }
      assert exit == 0;
    }
    assert exit == maximum;
    assert Spec.OperandExitSpec(observations) == maximum;
  }

  method ObservePath(
    cmd: Schema.LsCmd,
    displayName: string,
    entryKind: BenchWorld.DirectoryEntryKind,
    path: BenchWorld.Path,
    followSymlink: bool,
    io: BenchIO.IO
  ) returns (
      observation: Spec.EntryObservation,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool
    )
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    modifies io.statusObservationsRegion
    ensures Spec.MetadataObservationRelation(cmd, old(io.fs()), observation)
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal)
    ensures io.statusCursor() == old(io.statusCursor()) + 1
    ensures output ==
            (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    ensures errors ==
            (if observation.ok then [] else Spec.AccessErrorMessageSpec(displayName, observation.err))
    ensures hadError == !observation.ok
    ensures observation.entryKind == entryKind
    ensures observation.displayName == displayName
    ensures observation.accessPath == path
    ensures observation.followSymlink == followSymlink
  {
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    var ok, status, err := io.GetFileStatus(path, followSymlink);
    var renderName := displayName;
    if ok && status.kind == BenchWorld.SymlinkKind && !followSymlink && cmd.numericLong {
      var linkResult := io.ReadLink(path);
      match linkResult
      case Ok(target) => renderName := displayName + " -> " + target;
      case Err(_) =>
    }
    observation := Spec.EntryObservation(
      displayName, renderName, path, followSymlink, ok, status, err, entryKind,
      preStatus, Spec.StatusEntryEvidence(preStatus));
    if ok {
      output := RenderEntryCore(cmd, renderName, status);
      errors := [];
      hadError := false;
    } else {
      output := [];
      errors := Spec.AccessErrorMessageSpec(displayName, err);
      hadError := true;
    }
    reveal IOContract.ObservedFileStatusContractFields();
    reveal Spec.MetadataObservationRelation();
  }

  method ObserveDirectoryEntry(
    cmd: Schema.LsCmd, name: string, path: BenchWorld.Path,
    kind: BenchWorld.DirectoryEntryKind, ghost entry: BenchWorld.DirEntry,
    io: BenchIO.IO
  ) returns (observation: Spec.EntryObservation, output: BenchWorld.Bytes,
             errors: BenchWorld.Bytes, hadError: bool)
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires entry.name == name
    requires IOContract.DirectoryEntryKindMatchesEntry(kind, entry)
    modifies io.statusObservationsRegion
    ensures observation.displayName == name && observation.accessPath == path
    ensures observation.entryKind == kind
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + Spec.EntryStatusCallCount(observation)
    ensures if Spec.EntryStatusRequiredSpec(cmd, Spec.ClassifiedDirentKindSpec(kind), name) then
      observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal) &&
      Spec.MetadataObservationRelation(cmd, old(io.fs()), observation) &&
      observation.followSymlink ==
        (cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd))
    else
      observation.source == Spec.DirentEntryEvidence(entry, Spec.ClassifiedDirentKindSpec(kind)) &&
      Spec.DirentKindMatchesEntrySpec(Spec.ClassifiedDirentKindSpec(kind), entry) &&
      Spec.CanonicalDirentFields(observation)
    ensures output == (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    ensures errors == (if observation.ok then [] else Spec.AccessErrorMessageSpec(name, observation.err))
    ensures hadError == !observation.ok
  {
    if Spec.EntryStatusRequiredSpec(cmd, Spec.ClassifiedDirentKindSpec(kind), name) {
      observation, output, errors, hadError := ObservePath(
        cmd, name, kind, path,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
    } else {
      observation := Spec.EntryObservation(
        name, name, path, false, true, BenchWorld.DEFAULT_FILE_STATUS, 0, kind,
        io.statusCursor(), Spec.DirentEntryEvidence(entry, Spec.ClassifiedDirentKindSpec(kind)));
      output := RenderEntryCore(cmd, name, BenchWorld.DEFAULT_FILE_STATUS);
      errors := [];
      hadError := false;
    }
  }

  method ObserveDotEntry(
    cmd: Schema.LsCmd, name: string, path: BenchWorld.Path, io: BenchIO.IO
  ) returns (observation: Spec.EntryObservation, output: BenchWorld.Bytes,
             errors: BenchWorld.Bytes, hadError: bool)
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires name == "." || name == ".."
    modifies io.statusObservationsRegion
    ensures observation.displayName == name && observation.accessPath == path
    ensures observation.entryKind == BenchWorld.DirectoryDirentKind
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + Spec.EntryStatusCallCount(observation)
    ensures if Spec.EntryRenderSortMetadataRequiredSpec(cmd) then
      observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal) &&
      Spec.MetadataObservationRelation(cmd, old(io.fs()), observation) &&
      observation.followSymlink ==
        (cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd))
    else observation.source == Spec.ImpliedDotEntryEvidence && Spec.CanonicalDirentFields(observation)
    ensures output == (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    ensures errors == (if observation.ok then [] else Spec.AccessErrorMessageSpec(name, observation.err))
    ensures hadError == !observation.ok
  {
    if Spec.EntryRenderSortMetadataRequiredSpec(cmd) {
      observation, output, errors, hadError := ObservePath(
        cmd, name, BenchWorld.DirectoryDirentKind, path,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
    } else {
      observation := Spec.EntryObservation(
        name, name, path, false, true, BenchWorld.DEFAULT_FILE_STATUS, 0,
        BenchWorld.DirectoryDirentKind, io.statusCursor(), Spec.ImpliedDotEntryEvidence);
      output := RenderEntryCore(cmd, name, BenchWorld.DEFAULT_FILE_STATUS);
      errors := [];
      hadError := false;
    }
  }

  method AddObservation(
    cmd: Schema.LsCmd,
    observation: Spec.EntryObservation,
    piece: BenchWorld.Bytes,
    errorPiece: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>,
    output: BenchWorld.Bytes,
    errorFragments: seq<BenchWorld.Bytes>,
    errorCuts: seq<nat>,
    errors: BenchWorld.Bytes
  ) returns (
      observations2: seq<Spec.EntryObservation>,
      outputFragments2: seq<BenchWorld.Bytes>,
      outputCuts2: seq<nat>,
      output2: BenchWorld.Bytes,
      errorFragments2: seq<BenchWorld.Bytes>,
      errorCuts2: seq<nat>,
      errors2: BenchWorld.Bytes
    )
    requires RawObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
    requires Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    requires Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    requires piece ==
             (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    requires errorPiece ==
             (if observation.ok then [] else Spec.AccessErrorMessageSpec(observation.displayName, observation.err))
    ensures observations2 == observations + [observation]
    ensures RawObservationPiecesSummary(cmd, observations2, outputFragments2, errorFragments2)
    ensures Spec.FragmentsConcatenate(outputFragments2, output2, outputCuts2)
    ensures Spec.FragmentsConcatenate(errorFragments2, errors2, errorCuts2)
  {
    AppendFragment(outputFragments, output, outputCuts, piece);
    AppendFragment(errorFragments, errors, errorCuts, errorPiece);
    observations2 := observations + [observation];
    outputFragments2 := outputFragments + [piece];
    outputCuts2 := outputCuts + [|output + piece|];
    output2 := output + piece;
    errorFragments2 := errorFragments + [errorPiece];
    errorCuts2 := errorCuts + [|errors + errorPiece|];
    errors2 := errors + errorPiece;
  }

  method ContainsDisplayName(
    observations: seq<Spec.EntryObservation>,
    name: string
  ) returns (found: bool)
    ensures found == (exists i: nat :: i < |observations| && observations[i].displayName == name)
  {
    found := false;
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant found ==
                (exists j: nat :: j < i && observations[j].displayName == name)
      decreases |observations| - i
    {
      if observations[i].displayName == name {
        found := true;
      }
      i := i + 1;
    }
  }

  lemma DistinctEmpty()
    ensures Spec.DistinctDisplayNames([])
  {
    reveal Spec.DistinctDisplayNames();
  }

  lemma DistinctSnoc(
    observations: seq<Spec.EntryObservation>,
    observation: Spec.EntryObservation
  )
    requires Spec.DistinctDisplayNames(observations)
    requires !(exists i: nat ::
                 i < |observations| && observations[i].displayName == observation.displayName)
    ensures Spec.DistinctDisplayNames(observations + [observation])
  {
    reveal Spec.DistinctDisplayNames();
    assert (observations + [observation])[..|observations|] == observations;
    assert forall i: nat :: i < |observations| ==>
                              observations[i].displayName != observation.displayName by {
      forall i: nat | i < |observations|
        ensures observations[i].displayName != observation.displayName
      {
        assert !(exists k: nat ::
                   k < |observations| && observations[k].displayName == observation.displayName);
      }
    }
  }

  ghost opaque predicate ProcessedCoverage(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    remaining: set<BenchWorld.DirEntry>,
    observations: seq<Spec.EntryObservation>
  )
  {
    forall entry: BenchWorld.DirEntry ::
      entry in expected - remaining && Spec.VisibleNameSpec(cmd, entry.name) ==>
        exists i: nat :: i < |observations| && observations[i].displayName == entry.name
  }

  lemma ProcessedCoverageInit(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    observations: seq<Spec.EntryObservation>
  )
    ensures ProcessedCoverage(cmd, expected, expected, observations)
  {
    reveal ProcessedCoverage();
  }

  lemma ProcessedCoverageRemove(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    beforeRemaining: set<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry,
    before: seq<Spec.EntryObservation>,
    after: seq<Spec.EntryObservation>
  )
    requires ProcessedCoverage(cmd, expected, beforeRemaining, before)
    requires entry in beforeRemaining
    requires |before| <= |after| && after[..|before|] == before
    requires Spec.VisibleNameSpec(cmd, entry.name) ==>
               exists i: nat :: i < |after| && after[i].displayName == entry.name
    ensures ProcessedCoverage(cmd, expected, beforeRemaining - {entry}, after)
  {
    reveal ProcessedCoverage();
    forall candidate: BenchWorld.DirEntry |
      candidate in expected - (beforeRemaining - {entry}) &&
      Spec.VisibleNameSpec(cmd, candidate.name)
      ensures exists i: nat :: i < |after| && after[i].displayName == candidate.name
    {
      if candidate != entry {
        assert candidate in expected - beforeRemaining;
        var i: nat :| i < |before| && before[i].displayName == candidate.name;
        assert after[i] == before[i];
      }
    }
  }

  ghost predicate DirectoryStatusCuts(
    observations: seq<Spec.EntryObservation>, cuts: seq<nat>, firstStatus: nat, afterStatus: nat
  )
  {
    |cuts| == |observations| + 1 && cuts[0] == firstStatus &&
    cuts[|observations|] == afterStatus &&
    forall i: nat | i < |observations| ::
      observations[i].statusOrdinal == cuts[i] &&
      cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i])
  }

  lemma DirectoryStatusCutsSnoc(
    observations: seq<Spec.EntryObservation>, cuts: seq<nat>,
    firstStatus: nat, beforeStatus: nat, afterStatus: nat, observation: Spec.EntryObservation
  )
    requires DirectoryStatusCuts(observations, cuts, firstStatus, beforeStatus)
    requires observation.statusOrdinal == beforeStatus
    requires afterStatus == beforeStatus + Spec.EntryStatusCallCount(observation)
    ensures DirectoryStatusCuts(observations + [observation], cuts + [afterStatus], firstStatus, afterStatus)
  {
    forall i: nat | i < |observations + [observation]|
      ensures (observations + [observation])[i].statusOrdinal == (cuts + [afterStatus])[i] &&
        (cuts + [afterStatus])[i + 1] == (cuts + [afterStatus])[i] +
          Spec.EntryStatusCallCount((observations + [observation])[i])
    {
      if i < |observations| { assert i + 1 < |cuts|; }
      else { assert i == |observations|; }
    }
  }

  lemma CompleteDirectoryObservations(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    resolved: BenchWorld.Path,
    expected: set<BenchWorld.DirEntry>,
    firstStatus: nat,
    afterStatus: nat,
    observations: seq<Spec.EntryObservation>,
    statusCuts: seq<nat>
  )
    requires DirectoryStatusCuts(observations, statusCuts, firstStatus, afterStatus)
    requires IOContract.ResolvePathForMetadataFields(fs, path, true) == BenchWorld.Ok(resolved)
    requires BenchWorld.FsContainsPath(fs, resolved)
    requires expected == IOContract.DirectoryEntriesIncludingDotsForPathFields(fs, resolved)
    requires Spec.DistinctDisplayNames(observations)
    requires forall i: nat :: i < |observations| ==>
                                Spec.DirectorySourceRelation(cmd, fs, path, observations[i])
    requires ProcessedCoverage(cmd, expected, {}, observations)
    ensures Spec.DirectoryObservationRelation(
              cmd, fs, path, firstStatus, afterStatus,
              true, observations)
  {

    reveal Spec.DirectoryObservationRelation();
    reveal ProcessedCoverage();
    assert BenchWorld.DirEntry(".", true, false) in expected;
    assert BenchWorld.DirEntry("..", true, false) in expected;
  }

  lemma StatusOnlyDirectoryCuts(
    observations: seq<Spec.EntryObservation>, firstStatus: nat
  )
    requires forall i: nat :: i < |observations| ==>
      observations[i].statusOrdinal == firstStatus + i &&
      observations[i].source ==
        Spec.StatusEntryEvidence(observations[i].statusOrdinal)
    ensures exists cuts: seq<nat> ::
      |cuts| == |observations| + 1 &&
      cuts[0] == firstStatus &&
      cuts[|observations|] == firstStatus + |observations| &&
      (forall i: nat | i < |observations| ::
        observations[i].statusOrdinal == cuts[i] &&
        cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]))
  {
    ghost var cuts := seq(|observations| + 1,
      i requires i < |observations| + 1 => firstStatus + i);
    assert |cuts| == |observations| + 1;
    assert cuts[0] == firstStatus;
    assert cuts[|observations|] == firstStatus + |observations|;
    assert forall i: nat | i < |observations| ::
      observations[i].statusOrdinal == cuts[i] &&
      cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]);
    assert |cuts| == |observations| + 1 &&
      cuts[0] == firstStatus &&
      cuts[|observations|] == firstStatus + |observations| &&
      (forall i: nat | i < |observations| ::
        observations[i].statusOrdinal == cuts[i] &&
        cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]));
    assert exists witnessCuts: seq<nat> ::
      |witnessCuts| == |observations| + 1 &&
      witnessCuts[0] == firstStatus &&
      witnessCuts[|observations|] == firstStatus + |observations| &&
      (forall i: nat | i < |observations| ::
        observations[i].statusOrdinal == witnessCuts[i] &&
        witnessCuts[i + 1] == witnessCuts[i] +
          Spec.EntryStatusCallCount(observations[i]));
  }

  method RenderObservationSequence(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>
  ) returns (
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool,
      ghost outputFragments: seq<BenchWorld.Bytes>,
      ghost outputCuts: seq<nat>,
      ghost errorFragments: seq<BenchWorld.Bytes>,
      ghost errorCuts: seq<nat>
    )
    ensures ObservationPiecesSummary(cmd, observations, outputFragments)
    ensures Spec.ObservationErrorsRelation(displayPath, observations, errorFragments)
    ensures Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    ensures Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    ensures hadError ==
            (exists i: nat :: i < |observations| && !observations[i].ok)
  {
    hide RenderAlignedEntryCore();
    hide Spec.RenderFailedEntrySpec();
    hide Spec.ObservationWidthsSpec();
    output := [];
    errors := [];
    hadError := false;
    outputFragments := [];
    outputCuts := [0];
    errorFragments := [];
    errorCuts := [0];
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant |outputFragments| == i
      invariant |errorFragments| == i
      invariant forall j: nat | j < i ::
        outputFragments[j] == (if observations[j].ok then
          RenderAlignedEntryCore(cmd, observations[j].renderName, observations[j].status,
                                 Spec.ObservationWidthsSpec(cmd, observations)) else Spec.RenderFailedEntrySpec(cmd, observations[j], Spec.ObservationWidthsSpec(cmd, observations))) &&
        errorFragments[j] == (if observations[j].ok then [] else
          Spec.AccessErrorMessageSpec(Spec.EntryDiagnosticPathSpec(displayPath, observations[j].displayName), observations[j].err))
      invariant Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
      invariant Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
      invariant hadError ==
                (exists j: nat :: j < i && !observations[j].ok)
      decreases |observations| - i
    {
      var observation := observations[i];
      assert (exists j: nat :: j < i + 1 && !observations[j].ok) ==
             (hadError || !observation.ok) by {
        if exists j: nat :: j < i + 1 && !observations[j].ok {
          var j: nat :| j < i + 1 && !observations[j].ok;
          if j < i {
            assert exists k: nat :: k < i && !observations[k].ok;
          }
        }
        if hadError {
          var j: nat :| j < i && !observations[j].ok;
          assert j < i + 1 && !observations[j].ok;
        } else if !observation.ok {
          assert i < i + 1 && !observations[i].ok;
        }
      }
      var piece := if observation.ok
      then RenderAlignedEntryCore(cmd, observation.renderName, observation.status, Spec.ObservationWidthsSpec(cmd, observations))
      else Spec.RenderFailedEntrySpec(cmd, observation, Spec.ObservationWidthsSpec(cmd, observations));
      var errorPiece := if observation.ok
      then []
      else Spec.AccessErrorMessageSpec(Spec.EntryDiagnosticPathSpec(displayPath, observation.displayName), observation.err);
      AppendFragment(outputFragments, output, outputCuts, piece);
      AppendFragment(errorFragments, errors, errorCuts, errorPiece);
      outputFragments := outputFragments + [piece];
      outputCuts := outputCuts + [|output + piece|];
      output := output + piece;
      errorFragments := errorFragments + [errorPiece];
      errorCuts := errorCuts + [|errors + errorPiece|];
      errors := errors + errorPiece;
      hadError := hadError || !observation.ok;
      i := i + 1;
      assert observations[..i] == observations[..i - 1] + [observations[i - 1]];
    }
  }

  method {:vcs_split_on_every_assert} ReadOpenedDirectoryCore(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    path: BenchWorld.Path,
    handle: int,
    io: BenchIO.IO
  ) returns (
      observations: seq<Spec.EntryObservation>,
      readErr: int,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool
    )
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires handle in io.dirHandles()
    requires io.dirHandles()[handle].DotDirHandleState?
    requires exists resolved: BenchWorld.Path ::
      IOContract.ResolvePathForMetadataFields(io.fs(), path, true) == BenchWorld.Ok(resolved) &&
      BenchWorld.FsContainsPath(io.fs(), resolved) &&
      io.dirHandles()[handle].path == resolved &&
      io.dirHandles()[handle].remaining ==
        IOContract.DirectoryEntriesIncludingDotsForPathFields(io.fs(), resolved)
    modifies io.dirHandlesRegion, io.statusObservationsRegion
    ensures DirectoryListingSummary(
              cmd, displayPath, old(io.fs()), path, old(io.statusCursor()), io.statusCursor(),
              observations, readErr, output, errors, hadError)
    ensures handle !in io.dirHandles()
    decreases *
  {
    hide RenderEntryCore();
    hide RenderAlignedEntryCore();
    hide Spec.RenderFailedEntrySpec();
    hide Spec.ObservationWidthsSpec();
    hide TotalLineCore();
    hide IOContract.DirectoryEntryKindMatchesFilesystemFields();
    hide Spec.DirectorySourceRelation();
    reveal DirectoryListingSummary();
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    ghost var statusCuts: seq<nat> := [preStatus];
    observations := [];
    readErr := 0;
    output := [];
    errors := [];
    hadError := false;
    var outputFragments: seq<BenchWorld.Bytes> := [];
    var outputCuts: seq<nat> := [0];
    var errorFragments: seq<BenchWorld.Bytes> := [];
    var errorCuts: seq<nat> := [0];
    assert ObservationPiecesSummary(cmd, observations, outputFragments);
    assert Spec.ObservationErrorsRelation(displayPath, observations, errorFragments);
    assert Spec.FragmentsConcatenate(outputFragments, output, outputCuts);
    assert Spec.FragmentsConcatenate(errorFragments, errors, errorCuts);
    DistinctEmpty();

    ghost var expected := io.dirHandles()[handle].remaining;
    ghost var resolved := io.dirHandles()[handle].path;
    assert IOContract.ResolvePathForMetadataFields(preFs, path, true) == BenchWorld.Ok(resolved);
    assert BenchWorld.FsContainsPath(preFs, resolved);
    assert expected == IOContract.DirectoryEntriesIncludingDotsForPathFields(preFs, resolved);

    assert DirectoryStatusCuts(observations, statusCuts, preStatus, io.statusCursor());
    var finished := false;
    assert Spec.DistinctDisplayNames(observations);
    ProcessedCoverageInit(cmd, expected, observations);
    while !finished
      invariant handle in io.dirHandles()
      invariant io.dirHandles()[handle].DotDirHandleState?
      invariant io.dirHandles()[handle].remaining <= expected
      invariant io.dirHandles()[handle].path == resolved
      invariant finished ==> io.dirHandles()[handle].remaining == {}
      invariant RawObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
      invariant Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
      invariant Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
      invariant DirectoryStatusCuts(observations, statusCuts, preStatus, io.statusCursor())
      invariant forall i: nat :: i < |observations| ==>
                                   Spec.DirectorySourceRelation(cmd, preFs, path, observations[i])
      invariant Spec.DistinctDisplayNames(observations)
      invariant ProcessedCoverage(
                  cmd, expected, io.dirHandles()[handle].remaining, observations)
      invariant readErr == 0
      decreases *
    {
      ghost var beforeHandles := io.dirHandles();
      ghost var beforeRemaining := io.dirHandles()[handle].remaining;
      ghost var beforeObservations := observations;
      ghost var visibleCovered := false;
      ghost var visibleIndex: nat := 0;
      var hasMore, name, kind, err := io.ReadDir(handle);
      reveal IOContract.ReadDirContractFields();
      ghost var entry := BenchWorld.DirEntry("", false, false);
      if hasMore {
        entry :| entry in beforeRemaining && entry.name == name &&
          io.dirHandles()[handle].remaining == beforeRemaining - {entry} &&
          IOContract.DirectoryEntryKindMatchesEntry(kind, entry);
      }
      if err != 0 {
        readErr := err;
        finished := true;
        io.CloseDir(handle);
        var rawObservations := observations;
        assert DirectoryStatusCuts(rawObservations, statusCuts, preStatus, io.statusCursor());
        assert Spec.DirectoryObservationRelation(
          cmd, preFs, path, preStatus, io.statusCursor(), false, rawObservations);
        observations := SortEntriesCore(cmd, rawObservations);
        var entryErrors: BenchWorld.Bytes;
        var renderedHadError: bool;
        ghost var renderedOutputs: seq<BenchWorld.Bytes>;
        ghost var renderedOutputCuts: seq<nat>;
        ghost var renderedErrors: seq<BenchWorld.Bytes>;
        ghost var renderedErrorCuts: seq<nat>;
        output, entryErrors, renderedHadError,
        renderedOutputs, renderedOutputCuts,
        renderedErrors, renderedErrorCuts :=
          RenderObservationSequence(cmd, displayPath, observations);
        var ignoredOutput: BenchWorld.Bytes;
        var ignoredFailure: bool;
        ghost var ignoredFragments: seq<BenchWorld.Bytes>;
        ghost var ignoredCuts: seq<nat>;
        ignoredOutput, entryErrors, ignoredFailure,
        ignoredFragments, ignoredCuts, renderedErrors, renderedErrorCuts :=
          RenderObservationSequence(cmd, displayPath, rawObservations);
        var entryOutput := output;
        output := TotalLineCore(cmd, rawObservations) + entryOutput;
        errors := entryErrors + Spec.ReadDirectoryErrorMessageSpec(path, readErr);
        hadError := true;
        assert DirectoryListingSummary(cmd, displayPath, preFs, path, preStatus, io.statusCursor(),
                                       observations, readErr, output, errors, hadError);
        return;
      }
      if !hasMore {
        assert io.dirHandles()[handle].remaining == {};
        finished := true;
      } else if Spec.VisibleNameSpec(cmd, name) {
        var alreadyObserved := ContainsDisplayName(observations, name);
        if alreadyObserved {
          visibleIndex :| visibleIndex < |observations| &&
                          observations[visibleIndex].displayName == name;
          visibleCovered := true;
        } else {
          var beforeObservation := observations;
          ghost var beforeEntryStatus := io.statusCursor();
          var childPath := BenchWorld.AppendPath(path, name);
          var observation: Spec.EntryObservation;
          var piece: BenchWorld.Bytes;
          var errorPiece: BenchWorld.Bytes;
          var failed: bool;
          if name == "." || name == ".." {
            observation, piece, errorPiece, failed := ObserveDotEntry(cmd, name, childPath, io);
          } else {
            observation, piece, errorPiece, failed := ObserveDirectoryEntry(
              cmd, name, childPath, kind, entry, io);
          }
          DirectoryStatusCutsSnoc(observations, statusCuts, preStatus, beforeEntryStatus, io.statusCursor(), observation);
          observations, outputFragments, outputCuts, output,
          errorFragments, errorCuts, errors :=
            AddObservation(
              cmd, observation, piece, errorPiece, observations,
              outputFragments, outputCuts, output,
              errorFragments, errorCuts, errors);
          statusCuts := statusCuts + [io.statusCursor()];
          DistinctSnoc(beforeObservation, observation);
          hadError := hadError || failed;
          assert Spec.DirectorySourceRelation(cmd, preFs, path, observation) by {
            reveal Spec.DirectorySourceRelation();
          }
          assert observation.displayName == name;
          visibleIndex := |beforeObservation|;
          assert observations[visibleIndex] == observation;
          visibleCovered := true;
        }
      }
      if hasMore {
        assert entry in beforeRemaining;
        assert io.dirHandles()[handle].remaining == beforeRemaining - {entry};
        assert |beforeObservations| <= |observations|;
        assert observations[..|beforeObservations|] == beforeObservations;
        if Spec.VisibleNameSpec(cmd, name) {
          assert visibleCovered;
          assert visibleIndex < |observations| &&
                 observations[visibleIndex].displayName == name;
        }
        ProcessedCoverageRemove(
          cmd, expected, beforeRemaining, entry, beforeObservations, observations);
      }
    }
    assert io.dirHandles()[handle].remaining == {};
    var rawObservations := observations;
    hide Spec.DirectoryObservationRelation();
    CompleteDirectoryObservations(
      cmd, preFs, path, resolved, expected, preStatus, io.statusCursor(), rawObservations, statusCuts);
    assert DirectoryStatusCuts(rawObservations, statusCuts, preStatus, io.statusCursor());
    assert Spec.DirectoryObservationRelation(
      cmd, preFs, path, preStatus, io.statusCursor(), true, rawObservations);
    io.CloseDir(handle);
    observations := SortEntriesCore(cmd, rawObservations);
    ghost var renderedOutputs: seq<BenchWorld.Bytes>;
    ghost var renderedOutputCuts: seq<nat>;
    ghost var renderedErrors: seq<BenchWorld.Bytes>;
    ghost var renderedErrorCuts: seq<nat>;
    output, errors, hadError,
    renderedOutputs, renderedOutputCuts,
    renderedErrors, renderedErrorCuts :=
      RenderObservationSequence(cmd, displayPath, observations);
    var ignoredOutput: BenchWorld.Bytes;
    var ignoredFailure: bool;
    ghost var ignoredFragments: seq<BenchWorld.Bytes>;
    ghost var ignoredCuts: seq<nat>;
    ignoredOutput, errors, ignoredFailure,
    ignoredFragments, ignoredCuts, renderedErrors, renderedErrorCuts :=
      RenderObservationSequence(cmd, displayPath, rawObservations);
    var entryOutput := output;
    output := TotalLineCore(cmd, rawObservations) + entryOutput;
    assert DirectoryListingSummary(cmd, displayPath, preFs, path, preStatus, io.statusCursor(),
                                   observations, readErr, output, errors, hadError);
  }

  method {:vcs_split_on_every_assert} ReadDirectoryCore(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    path: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (
      observations: seq<Spec.EntryObservation>,
      readErr: int,
      wasOpened: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool
    )
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    modifies io.dirHandlesRegion, io.statusObservationsRegion
    ensures wasOpened ==
            (IOContract.OpenDirFailureErrFields(old(io.fs()), path) == 0)
    ensures wasOpened ==> DirectoryListingSummary(
              cmd, displayPath, old(io.fs()), path,
              old(io.statusCursor()), io.statusCursor(),
              observations, readErr, output, errors, hadError)
    ensures !wasOpened ==>
              observations == [] &&
              readErr == IOContract.OpenDirFailureErrFields(old(io.fs()), path) &&
              output == [] &&
              errors == Spec.OpenDirectoryErrorMessageSpec(displayPath, readErr) &&
              hadError && io.statusCursor() == old(io.statusCursor())
    decreases *
  {
    var openOk, handle, openErr := io.OpenDir(path, true);
    reveal IOContract.OpenDirContractFields();
    wasOpened := openOk;
    if !openOk {
      observations := [];
      readErr := openErr;
      output := [];
      errors := Spec.OpenDirectoryErrorMessageSpec(displayPath, openErr);
      hadError := true;
      return;
    }
    observations, readErr, output, errors, hadError :=
      ReadOpenedDirectoryCore(cmd, displayPath, path, handle, io);
  }

  ghost predicate RecursivePrefixSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    observations: seq<Spec.EntryObservation>,
    listing: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes,
    listingHadError: bool,
    i: nat,
    children: map<nat, Spec.RecursiveWitness>,
    cycles: set<nat>,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
  {
    i <= |observations| &&
    (forall j: nat :: j in children ==> j < i) &&
    (forall j: nat :: j in cycles ==> j < i) &&
    cycles <= children.Keys &&
    (forall j: nat :: j < i ==>
                        (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
                        (j in cycles <==> j in children && children[j].cycle)) &&
    (forall j: nat :: j in children ==>
                        j < |observations| &&
                        RecursiveDirectorySummary(
                          cmd, fs,
                          Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                          observations[j].accessPath,
                          ancestors, children[j])) &&
    output == Spec.DirectoryHeaderSpec(displayPath) + listing +
    RecursiveChildOutputPrefixCore(observations, children, i) &&
    errors == listingErrors + RecursiveChildErrorPrefixCore(
      displayPath, observations, children, cycles, i) &&
    hadError ==
    (listingHadError ||
     exists j: nat :: j in children && children[j].hadError)
  }

  lemma RecursivePrefixRanges(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path, ancestors: set<BenchWorld.HostInodeKey>,
    observations: seq<Spec.EntryObservation>, listing: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes, listingHadError: bool, i: nat,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>,
    output: BenchWorld.Bytes, errors: BenchWorld.Bytes, hadError: bool
  )
    requires RecursivePrefixSummary(
               cmd, fs, displayPath, ancestors, observations, listing,
               listingErrors, listingHadError, i, children, cycles,
               output, errors, hadError)
    ensures forall j: nat :: j in children ==> j < i
    ensures forall j: nat :: j in cycles ==> j < i
  {
    reveal RecursivePrefixSummary(
           cmd, fs, displayPath, ancestors, observations, listing,
           listingErrors, listingHadError, i, children, cycles,
           output, errors, hadError);
  }

  lemma RecursivePrefixComplete(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path, accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>, tree: Spec.RecursiveWitness,
    statusCuts: seq<nat>
  )
    requires DirectoryListingSummary(
               cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
               tree.listingAfterStatus,
               tree.observations, tree.readErr,
               tree.listingOutput, tree.listingErrors, tree.listingHadError)
    requires cmd.statusContext.BoundStatusObservations?
    requires tree.openOk && tree.openErr == 0 && tree.statusOk &&
             tree.statusErr == 0 && !tree.cycle
    requires tree.openedStatus.hostKey !in ancestors
    requires tree.listingFirstStatus == tree.firstStatus + 1
    requires exists resolved: BenchWorld.Path ::
      IOContract.ResolvePathForMetadataFields(fs, accessPath, true) == BenchWorld.Ok(resolved) &&
      IOContract.ObservedFileStatusContractFields(
        cmd.statusContext.observations, tree.firstStatus, fs, resolved,
        true, true, tree.openedStatus, 0)
    requires IOContract.OpenDirFailureErrFields(fs, accessPath) == 0
    requires |statusCuts| == |tree.observations| + 1
    requires statusCuts[0] == tree.listingAfterStatus
    requires statusCuts[|tree.observations|] == tree.afterStatus
    requires forall i: nat | i < |tree.observations| ::
      (if i in tree.children then
         tree.children[i].firstStatus == statusCuts[i] &&
         tree.children[i].afterStatus == statusCuts[i + 1]
       else statusCuts[i] == statusCuts[i + 1])
    requires RecursivePrefixSummary(
               cmd, fs, displayPath, ancestors + {tree.openedStatus.hostKey},
               tree.observations, tree.listingOutput,
               tree.listingErrors, tree.listingHadError, |tree.observations|,
               tree.children, tree.cycles, tree.output, tree.errors, tree.hadError)
    ensures RecursiveDirectorySummary(
              cmd, fs, displayPath, accessPath, ancestors, tree)
  {
    reveal RecursivePrefixSummary(
           cmd, fs, displayPath, ancestors + {tree.openedStatus.hostKey},
           tree.observations, tree.listingOutput,
           tree.listingErrors, tree.listingHadError, |tree.observations|,
           tree.children, tree.cycles, tree.output, tree.errors, tree.hadError);
    reveal RecursiveDirectorySummary();
  }

  ghost opaque predicate StatusCutsPrefix(
    cuts: seq<nat>, children: map<nat, Spec.RecursiveWitness>, processed: nat
  )
  {
    |cuts| == processed + 1 &&
    forall j: nat | j < processed ::
      (if j in children then
         children[j].firstStatus == cuts[j] &&
         children[j].afterStatus == cuts[j + 1]
       else cuts[j] == cuts[j + 1])
  }

  lemma StatusCutsSnoc(
    beforeCuts: seq<nat>, beforeChildren: map<nat, Spec.RecursiveWitness>,
    afterChildren: map<nat, Spec.RecursiveWitness>, i: nat,
    afterStatus: nat, addedChild: bool
  )
    requires StatusCutsPrefix(beforeCuts, beforeChildren, i)
    requires |beforeCuts| == i + 1
    requires i !in beforeChildren
    requires if addedChild then
      i in afterChildren &&
      afterChildren == beforeChildren[i := afterChildren[i]] &&
      afterChildren[i].firstStatus == beforeCuts[i] &&
      afterChildren[i].afterStatus == afterStatus
    else afterChildren == beforeChildren && afterStatus == beforeCuts[i]
    ensures StatusCutsPrefix(beforeCuts + [afterStatus], afterChildren, i + 1)
  {
    reveal StatusCutsPrefix();
    forall j: nat | j < i + 1
      ensures (if j in afterChildren then
                 afterChildren[j].firstStatus == (beforeCuts + [afterStatus])[j] &&
                 afterChildren[j].afterStatus == (beforeCuts + [afterStatus])[j + 1]
               else (beforeCuts + [afterStatus])[j] ==
                    (beforeCuts + [afterStatus])[j + 1])
    {
      if j < i {
        assert j in afterChildren <==> j in beforeChildren;
        if j in afterChildren {
          assert afterChildren[j] == beforeChildren[j];
        }
        assert (beforeCuts + [afterStatus])[j] == beforeCuts[j];
        assert (beforeCuts + [afterStatus])[j + 1] == beforeCuts[j + 1];
      } else {
        assert j == i;
        assert (beforeCuts + [afterStatus])[j] == beforeCuts[i];
        assert (beforeCuts + [afterStatus])[j + 1] == afterStatus;
      }
    }
  }

  lemma RecursiveOutputPrefixAgreement(
    observations: seq<Spec.EntryObservation>,
    left: map<nat, Spec.RecursiveWitness>,
    right: map<nat, Spec.RecursiveWitness>,
    processed: nat
  )
    requires processed <= |observations|
    requires forall k: nat :: k < processed ==>
                                (k in left <==> k in right) &&
                                (k in left ==> left[k] == right[k])
    ensures RecursiveChildOutputPrefixCore(observations, left, processed) ==
            RecursiveChildOutputPrefixCore(observations, right, processed)
    decreases processed
  {
    if processed > 0 {
      RecursiveOutputPrefixAgreement(observations, left, right, processed - 1);
      reveal RecursiveChildOutputPrefixCore();
    }
  }

  lemma RecursiveErrorPrefixAgreement(
    displayPath: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>,
    leftChildren: map<nat, Spec.RecursiveWitness>, leftCycles: set<nat>,
    rightChildren: map<nat, Spec.RecursiveWitness>, rightCycles: set<nat>,
    processed: nat
  )
    requires processed <= |observations|
    requires forall k: nat :: k < processed ==>
                                (k in leftCycles <==> k in rightCycles) &&
                                (k in leftChildren <==> k in rightChildren) &&
                                (k in leftChildren ==> leftChildren[k].errors == rightChildren[k].errors)
    ensures RecursiveChildErrorPrefixCore(
              displayPath, observations, leftChildren, leftCycles, processed) ==
            RecursiveChildErrorPrefixCore(
              displayPath, observations, rightChildren, rightCycles, processed)
    decreases processed
  {
    if processed > 0 {
      RecursiveErrorPrefixAgreement(
        displayPath, observations, leftChildren, leftCycles,
        rightChildren, rightCycles, processed - 1);
      reveal RecursiveChildErrorPrefixCore();
    }
  }

  lemma RecursiveOutputSnoc(
    displayPath: BenchWorld.Path, listing: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    beforeChildren: map<nat, Spec.RecursiveWitness>,
    afterChildren: map<nat, Spec.RecursiveWitness>, i: nat,
    beforeOutput: BenchWorld.Bytes, piece: BenchWorld.Bytes
  )
    requires i < |observations|
    requires beforeOutput == Spec.DirectoryHeaderSpec(displayPath) + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i)
    requires afterChildren == beforeChildren ||
             (i in afterChildren && afterChildren == beforeChildren[i := afterChildren[i]])
    requires piece ==
             (if i in afterChildren && Spec.RecursiveNodeListed(afterChildren[i])
              then "\n" + afterChildren[i].output else [])
    ensures beforeOutput + piece == Spec.DirectoryHeaderSpec(displayPath) + listing +
                                    RecursiveChildOutputPrefixCore(observations, afterChildren, i + 1)
  {
    assert forall k: nat :: k < i ==>
                              (k in beforeChildren <==> k in afterChildren) &&
                              (k in beforeChildren ==> beforeChildren[k] == afterChildren[k]) by {
      forall k: nat | k < i
        ensures (k in beforeChildren <==> k in afterChildren) &&
                (k in beforeChildren ==> beforeChildren[k] == afterChildren[k])
      {
        assert k != i;
      }
    }
    RecursiveOutputPrefixAgreement(observations, beforeChildren, afterChildren, i);
    reveal RecursiveChildOutputPrefixCore();
  }

  lemma RecursiveErrorSnoc(
    displayPath: BenchWorld.Path, listingErrors: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    beforeChildren: map<nat, Spec.RecursiveWitness>, beforeCycles: set<nat>,
    afterChildren: map<nat, Spec.RecursiveWitness>, afterCycles: set<nat>, i: nat,
    beforeErrors: BenchWorld.Bytes, piece: BenchWorld.Bytes
  )
    requires i < |observations|
    requires beforeErrors == listingErrors + RecursiveChildErrorPrefixCore(
                               displayPath, observations, beforeChildren, beforeCycles, i)
    requires afterChildren == beforeChildren ||
             (i in afterChildren && afterChildren == beforeChildren[i := afterChildren[i]])
    requires afterCycles == beforeCycles || afterCycles == beforeCycles + {i}
    requires piece ==
             (if i in afterCycles then
                Spec.RecursiveCycleMessageSpec(
                  Spec.ChildDisplayPath(displayPath, observations[i].displayName))
              else if i in afterChildren then afterChildren[i].errors else [])
    ensures beforeErrors + piece == listingErrors + RecursiveChildErrorPrefixCore(
                                      displayPath, observations, afterChildren, afterCycles, i + 1)
  {
    assert forall k: nat :: k < i ==>
                              (k in beforeCycles <==> k in afterCycles) &&
                              (k in beforeChildren <==> k in afterChildren) &&
                              (k in beforeChildren ==> beforeChildren[k].errors == afterChildren[k].errors) by {
      forall k: nat | k < i
        ensures (k in beforeCycles <==> k in afterCycles) &&
                (k in beforeChildren <==> k in afterChildren) &&
                (k in beforeChildren ==> beforeChildren[k].errors == afterChildren[k].errors)
      {
        assert k != i;
      }
    }
    RecursiveErrorPrefixAgreement(
      displayPath, observations, beforeChildren, beforeCycles,
      afterChildren, afterCycles, i);
    reveal RecursiveChildErrorPrefixCore();
  }

  lemma FailedChildAfterUpdate(
    before: map<nat, Spec.RecursiveWitness>,
    index: nat,
    child: Spec.RecursiveWitness
  )
    requires index !in before
    ensures (exists j: nat {:trigger before[index := child][j]} ::
               j in before[index := child] && before[index := child][j].hadError) <==>
            (child.hadError || exists j: nat {:trigger before[j]} :: j in before && before[j].hadError)
  {
    assert (exists j: nat {:trigger before[index := child][j]} ::
              j in before[index := child] && before[index := child][j].hadError) ==>
        (child.hadError || exists j: nat {:trigger before[j]} ::
           j in before && before[j].hadError) by {
      if exists j: nat {:trigger before[index := child][j]} ::
          j in before[index := child] && before[index := child][j].hadError {
        var j: nat :| j in before[index := child] && before[index := child][j].hadError;
        if j != index {
          assert j in before;
          assert before[index := child][j] == before[j];
          assert exists k: nat {:trigger before[k]} :: k in before && before[k].hadError;
        }
      }
    }
    assert (child.hadError || exists j: nat {:trigger before[j]} ::
              j in before && before[j].hadError) ==>
        (exists j: nat {:trigger before[index := child][j]} ::
           j in before[index := child] && before[index := child][j].hadError) by {
      if child.hadError {
        assert index in before[index := child];
      } else if exists j: nat {:trigger before[j]} :: j in before && before[j].hadError {
        var j: nat :| j in before && before[j].hadError;
        assert j != index;
        assert before[index := child][j] == before[j];
      }
    }
  }

  method {:vcs_split_on_every_assert} WalkDirectoryRecursive(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    io: BenchIO.IO
  ) returns (
      wasOpened: bool,
      wasListed: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool,
      hasCycle: bool,
      ghost tree: Spec.RecursiveWitness
    )
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    modifies io.dirHandlesRegion, io.statusObservationsRegion
    ensures RecursiveDirectorySummary(
              cmd, old(io.fs()), displayPath, accessPath, ancestors, tree)
    ensures wasOpened ==
            (IOContract.OpenDirFailureErrFields(old(io.fs()), accessPath) == 0)
    ensures !wasOpened ==>
              errors == Spec.OpenDirectoryErrorMessageSpec(
                displayPath, IOContract.OpenDirFailureErrFields(old(io.fs()), accessPath)) &&
              hadError && io.statusCursor() == old(io.statusCursor())
    ensures !wasOpened ==> !hasCycle
    ensures hasCycle == Spec.RecursiveHasCycle(tree)
    ensures wasListed == Spec.RecursiveNodeListed(tree)
    ensures output == tree.output && errors == tree.errors && hadError == tree.hadError
    ensures tree.firstStatus == old(io.statusCursor())
    ensures tree.afterStatus == io.statusCursor()
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    var openOk, handle, openErr := io.OpenDir(accessPath, true);
    reveal IOContract.OpenDirContractFields();
    wasOpened := openOk;
    if !openOk {
      wasListed := false;
      output := [];
      errors := Spec.OpenDirectoryErrorMessageSpec(displayPath, openErr);
      hadError := true;
      hasCycle := false;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        false, openErr, false, BenchWorld.DEFAULT_FILE_STATUS, 0, false,
        preStatus, preStatus, preStatus, preStatus);
      assert RecursiveDirectorySummary(
        cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary();
      }
      return;
    }
    var statusOk, openedStatus, statusErr := io.GetOpenDirectoryStatus(handle);
    reveal IOContract.GetOpenDirectoryStatusContractFields();
    if !statusOk {
      wasListed := false;
      io.CloseDir(handle);
      output := [];
      errors := Spec.DirectoryIdentityErrorMessageSpec(displayPath, statusErr);
      hadError := true;
      hasCycle := false;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        true, 0, false, openedStatus, statusErr, false,
        preStatus, preStatus, preStatus, preStatus);
      assert RecursiveDirectorySummary(
        cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary();
      }
      return;
    }
    ghost var listingFirst := io.statusCursor();
    assert listingFirst == preStatus + 1;
    if openedStatus.hostKey in ancestors {
      wasListed := false;
      io.CloseDir(handle);
      output := [];
      errors := Spec.RecursiveCycleMessageSpec(displayPath);
      hadError := true;
      hasCycle := true;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        true, 0, true, openedStatus, 0, true,
        preStatus, listingFirst, listingFirst, listingFirst);
      assert RecursiveDirectorySummary(
        cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary();
      }
      return;
    }
    var observations: seq<Spec.EntryObservation>;
    var readErr: int;
    var listing: BenchWorld.Bytes;
    var listingErrors: BenchWorld.Bytes;
    var listingHadError: bool;
    observations, readErr, listing, listingErrors, listingHadError :=
      ReadOpenedDirectoryCore(cmd, displayPath, accessPath, handle, io);
    wasListed := true;
    ghost var listingAfter := io.statusCursor();
    errors := listingErrors;
    hadError := listingHadError;
    hasCycle := false;
    output := Spec.DirectoryHeaderSpec(displayPath) + listing;
    ghost var children: map<nat, Spec.RecursiveWitness> := map[];
    ghost var cycles: set<nat> := {};
    var childAncestors := ancestors + {openedStatus.hostKey};
    ghost var statusCuts: seq<nat> := [listingAfter];
    assert StatusCutsPrefix(statusCuts, children, 0) by {
      reveal StatusCutsPrefix();
    }
    var i := 0;
    assert RecursivePrefixSummary(
        cmd, preFs, displayPath, childAncestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError) by {
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, childAncestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
    }
    while i < |observations|
      invariant hasCycle == (cycles != {} || exists j: nat :: j in children && Spec.RecursiveHasCycle(children[j]))
      invariant 0 <= i <= |observations|
      invariant |statusCuts| == i + 1
      invariant statusCuts[0] == listingAfter
      invariant statusCuts[i] == io.statusCursor()
      invariant StatusCutsPrefix(statusCuts, children, i)
      invariant RecursivePrefixSummary(
                  cmd, preFs, displayPath, childAncestors, observations, listing,
                  listingErrors, listingHadError, i, children, cycles,
                  output, errors, hadError)
      decreases *
    {
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, childAncestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
      ghost var beforeChildren := children;
      ghost var beforeCycles := cycles;
      ghost var beforeStatus := io.statusCursor();
      ghost var beforeCuts := statusCuts;
      var beforeOutput := output;
      var beforeErrors := errors;
      var beforeHadError := hadError;
      assert beforeOutput == Spec.DirectoryHeaderSpec(displayPath) + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i);
      assert beforeErrors == listingErrors + RecursiveChildErrorPrefixCore(
                               displayPath, observations, beforeChildren, beforeCycles, i);
      assert beforeHadError ==
             (listingHadError ||
              exists j: nat :: j in beforeChildren && beforeChildren[j].hadError);
      RecursivePrefixRanges(
        cmd, preFs, displayPath, childAncestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError);
      var observation := observations[i];
      var outputPiece: BenchWorld.Bytes := [];
      var errorPiece: BenchWorld.Bytes := [];
      var stepFailed := false;
      ghost var addedChild := false;
      ghost var addedCycle := false;
      if Spec.RecursiveEntryEligible(observation)
      {
        var childDisplay := Spec.ChildDisplayPath(displayPath, observation.displayName);
        var descendantOutput: BenchWorld.Bytes;
        var descendantErrors: BenchWorld.Bytes;
        var childFailed: bool;
        var childHasCycle: bool;
        var childListed: bool;
        ghost var childTree: Spec.RecursiveWitness;
        var childOpened: bool;
        childOpened, childListed, descendantOutput, descendantErrors, childFailed, childHasCycle, childTree := WalkDirectoryRecursive(
          cmd, childDisplay, observation.accessPath, childAncestors, io);
        outputPiece := if childListed then "\n" + descendantOutput else [];
        errorPiece := descendantErrors;
        assert i !in children;
        children := children[i := childTree];
        if childTree.cycle {
          cycles := cycles + {i};
          addedCycle := true;
        }
        hasCycle := hasCycle || childHasCycle;
        stepFailed := childFailed;
        addedChild := true;
      }
      output := output + outputPiece;
      errors := errors + errorPiece;
      hadError := hadError || stepFailed;
      statusCuts := statusCuts + [io.statusCursor()];
      StatusCutsSnoc(beforeCuts, beforeChildren, children, i,
                     io.statusCursor(), addedChild);
      assert children == beforeChildren ||
             (i in children && children == beforeChildren[i := children[i]]);
      assert cycles == beforeCycles || cycles == beforeCycles + {i};
      assert i !in beforeChildren;
      assert children.Keys <= beforeChildren.Keys + {i};
      assert cycles <= beforeCycles + {i};
      assert forall j: nat :: j in children ==> j < i + 1 by {
        forall j: nat | j in children
          ensures j < i + 1
        {
          if j != i {
            assert j in beforeChildren.Keys;
            assert j < i;
          }
        }
      }
      assert forall j: nat :: j in cycles ==> j < i + 1 by {
        forall j: nat | j in cycles
          ensures j < i + 1
        {
          if j != i {
            assert j in beforeCycles;
            assert j < i;
          }
        }
      }
      assert cycles <= children.Keys;
      assert forall j: nat :: j < i + 1 ==>
                                (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
                                (j in cycles <==> j in children && children[j].cycle) by {
        forall j: nat | j < i + 1
          ensures
            (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
            (j in cycles <==> j in children && children[j].cycle)
        {
          if j < i {
            assert j in children <==> j in beforeChildren;
            assert j in cycles <==> j in beforeCycles;
          } else {
            assert j == i;
          }
        }
      }
      assert forall j: nat :: j in children ==>
                                j < |observations| &&
                                RecursiveDirectorySummary(
                                  cmd, preFs,
                                  Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                                  observations[j].accessPath,
                                  childAncestors, children[j]) by {
        forall j: nat | j in children
          ensures j < |observations| &&
                  RecursiveDirectorySummary(
                    cmd, preFs,
                    Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                    observations[j].accessPath,
                    childAncestors, children[j])
        {
          if j != i {
            assert j in beforeChildren;
          }
        }
      }
      assert outputPiece ==
             (if i in children && Spec.RecursiveNodeListed(children[i])
              then "\n" + children[i].output else []);
      RecursiveOutputSnoc(
        displayPath, listing, observations, beforeChildren, children, i,
        beforeOutput, outputPiece);
      assert output == beforeOutput + outputPiece;
      if i in cycles {
        assert i in children;
        assert children[i].errors == Spec.RecursiveCycleMessageSpec(
          Spec.ChildDisplayPath(displayPath, observations[i].displayName)) by {
          reveal RecursiveDirectorySummary(
            cmd, preFs,
            Spec.ChildDisplayPath(displayPath, observations[i].displayName),
            observations[i].accessPath, childAncestors, children[i]);
        }
      }
      assert errorPiece ==
             (if i in cycles then
                Spec.RecursiveCycleMessageSpec(
                  Spec.ChildDisplayPath(displayPath, observations[i].displayName))
              else if i in children then children[i].errors else []);
      RecursiveErrorSnoc(
        displayPath, listingErrors, observations, beforeChildren, beforeCycles,
        children, cycles, i, beforeErrors, errorPiece);
      assert errors == beforeErrors + errorPiece;
      assert hadError ==
             (listingHadError ||
              exists j: nat :: j in children && children[j].hadError) by {
        if addedChild {
          assert i in children;
          assert children == beforeChildren[i := children[i]];
          assert stepFailed == children[i].hadError;
          FailedChildAfterUpdate(beforeChildren, i, children[i]);
        } else if addedCycle {
          assert cycles == beforeCycles + {i};
          assert |cycles| > 0;
        } else {
          assert children == beforeChildren;
          assert cycles == beforeCycles;
          assert !stepFailed;
        }
      }
      i := i + 1;
      assert RecursivePrefixSummary(
          cmd, preFs, displayPath, childAncestors, observations, listing,
          listingErrors, listingHadError, i, children, cycles,
          output, errors, hadError) by {
        reveal RecursivePrefixSummary(
               cmd, preFs, displayPath, childAncestors, observations, listing,
               listingErrors, listingHadError, i, children, cycles,
               output, errors, hadError);
      }
    }
    reveal RecursivePrefixSummary(
           cmd, preFs, displayPath, childAncestors, observations, listing,
           listingErrors, listingHadError, i, children, cycles,
           output, errors, hadError);
    tree := Spec.RecursiveWitness(
      observations, readErr, listing, listingErrors, listingHadError,
      children, cycles, output, errors, hadError,
      true, 0, true, openedStatus, 0, false,
      preStatus, listingFirst, listingAfter, io.statusCursor());
    reveal StatusCutsPrefix();
    RecursivePrefixComplete(
      cmd, preFs, displayPath, accessPath, ancestors, tree, statusCuts);
  }

  method {:vcs_split_on_every_assert} ObserveOperand(
    index: nat,
    cmd: Schema.LsCmd,
    cwd: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (observation: Spec.OperandObservation)
    requires index < |cmd.operands|
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    modifies io.dirHandlesRegion, io.statusObservationsRegion
    ensures observation.index == index
    ensures OperandObservationSummary(cmd, old(io.fs()), cwd, observation)
    ensures observation.firstStatus == old(io.statusCursor())
    ensures observation.afterStatus == io.statusCursor()
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    var operand := cmd.operands[index];
    var path := Spec.MakeAbsoluteSpec(cwd, operand);
    var follow := Spec.ImplicitDirectoryFollowSpec(cmd) ||
                  Spec.ExplicitCommandLineFollowSpec(cmd);
    var ok, status, err := io.GetFileStatus(path, follow);
    reveal IOContract.ObservedFileStatusContractFields();
    if Spec.ImplicitDirectoryFollowSpec(cmd) &&
       (!ok || status.kind != BenchWorld.DirectoryKind) {
      ok, status, err := io.GetFileStatus(path, false);
      reveal IOContract.ObservedFileStatusContractFields();
    }
    ghost var afterOperandStatus := io.statusCursor();
    assert afterOperandStatus == preStatus +
      Spec.OperandStatusCallCountSpec(cmd, preFs, path, preStatus);
    assert match Spec.OperandStatusResultSpec(cmd, preFs, path, preStatus)
           case Ok(expected) => ok && status == expected && err == 0
           case Err(error) => !ok && err == IOContract.IOErrorErrno(error) by {
      reveal IOContract.ObservedFileStatusContractFields();
    }
    if !ok {
      observation := Spec.OperandObservation(
        index, operand, operand, path, false, status, err, Spec.AccessFailure,
        false, [], Spec.AccessErrorMessageSpec(operand, err), [], true, false,
        preStatus, io.statusCursor());
      assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
        reveal OperandObservationSummary();
      }
    } else if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories {
      var wasOpened: bool;
      var body: BenchWorld.Bytes;
      var sectionErrors: BenchWorld.Bytes;
      var failed: bool;
      if cmd.recursive {
        var hasCycle: bool;
        var wasListed: bool;
        ghost var recursiveTree: Spec.RecursiveWitness;
        wasOpened, wasListed, body, sectionErrors, failed, hasCycle, recursiveTree := WalkDirectoryRecursive(
          cmd, operand, path, {}, io);
        observation := Spec.OperandObservation(
          index, operand, operand, path, true, status, 0, Spec.ExpandedDirectory,
          wasOpened, if wasOpened then body else [], [], sectionErrors, failed, hasCycle,
          preStatus, io.statusCursor());
        assert recursiveTree.firstStatus == afterOperandStatus;
        assert recursiveTree.afterStatus == observation.afterStatus;
        assert observation.sectionAvailable ==
          (IOContract.OpenDirFailureErrFields(preFs, path) == 0);
        ExpandedRecursiveOperandSummary(
          cmd, preFs, cwd, observation, recursiveTree);
      } else {
        var observations: seq<Spec.EntryObservation>;
        var readErr: int;
        var listingOutput: BenchWorld.Bytes;
        observations, readErr, wasOpened, listingOutput, sectionErrors, failed :=
          ReadDirectoryCore(cmd, operand, path, io);
        body := listingOutput;
        if |cmd.operands| > 1 {
          body := Spec.DirectoryHeaderSpec(operand) + body;
        }
        observation := Spec.OperandObservation(
          index, operand, operand, path, true, status, 0, Spec.ExpandedDirectory,
          wasOpened, if wasOpened then body else [], [], sectionErrors, failed, false,
          preStatus, io.statusCursor());
        assert observation.sectionAvailable ==
          (IOContract.OpenDirFailureErrFields(preFs, path) == 0);
        assert Spec.OperandStatusResultSpec(cmd, preFs, path, preStatus) ==
          BenchWorld.Ok(status);
        if wasOpened {
          assert observation.body ==
            (if |cmd.operands| > 1 then Spec.DirectoryHeaderSpec(operand)
             else []) + listingOutput by {
            if |cmd.operands| > 1 {
            } else {
            }
          }
          assert DirectoryListingSummary(
            cmd, operand, preFs, path, afterOperandStatus, io.statusCursor(),
            observations, readErr, listingOutput, sectionErrors, failed);
        } else {
          assert io.statusCursor() == afterOperandStatus;
          assert observation.body == [];
          assert observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
            operand, IOContract.OpenDirFailureErrFields(preFs, path));
        }
        assert observation.index < |cmd.operands|;
        assert observation.operand == cmd.operands[observation.index];
        assert observation.path == Spec.MakeAbsoluteSpec(cwd, observation.operand);
        assert observation.ok && observation.err == 0 &&
               observation.operandClass == Spec.ExpandedDirectory;
        assert observation.status.kind == BenchWorld.DirectoryKind &&
               !cmd.listDirectories && !cmd.recursive;
        assert observation.accessErrors == [];
        assert if observation.sectionAvailable then
          DirectoryListingSummary(
            cmd, observation.operand, preFs, observation.path,
            observation.firstStatus + Spec.OperandStatusCallCountSpec(
              cmd, preFs, observation.path, observation.firstStatus),
            observation.afterStatus, observations, readErr,
            listingOutput, observation.sectionErrors, observation.failed) &&
          observation.body ==
            (if |cmd.operands| > 1
             then Spec.DirectoryHeaderSpec(observation.operand)
             else []) + listingOutput
        else
          observation.afterStatus == observation.firstStatus +
            Spec.OperandStatusCallCountSpec(
              cmd, preFs, observation.path, observation.firstStatus) &&
          observation.body == [] &&
          observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
            observation.operand,
            IOContract.OpenDirFailureErrFields(preFs, observation.path)) &&
          observation.failed by {
          if observation.sectionAvailable {
            assert wasOpened;
          } else {
            assert !wasOpened;
          }
        }
        ExpandedFlatOperandSummary(
          cmd, preFs, cwd, observation, observations, readErr, listingOutput);
      }
    } else {
      var renderName := operand;
      if status.kind == BenchWorld.SymlinkKind && !follow && cmd.numericLong {
        var linkResult := io.ReadLink(path);
        match linkResult
        case Ok(target) => renderName := operand + " -> " + target;
        case Err(_) =>
      }
      observation := Spec.OperandObservation(
        index, operand, renderName, path, true, status, 0, Spec.DirectOperand,
        false, RenderEntryCore(cmd, renderName, status), [], [], false, false,
        preStatus, io.statusCursor());
      assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
        reveal OperandObservationSummary();
      }
    }
  }

  function PositiveEnvironmentResult(result: BenchWorld.Result<string>): nat
  {
    match result
    case Ok(value) => Spec.ParsedPositiveOrZeroSpec(value)
    case Err(_) => 0
  }

  method ResolveEnvironmentBlockSize(io: BenchIO.IO) returns (
      blockSize: nat,
      fileSizeBlockSize: nat
    )
    ensures blockSize == Spec.EnvironmentBlockSizeSpec(old(io.env()))
    ensures fileSizeBlockSize == Spec.EnvironmentFileSizeBlockSizeSpec(old(io.env()))
    ensures blockSize > 0
    ensures fileSizeBlockSize > 0
  {
    ghost var preEnv := io.env();
    var lsValue := io.GetEnv("LS_BLOCK_SIZE");
    var blockValue := io.GetEnv("BLOCK_SIZE");
    var legacyValue := io.GetEnv("BLOCKSIZE");
    var lsSize := PositiveEnvironmentResult(lsValue);
    var genericSize := PositiveEnvironmentResult(blockValue);
    var legacySize := PositiveEnvironmentResult(legacyValue);
    blockSize := if lsSize > 0 then lsSize
    else if genericSize > 0 then genericSize
    else if legacySize > 0 then legacySize
    else 1024;
    fileSizeBlockSize := if lsSize > 0 then lsSize
    else if genericSize > 0 then genericSize
    else 1;
    reveal IOContract.GetEnvContractFields();
  }

  method {:vcs_split_on_every_assert} RunCore(raw: Schema.LsCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preEnv := io.env();
    ghost var preNow := io.now();
    ghost var preStatus := io.statusCursor();
    ghost var preStatusObservations := io.statusObservations();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var parsedCmd := Schema.Command(raw);
    var cmd := parsedCmd;
    if parsedCmd.mode == Schema.ModeHelp {
      var _, _ := io.WriteStdout(Spec.HelpTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
      }
      return;
    }
    if parsedCmd.mode == Schema.ModeVersion {
      var _, _ := io.WriteStdout(Spec.VersionTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
      }
      return;
    }
    if parsedCmd.mode != Schema.ModeRun {
      var _, _ := io.WriteStderr(Spec.InvalidModeMessageSpec(parsedCmd.mode), BenchWorld.ThrowOnError);
      exit := if parsedCmd.mode.ModeInvalidTime? then 1 else 2;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
      }
      return;
    }

    var blockSize := parsedCmd.cliBlockSize;
    var fileSizeBlockSize := parsedCmd.fileSizeBlockSize;
    if blockSize == 0 {
      blockSize, fileSizeBlockSize := ResolveEnvironmentBlockSize(io);
    }
    var referenceNow := io.Now();
    cmd := Schema.WithReferenceNow(
      Schema.WithBlockSize(parsedCmd, blockSize, fileSizeBlockSize), referenceNow);
    assert cmd == Spec.EffectiveCommandSpec(raw, preEnv, preNow);
    cmd := Schema.WithStatusObservations(cmd, preStatusObservations, preStatus);
    assert cmd == Schema.WithStatusObservations(
      Spec.EffectiveCommandSpec(raw, preEnv, preNow), preStatusObservations, preStatus);

    var cwd := io.GetCwd();
    var output: BenchWorld.Bytes := [];
    var errors: BenchWorld.Bytes := [];
    var hadError := false;
    var observations: seq<Spec.OperandObservation> := [];
    ghost var statusCuts: seq<nat> := [preStatus];
    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant |observations| == i
      invariant |statusCuts| == i + 1
      invariant statusCuts[0] == preStatus
      invariant statusCuts[i] == io.statusCursor()
      invariant io.statusObservations() == preStatusObservations
      invariant forall j: nat | j < i ::
        observations[j].firstStatus == statusCuts[j] &&
        observations[j].afterStatus == statusCuts[j + 1]
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant cwd == preCwd
      invariant forall j: nat :: j < i ==>
                                   observations[j].index == j &&
                                   OperandObservationSummary(cmd, preFs, preCwd, observations[j])
      invariant output == []
      invariant errors == []
      invariant hadError ==
                (exists j: nat :: j < i && observations[j].failed)
      decreases |cmd.operands| - i
    {
      var observation := ObserveOperand(i, cmd, cwd, io);
      ghost var beforeObservations := observations;
      FailedOperandSnoc(beforeObservations, observation);
      observations := observations + [observation];
      statusCuts := statusCuts + [io.statusCursor()];
      hadError := hadError || observation.failed;
      assert observations[i] == observation;
      i := i + 1;
    }
    var sorted := SortOperandsCore(cmd, observations);
    var groups := OutputGroupsCore(cmd, sorted);
    output := JoinOutputGroupsCore(groups);
    errors := AccessErrorsCore(observations) + SectionErrorsCore(sorted);
    var _, _ := io.WriteStdout(output, BenchWorld.ThrowOnError);
    var _, _ := io.WriteStderr(errors, BenchWorld.ThrowOnError);
    exit := OperandExitCore(observations);
    assert RunSummary(cmd, preFs, preCwd, preStatus, io.statusCursor(),
                      output, errors, exit);
    assert CoreSummary(raw, io, exit) by {
      reveal CoreSummary();
    }
  }
}
