include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "MvPathSpec.dfy"
include "MvQuoteSpec.dfy"
include "MvSchema.dfy"

module MvSpec {
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = MvQuoteSpec
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping





  function ErrnoTextSpec(err: int): string
  {
    if err == Errno.ENOENT then
      "No such file or directory"
    else if err == Errno.EACCES then
      "Permission denied"
    else if err == Errno.EBUSY then
      "Device or resource busy"
    else if err == Errno.EEXIST then
      "File exists"
    else if err == Errno.ENOTDIR then
      "Not a directory"
    else if err == Errno.EISDIR then
      "Is a directory"
    else if err == Errno.EINVAL then
      "Invalid argument"
    else if err == Errno.ENOTEMPTY then
      "Directory not empty"
    else if err == Errno.ELOOP then
      "Too many levels of symbolic links"
    else
      "unknown error"
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: mv [OPTION]... [-T] SOURCE DEST\n"
    + "  or:  mv [OPTION]... SOURCE... DIRECTORY\n"
    + "  or:  mv [OPTION]... -t DIRECTORY SOURCE...\n"
    + "Rename SOURCE to DEST, or move SOURCE(s) to DIRECTORY.\n"
    + "\n"
    + "      --backup[=CONTROL]       make a backup of each existing destination file\n"
    + "  -b                           like --backup but does not accept an argument\n"
    + "      --debug                  explain how a file is moved; implies -v\n"
    + "  -f, --force                  do not prompt before overwriting\n"
    + "  -n, --no-clobber             do not overwrite an existing file\n"
    + "      --no-copy                do not copy if a rename cannot be performed\n"
    + "  -S, --suffix=SUFFIX          override the usual backup suffix\n"
    + "      --strip-trailing-slashes remove any trailing slashes from each SOURCE\n"
    + "  -t, --target-directory=DIR   move all SOURCE arguments into DIR\n"
    + "  -T, --no-target-directory    treat DEST as a normal file\n"
    + "      --update[=UPDATE]        control which existing files are updated\n"
    + "  -u                           equivalent to --update=older\n"
    + "  -v, --verbose                explain what is being done\n"
    + "      --help                   display this help and exit\n"
    + "      --version                output version information and exit\n"
    + "\n"
    + "This benchmark models rename-style moves over regular files, directories,\n"
    + "and symlinks already represented in the benchmark IO filesystem.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/mv>\n"
    + "or available locally via: info '(coreutils) mv invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "mv (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker, David MacKenzie, and Jim Meyering.\n"
  }

  function MissingFileOperandMessageSpec(): BenchWorld.Bytes
  {
    "mv: missing file operand\nTry 'mv --help' for more information.\n"
  }

  function MissingDestinationMessageSpec(source: string): BenchWorld.Bytes
  {
    "mv: missing destination file operand after " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + "\n"
    + "Try 'mv --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    "mv: extra operand " + Quote.SpecQuoteAfBytes(Utf8.Encode(operand)) +
    "\nTry 'mv --help' for more information.\n"
  }

  function TargetDirectoryConflictMessageSpec(): BenchWorld.Bytes
  {
    "mv: cannot combine --target-directory (-t) and --no-target-directory (-T)\n"
  }

  function InvalidBackupArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    "mv: invalid argument " + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    " for 'backup type'\n"
    + "Valid arguments are:\n"
    + "  - 'none', 'off'\n"
    + "  - 'simple', 'never'\n"
    + "  - 'existing', 'nil'\n"
    + "  - 'numbered', 't'\n"
    + "Try 'mv --help' for more information.\n"
  }

  function InvalidUpdateArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    "mv: invalid argument " + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    " for '--update'\n"
    + "Valid arguments are:\n"
    + "  - 'all'\n"
    + "  - 'none'\n"
    + "  - 'none-fail'\n"
    + "  - 'older'\n"
    + "Try 'mv --help' for more information.\n"
  }

  function TargetFailureMessageSpec(path: string, explicitTargetDirectory: bool, err: int): BenchWorld.Bytes
  {
    if explicitTargetDirectory then
      "mv: target directory " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ": " + ErrnoTextSpec(err) + "\n"
    else
      "mv: target " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  function SourceStatFailureMessageSpec(source: string, err: int): BenchWorld.Bytes
  {
    "mv: cannot stat " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function RenameFailureMessageSpec(source: string, target: string, err: int): BenchWorld.Bytes
  {
    if err == Errno.EISDIR then
      "mv: cannot overwrite directory " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      " with non-directory " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + "\n"
    else if err == Errno.ENOTEMPTY then
      "mv: cannot overwrite " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      ": " + ErrnoTextSpec(err) + "\n"
    else
      "mv: cannot move " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      " to " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  function SourceRenameFailureMessageSpec(
    source: string,
    target: string,
    err: int,
    directorySourceWithExistingTarget: bool
  ): BenchWorld.Bytes
  {
    if directorySourceWithExistingTarget && err == Errno.ENOTDIR then
      "mv: cannot overwrite non-directory " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      " with directory " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + "\n"
    else if err == Errno.EINVAL then
      "mv: cannot move " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      " to a subdirectory of itself, " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + "\n"
    else
      RenameFailureMessageSpec(source, target, err)
  }

  function SourceRenameDiagnosticErrSpec(
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

  function SameFileMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    "mv: " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " and " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    " are the same file\n"
  }

  function BackupWouldDestroySourceMessageSpec(
    source: string,
    target: string
  ): BenchWorld.Bytes
  {
    "mv: backing up " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    " might destroy source;  " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " not moved\n"
  }

  function VerboseRenameMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    "renamed " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " -> " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + "\n"
  }

  function VerboseRenameWithBackupMessageSpec(source: string, target: string, backup: string): BenchWorld.Bytes
  {
    "renamed " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " -> " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    " (backup: " + Quote.SpecQuoteAfBytes(Utf8.Encode(backup)) + ")\n"
  }

  function DebugSkipMessageSpec(target: string): BenchWorld.Bytes
  {
    "skipped " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + "\n"
  }

  function NotReplacingMessageSpec(target: string): BenchWorld.Bytes
  {
    "mv: not replacing " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + "\n"
  }




















  function ShowActionMessageSpec(verbose: bool, debug: bool): bool
  {
    verbose || debug
  }

  function SkipStdoutSpec(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then DebugSkipMessageSpec(target) else []
  }

  function SourceLeafNameSpec(source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    if leaf == "" then source else leaf
  }

  // Both stay compilable structural recursions rather than quantifiers: a
  // quantifier is ghost in Dafny, and the non-ghost `NormalizeSourceSpec`
  // below calls these.
  function AllSlashesSpec(text: string): bool
    decreases |text|
  {
    |text| == 0 ||
    (text[0] == '/' && AllSlashesSpec(text[1..]))
  }

  function TrimTrailingSlashesSpec(text: string): string
    decreases |text|
  {
    if |text| == 0 then
      ""
    else if text[|text| - 1] == '/' then
      TrimTrailingSlashesSpec(text[..|text| - 1])
    else
      text
  }

  function NormalizeSourceSpec(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes then
      source
    else if source == "" then
      source
    else if AllSlashesSpec(source) then
      "/"
    else
      TrimTrailingSlashesSpec(source)
  }

  function TargetInDirectorySpec(directory: string, source: string): string
  {
    BenchWorld.AppendPath(directory, SourceLeafNameSpec(source))
  }

  ghost predicate SameInode(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists resolvedLeft: BenchWorld.Path, resolvedRight: BenchWorld.Path ::
      IOContract.ResolvePathForMetadataFields(fs, left, false) ==
      Result.Ok(resolvedLeft) &&
      IOContract.ResolvePathForMetadataFields(fs, right, false) ==
      Result.Ok(resolvedRight) &&
      BenchWorld.InodeSameObject(fs, resolvedLeft, resolvedRight)
  }

  ghost predicate SameDirectoryEntry(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists
      leftParent: string,
      rightParent: string,
      leftLeaf: string,
      rightLeaf: string,
      resolvedLeftParent: BenchWorld.Path,
      resolvedRightParent: BenchWorld.Path
      ::
        Dirname.DirnameRelation(left, leftParent) &&
        Dirname.DirnameRelation(right, rightParent) &&
        Basename.BasenameRelation(left, leftLeaf) &&
        Basename.BasenameRelation(right, rightLeaf) &&
        leftLeaf == rightLeaf &&
        IOContract.ResolvePathForMetadataFields(fs, leftParent, false) ==
        Result.Ok(resolvedLeftParent) &&
        IOContract.ResolvePathForMetadataFields(fs, rightParent, false) ==
        Result.Ok(resolvedRightParent) &&
        BenchWorld.InodeSameObject(
          fs, resolvedLeftParent, resolvedRightParent
        )
  }

  ghost predicate SourceSymlinkReferentHasTargetName(
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    exists
      resolvedSource: BenchWorld.Path,
      resolvedReferent: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(fs, source, false) ==
        Result.Ok(resolvedSource) &&
        BenchWorld.FsContainsPath(fs, resolvedSource) &&
        BenchWorld.FsNodeAt(fs, resolvedSource).Symlink? &&
        IOContract.ResolvePathIdentityContractFields(
          fs, preCwd, source, true, resolvedReferent, 0
        ) &&
        SameDirectoryEntry(fs, resolvedReferent, target)
  }

  datatype SameFileDecision =
    | ContinueMove
    | RejectSameFile

  ghost predicate SameFileMustBeRejected(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    SameDirectoryEntry(fs, source, target) ||
    (cmd.backupMode == Schema.BackupOff &&
     (SameInode(fs, source, target) ||
      SourceSymlinkReferentHasTargetName(
        fs, preCwd, source, target
      )))
  }

  ghost predicate SameFilePolicyRelation(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    decision: SameFileDecision
  )
  {
    decision ==
    if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
    then RejectSameFile
    else ContinueMove
  }

  lemma SameFilePolicyTotal(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
    ensures exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, fs, preCwd, source, target, decision
              )
  {
    var decision :=
      if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
      then RejectSameFile
      else ContinueMove;
    assert SameFilePolicyRelation(
        cmd, fs, preCwd, source, target, decision
      );
  }

  lemma SameFilePolicyFunctional(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    left: SameFileDecision,
    right: SameFileDecision
  )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, left
             )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, right
             )
    ensures left == right
  {
  }

  function DigitCharSpec(d: nat): char
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

  function DecimalNatSpec(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitCharSpec(n)]
    else
      DecimalNatSpec(n / 10) + [DigitCharSpec(n % 10)]
  }

  function NumberedBackupPathSpec(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNatSpec(index) + "~"
  }

  function SimpleBackupPathSpec(target: string, suffix: string): string
  {
    target + suffix
  }

  function SourceNewerSpec(srcSec: int, srcNsec: int, dstSec: int, dstNsec: int): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  }

  function TargetDirectoryErrSpec(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk then
      if !isDir then Errno.ENOTDIR else statErr
    else
      statErr
  }

  function StepSuccessStdoutSpec(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !ShowActionMessageSpec(verbose, debug) then
      []
    else if backupPath == "" then
      VerboseRenameMessageSpec(source, target)
    else
      VerboseRenameWithBackupMessageSpec(source, target, backupPath)
  }

  datatype MoveOutcome = MoveOutcome(
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool
  )

  datatype StatusCallEvidence = StatusCallEvidence(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int
  )

  ghost predicate StatusCallsFor(
    observations: BenchWorld.StatusTimeObservations,
    first: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    forall i: nat | i < |calls| ::
      IOContract.ObservedFileStatusContractFields(
        observations, first + i, calls[i].fs, calls[i].path,
        calls[i].followSymlink, calls[i].ok, calls[i].status, calls[i].err
      )
  }

  ghost predicate StatusRequest(
    call: StatusCallEvidence,
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool
  )
  {
    call.fs == fs && call.path == path && call.followSymlink == followSymlink
  }

  ghost predicate BackupStatusSuffix(
    backupMode: Schema.BackupMode,
    fs: BenchWorld.FileSystem,
    target: string,
    calls: seq<StatusCallEvidence>
  )
  {
    if backupMode == Schema.BackupOff || backupMode == Schema.BackupSimple then
      |calls| == 0
    else if backupMode == Schema.BackupExisting then
      |calls| >= 1 &&
      StatusRequest(calls[0], fs, NumberedBackupPathSpec(target, 1), false) &&
      (if !calls[0].ok then
         |calls| == 1
       else
         |calls| >= 2 &&
         (forall i: nat | 1 <= i < |calls| ::
            StatusRequest(calls[i], fs, NumberedBackupPathSpec(target, i), false)) &&
         (forall i: nat | 1 <= i + 1 < |calls| :: calls[i].ok) &&
         !calls[|calls| - 1].ok)
    else
      |calls| >= 1 &&
      (forall i: nat | i < |calls| ::
        StatusRequest(calls[i], fs, NumberedBackupPathSpec(target, i + 1), false)) &&
      (forall i: nat | i + 1 < |calls| :: calls[i].ok) &&
      !calls[|calls| - 1].ok
  }

  ghost predicate ObservedUpdateDecision(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>
  )
  {
    if cmd.updateMode == Schema.UpdateOlder &&
       cmd.overwriteMode != Schema.OverwriteSkip &&
       |calls| >= 2 && calls[0].ok && calls[1].ok &&
       !SameFileMustBeRejected(cmd, fs, cwd, source, target) then
      |calls| >= 4 &&
      StatusRequest(calls[2], fs, source, false) &&
      StatusRequest(calls[3], fs, target, false) &&
      calls[2].ok && calls[3].ok &&
      (if !SourceNewerSpec(
            calls[2].status.times.mtimeSec,
            calls[2].status.times.mtimeNsec,
            calls[3].status.times.mtimeSec,
            calls[3].status.times.mtimeNsec
          ) then
         afterFs == fs &&
         outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
       else
         ExistingTargetRenameEffectRelation(
           source, target, cmd, fs, cwd, afterFs, outcome
         ))
    else
      true
  }

  ghost predicate MoveStatusShapeWitness(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    sourceParent: string,
    targetParent: string,
    sourceLeaf: string,
    targetLeaf: string,
    resolveOk: bool,
    resolvedSource: string,
    resolveErr: int,
    afterEntries: nat
  )
  {
    |calls| >= 6 &&
    calls[2].ok && calls[3].ok &&
    StatusRequest(calls[2], fs, source, false) &&
    StatusRequest(calls[3], fs, target, false) &&
    Dirname.DirnameRelation(source, sourceParent) &&
    Dirname.DirnameRelation(target, targetParent) &&
    Basename.BasenameRelation(source, sourceLeaf) &&
    Basename.BasenameRelation(target, targetLeaf) &&
    StatusRequest(calls[4], fs, sourceParent, false) &&
    StatusRequest(calls[5], fs, targetParent, false) &&
    (if calls[2].status.kind == BenchWorld.SymlinkKind then
       IOContract.ResolvePathIdentityContractFields(
         fs, cwd, source, resolveOk, resolvedSource, resolveErr
       ) &&
       |calls| >= 7 &&
       StatusRequest(calls[6], fs, source, true) &&
       (if resolveOk then
          exists referentParent: string ::
            afterEntries == 8 && |calls| >= 8 &&
            Dirname.DirnameRelation(resolvedSource, referentParent) &&
            StatusRequest(calls[7], fs, referentParent, false)
        else
          afterEntries == 7)
     else
       afterEntries == 6) &&
    (if SameFileMustBeRejected(cmd, fs, cwd, source, target) ||
        (cmd.updateMode == Schema.UpdateOlder &&
         !SourceNewerSpec(
           calls[2].status.times.mtimeSec,
           calls[2].status.times.mtimeNsec,
           calls[3].status.times.mtimeSec,
           calls[3].status.times.mtimeNsec
         )) then
       |calls| == afterEntries
     else
       var collisionNeeded :=
         (cmd.backupMode == Schema.BackupSimple ||
          cmd.backupMode == Schema.BackupExisting) &&
         sourceLeaf == targetLeaf + cmd.backupSuffix;
       var afterCollision := afterEntries +
         (if collisionNeeded then 1 else 0);
       afterCollision <= |calls| &&
       (collisionNeeded ==>
         StatusRequest(
           calls[afterEntries], fs,
           SimpleBackupPathSpec(target, cmd.backupSuffix), true
         )) &&
       (if collisionNeeded && calls[afterEntries].ok &&
           calls[afterEntries].status.hostKey == calls[2].status.hostKey then
          |calls| == afterCollision
        else
          BackupStatusSuffix(cmd.backupMode, fs, target, calls[afterCollision..])))
  }

  ghost predicate MoveStatusShape(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>
  )
  {
    |calls| >= 1 &&
    StatusRequest(calls[0], fs, source, false) &&
    (if !calls[0].ok then
       |calls| == 1
     else
       |calls| >= 2 &&
       StatusRequest(calls[1], fs, target, false) &&
       (if !calls[1].ok || cmd.overwriteMode == Schema.OverwriteSkip ||
           cmd.updateMode == Schema.UpdateNone ||
           cmd.updateMode == Schema.UpdateNoneFail then
          |calls| == 2
        else
          exists sourceParent: string, targetParent: string,
                 sourceLeaf: string, targetLeaf: string,
                 resolveOk: bool, resolvedSource: string, resolveErr: int,
                 afterEntries: nat ::
            MoveStatusShapeWitness(
              cmd, fs, cwd, source, target, calls,
              sourceParent, targetParent, sourceLeaf, targetLeaf,
              resolveOk, resolvedSource, resolveErr, afterEntries
            )))
  }

  ghost function ConcatenateFragments(fragments: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |fragments|
  {
    if |fragments| == 0 then
      []
    else
      fragments[0] + ConcatenateFragments(fragments[1..])
  }

  ghost predicate NumberedBackupTargetSpecFromFields(preFs: BenchWorld.FileSystem, target: string, start: nat, backupPath: string)
  {
    start >= 1 &&
    exists index: nat, missErr: int ::
      index >= start &&
      backupPath == NumberedBackupPathSpec(target, index) &&
      IOContract.PathExistsContractFields(preFs, backupPath, false, false, missErr) &&
      forall j: nat | start <= j < index ::
        IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, j), false, true, 0)
  }

  ghost predicate NumberedBackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupPath: string)
  {
    NumberedBackupTargetSpecFromFields(preFs, target, 1, backupPath)
  }

  ghost predicate BackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupMode: Schema.BackupMode, suffix: string, backupPath: string)
  {
    if backupMode == Schema.BackupOff then
      backupPath == ""
    else if backupMode == Schema.BackupSimple then
      backupPath == SimpleBackupPathSpec(target, suffix)
    else if backupMode == Schema.BackupExisting then
      ((exists hitErr: int ::
          IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, 1), false, true, hitErr) &&
          NumberedBackupTargetSpecFields(preFs, target, backupPath)) ||
       (exists missErr: int ::
          IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, 1), false, false, missErr) &&
          backupPath == SimpleBackupPathSpec(target, suffix)))
    else
      NumberedBackupTargetSpecFields(preFs, target, backupPath)
  }

  ghost predicate BackupWouldDestroySource(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string
  )
  {
    (cmd.backupMode == Schema.BackupSimple ||
     cmd.backupMode == Schema.BackupExisting) &&
    (exists sourceLeaf: string, targetLeaf: string ::
       Basename.BasenameRelation(source, sourceLeaf) &&
       Basename.BasenameRelation(target, targetLeaf) &&
       sourceLeaf == targetLeaf + cmd.backupSuffix) &&
    exists
      resolvedSource: BenchWorld.Path,
      resolvedBackup: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(
          fs, source, false
        ) == Result.Ok(resolvedSource) &&
        IOContract.ResolvePathForMetadataFields(
          fs, SimpleBackupPathSpec(target, cmd.backupSuffix), true
        ) == Result.Ok(resolvedBackup) &&
        BenchWorld.InodeSameObject(
          fs, resolvedSource, resolvedBackup
        )
  }

  ghost predicate RenameEffectRelation(
    source: string,
    target: string,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    (backupPath == "" &&
     IOContract.RenamePathContractFields(beforeFs, source, target, true, 0, afterFs) &&
     outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", verbose, debug), [], false)) ||
    (backupPath == "" &&
     exists
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             ),
             sourceIsDir && IOContract.PathExistsContractFields(
               beforeFs, target, false, true, 0)
           ),
           true
         )) ||
    (backupPath != "" &&
     exists backupErr: int ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, false, backupErr, afterFs) &&
       outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, backupErr), true)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
       IOContract.RenamePathContractFields(backupFs, source, target, true, 0, afterFs) &&
       outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, verbose, debug), [], false)) ||
    (backupPath != "" &&
     exists
       backupFs: BenchWorld.FileSystem,
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
         IOContract.RenamePathContractFields(backupFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             ),
             false
           ),
           true
         ))
  }

  ghost predicate ExistingTargetRenameEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    if BackupWouldDestroySource(cmd, beforeFs, source, target) then
      afterFs == beforeFs &&
      outcome == MoveOutcome(
        [],
        BackupWouldDestroySourceMessageSpec(source, target),
        true
      )
    else if cmd.backupMode == Schema.BackupOff then
      RenameEffectRelation(
        source, target, "", cmd.verbose, cmd.debug,
        beforeFs, preCwd, afterFs, outcome
      )
    else
      exists backupPath: string ::
        BackupTargetSpecFields(
          beforeFs, target, cmd.backupMode, cmd.backupSuffix, backupPath
        ) &&
        RenameEffectRelation(
          source, target, backupPath, cmd.verbose, cmd.debug,
          beforeFs, preCwd, afterFs, outcome
        )
  }

  ghost predicate MoveEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
      IOContract.IsDirectoryStrictContractFields(
        beforeFs, source, false, sourceOk, sourceIsDir, sourceErr
      ) &&
      if !sourceOk then
        afterFs == beforeFs &&
        outcome == MoveOutcome(
          [], SourceStatFailureMessageSpec(source, sourceErr), true
        )
      else
        exists found: bool, existsErr: int ::
          IOContract.PathExistsContractFields(
            beforeFs, target, false, found, existsErr
          ) &&
          if !found then
            RenameEffectRelation(
              source, target, "", cmd.verbose, cmd.debug,
              beforeFs, preCwd, afterFs, outcome
            )
          else if cmd.overwriteMode == Schema.OverwriteSkip then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNone then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNoneFail then
            afterFs == beforeFs &&
            outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
          else
            exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, beforeFs, preCwd, source, target, decision
              ) &&
              if decision == RejectSameFile then
                afterFs == beforeFs &&
                outcome == MoveOutcome(
                  [], SameFileMessageSpec(source, target), true
                )
              else if cmd.updateMode == Schema.UpdateOlder then
                exists sourceMtimeSec: int, sourceMtimeNsec: int,
                       targetMtimeSec: int, targetMtimeNsec: int ::
                  if !SourceNewerSpec(
                       sourceMtimeSec, sourceMtimeNsec,
                       targetMtimeSec, targetMtimeNsec
                     ) then
                    afterFs == beforeFs &&
                    outcome == MoveOutcome(
                      SkipStdoutSpec(target, cmd.debug), [], false
                    )
                  else
                    ExistingTargetRenameEffectRelation(
                      source, target, cmd, beforeFs, preCwd, afterFs, outcome
                    )
              else
                ExistingTargetRenameEffectRelation(
                  source, target, cmd, beforeFs, preCwd, afterFs, outcome
                )
  }

  ghost predicate BatchMoveWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
  {
    |fsBounds| == |sources| + 1 &&
    |outcomes| == |sources| &&
    |stdoutFragments| == |sources| &&
    |stderrFragments| == |sources| &&
    fsBounds[0] == beforeFs &&
    fsBounds[|fsBounds| - 1] == afterFs &&
    (forall i: nat | i < |sources| ::
       var normalizedSource :=
         NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       MoveEffectRelation(
         normalizedSource,
         TargetInDirectorySpec(directory, normalizedSource),
         cmd,
         fsBounds[i],
         preCwd,
         fsBounds[i + 1],
         outcomes[i]
       ) &&
       stdoutFragments[i] == outcomes[i].stdoutFragment &&
       stderrFragments[i] == outcomes[i].stderrFragment) &&
    ConcatenateFragments(stdoutFragments) == out &&
    ConcatenateFragments(stderrFragments) == err &&
    (hadError <==>
     exists i: nat :: i < |outcomes| && outcomes[i].failed)
  }

  ghost predicate BatchMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes
  )
  {
    exists
      fsBounds: seq<BenchWorld.FileSystem>,
      outcomes: seq<MoveOutcome>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>
      ::
        BatchMoveWitnessRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err,
          fsBounds, outcomes, stdoutFragments, stderrFragments
        )
  }

  ghost predicate TargetDirectoryCheckSpecFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    exists statOk: bool, isDir: bool, statErr: int ::
      IOContract.IsDirectoryContractFields(
        preFs, directory, true, statOk, isDir, statErr
      ) &&
      ok == (statOk && isDir) &&
      err == TargetDirectoryErrSpec(statOk, isDir, statErr)
  }

  ghost predicate CandidateRunIntoDirectoryFields(
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
    (exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
       TargetDirectoryCheckSpecFields(directory, beforeFs, true, 0) &&
       BatchMoveRelation(
         sources, directory, cmd,
         beforeFs, preCwd, afterFs, hadError, out, err
       ) &&
       exit == (if hadError then 1 else 0) &&
       stdout2 == preStdout + out &&
       stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSpecFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate CandidateRunTwoOperandFields(
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
      NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists outcome: MoveOutcome ::
        MoveEffectRelation(
          source, destination, cmd,
          beforeFs, preCwd, afterFs, outcome
        ) &&
        exit == (if outcome.failed then 1 else 0) &&
        stdout2 == preStdout + outcome.stdoutFragment &&
        stderr2 == preStderr + outcome.stderrFragment
    else
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, true, directoryErr
         ) &&
         BatchMoveRelation(
           [cmd.operands[0]], destination, cmd,
           beforeFs, preCwd, afterFs, outcome.failed,
           outcome.stdoutFragment, outcome.stderrFragment
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment)
  }

  ghost predicate CandidateSpecFields(
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
      io.stderr() ==
      preStderr + InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() ==
      preStderr + InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + HelpTextSpec() &&
      io.stderr() == preStderr
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + VersionTextSpec() &&
      io.stderr() == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      CandidateRunIntoDirectoryFields(
        cmd.operands, cmd.targetDirectory, true, cmd,
        preFs, preCwd, io.fs(),
        preStdout, preStderr, io.stdout(), io.stderr(), exit
      )
    else if |cmd.operands| == 1 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() ==
      preStderr + MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      CandidateRunTwoOperandFields(
        cmd, preFs, preCwd, io.fs(),
        preStdout, preStderr, io.stdout(), io.stderr(), exit
      )
    else
      CandidateRunIntoDirectoryFields(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        io.stdout(),
        io.stderr(),
        exit
      )
  }

  ghost predicate ObservedStepRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    observations: BenchWorld.StatusTimeObservations,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    MoveEffectRelation(source, target, cmd, beforeFs, cwd, afterFs, outcome) &&
    MoveStatusShape(cmd, beforeFs, cwd, source, target, calls) &&
    ObservedUpdateDecision(
      cmd, beforeFs, cwd, source, target, afterFs, outcome, calls
    )
  }

  ghost predicate ObservedBatchRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    observations: BenchWorld.StatusTimeObservations,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    exists fsBounds: seq<BenchWorld.FileSystem>,
           outcomes: seq<MoveOutcome>,
           stdoutFragments: seq<BenchWorld.Bytes>,
           stderrFragments: seq<BenchWorld.Bytes>,
           statusBounds: seq<nat> ::
      BatchMoveWitnessRelation(
        sources, directory, cmd, beforeFs, cwd, afterFs,
        hadError, out, err,
        fsBounds, outcomes, stdoutFragments, stderrFragments
      ) &&
      |statusBounds| == |sources| + 1 &&
      statusBounds[0] == firstStatus &&
      statusBounds[|sources|] == afterStatus &&
      (forall i: nat {:trigger statusBounds[i]} | i < |sources| ::
        firstStatus <= statusBounds[i] <= statusBounds[i + 1] <= afterStatus &&
        ObservedStepRelation(
          NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
          TargetInDirectorySpec(
            directory,
            NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)
          ),
          cmd,
          fsBounds[i], cwd, fsBounds[i + 1], outcomes[i],
          observations, statusBounds[i], statusBounds[i + 1],
          calls[statusBounds[i] - firstStatus ..
                statusBounds[i + 1] - firstStatus]
        ))
  }

  ghost predicate ObservedStatusSpec(
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
    calls: seq<StatusCallEvidence>
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
       |calls| == 0
     else if cmd.targetDirectory != "" then
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, cmd.targetDirectory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1)
     else if |cmd.operands| == 2 then
       var source := NormalizeSourceSpec(
         cmd.operands[0], cmd.stripTrailingSlashes
       );
       var destination := cmd.operands[1];
       (if cmd.noTargetDirectory then
          exists outcome: MoveOutcome ::
            ObservedStepRelation(
              source, destination, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus, afterStatus, calls
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment
        else
          |calls| >= 1 &&
          StatusRequest(calls[0], beforeFs, destination, true) &&
          var target :=
            if calls[0].ok &&
               calls[0].status.kind == BenchWorld.DirectoryKind then
              TargetInDirectorySpec(destination, source)
            else destination;
          exists outcome: MoveOutcome ::
            ObservedStepRelation(
              source, target, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment)
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, directory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1))
  }

  twostate predicate Spec(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    CandidateSpecFields(
      raw,
      old(io.fs()),
      old(io.cwd()),
      old(io.stdout()),
      old(io.stderr()),
      io,
      exit
    ) &&
    exists calls: seq<StatusCallEvidence> ::
      ObservedStatusSpec(
        raw, old(io.fs()), old(io.cwd()), io.fs(),
        old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit,
        io.statusObservations(), old(io.statusCursor()), io.statusCursor(), calls
      )
  }
}
