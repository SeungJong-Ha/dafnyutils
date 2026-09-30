include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "LnSchema.dfy"

module LnSpec {
  import BenchIO
  import IOContract
  import BenchWorld
  import Schema = LnSchema
  import SE = StringEscaping
  import Utf8 = Utf8Semantics




  function ErrnoTextSpec(err: int): string
  {
    if err == 2 then
      "No such file or directory"
    else if err == 13 then
      "Permission denied"
    else if err == 17 then
      "File exists"
    else if err == 20 then
      "Not a directory"
    else if err == 21 then
      "Is a directory"
    else if err == 22 then
      "Invalid argument"
    else if err == 36 then
      "File name too long"
    else if err == 40 then
      "Too many levels of symbolic links"
    else
      "unknown error"
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: ln [OPTION]... TARGET LINK_NAME\n"
    + "Create a link named LINK_NAME to TARGET.\n"
    + "\n"
    + "With one TARGET, create a link in the current directory.\n"
    + "\n"
    + "  -s, --symbolic\n"
    + "         make symbolic links instead of hard links\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/ln>\n"
    + "or available locally via: info '(coreutils) ln invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "ln (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker and David MacKenzie.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "ln: missing file operand\nTry 'ln --help' for more information.\n"
  }

  function UnsupportedHardLinkMessageSpec(): BenchWorld.Bytes
  {
    "ln: hard links are outside this benchmark; use -s/--symbolic\n"
  }

  function FailedAccessMessageSpec(source: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ln: failed to access " + SE.SpecQuoteAfBytes(Utf8.Encode(source)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function HardDirectoryMessageSpec(source: BenchWorld.Path): BenchWorld.Bytes
  {
    "ln: " + SE.SpecQuoteFBytes(Utf8.Encode(source)) +
    ": hard link not allowed for directory\n"
  }

  function CreateHardLinkErrorMessageSpec(
    source: BenchWorld.Path, linkName: BenchWorld.Path, err: int
  ): BenchWorld.Bytes
  {
    "ln: " +
    (if err == 31 then
       "failed to create hard link to " + SE.SpecQuoteAfBytes(Utf8.Encode(source))
     else if err == 17 || err == 28 || err == 122 || err == 30 then
       "failed to create hard link " + SE.SpecQuoteAfBytes(Utf8.Encode(linkName))
     else
       "failed to create hard link " + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
       " => " + SE.SpecQuoteAfBytes(Utf8.Encode(source))) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function TrimTrailingSlashes(path: string): string
    decreases |path|
  {
    if |path| > 0 && path[|path| - 1] == '/' then
      TrimTrailingSlashes(path[..|path| - 1])
    else
      path
  }

  function LastSlash(path: string): int
    ensures -1 <= LastSlash(path) < |path|
    decreases |path|
  {
    if |path| == 0 then -1
    else if path[|path| - 1] == '/' then |path| - 1
    else LastSlash(path[..|path| - 1])
  }

  function BaseName(path: string): string
  {
    var trimmed := TrimTrailingSlashes(path);
    if |trimmed| == 0 then (if |path| == 0 then "" else "/")
    else trimmed[LastSlash(trimmed) + 1..]
  }

  function InDirectory(directory: string, source: string): string
  {
    directory + (if |directory| > 0 && directory[|directory| - 1] == '/' then "" else "/") +
    BaseName(source)
  }

  function LinkDestination(
    fs: BenchWorld.FileSystem, operands: seq<string>
  ): string
    requires 1 <= |operands| <= 2
  {
    if |operands| == 1 then InDirectory(".", operands[0])
    else if operands[0] == "" then operands[1]
    else if LinkNameIsDirectoryFs(fs, operands[1]) then InDirectory(operands[1], operands[0])
    else operands[1]
  }

  function UnsupportedTargetDirectoryMessageSpec(): BenchWorld.Bytes
  {
    "ln: target-directory link modes are outside this benchmark; use explicit SOURCE LINK_NAME\n"
  }

  function CreateSymlinkErrorMessageSpec(
    linkName: BenchWorld.Path, source: BenchWorld.Path, err: int
  ): BenchWorld.Bytes
  {
    "ln: failed to create symbolic link " + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
    (if source == "" then " -> " + SE.SpecQuoteAfBytes(Utf8.Encode(source)) else "") +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function TargetDirectoryErrorMessageSpec(target: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ln: target " + SE.SpecQuoteAfBytes(Utf8.Encode(target)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  opaque ghost predicate LinkStepRelation(
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
        diagnostic == (if ok then [] else CreateSymlinkErrorMessageSpec(destination, source, err)) &&
        success == ok
    else
      exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
        IOContract.IsDirectoryStrictContractFields(
          beforeFs, source, false, sourceOk, sourceIsDir, sourceErr) &&
        (if !sourceOk then
           afterFs == beforeFs &&
           diagnostic == FailedAccessMessageSpec(source, sourceErr) &&
           !success
         else if sourceIsDir then
           afterFs == beforeFs &&
           diagnostic == HardDirectoryMessageSpec(source) &&
           !success
         else
           exists ok: bool, err: int ::
             IOContract.CreateHardLinkSpec(
               beforeFs, now, trustedFilesystem, afterFs,
               source, destination, ok, err) &&
             diagnostic == (if ok then [] else
               CreateHardLinkErrorMessageSpec(source, destination, err)) &&
             success == ok)
  }

  opaque ghost predicate LinkBatchRelation(
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
          LinkStepRelation(
            states[i], states[i + 1], now, trustedFilesystem,
            sources[i], InDirectory(directory, sources[i]), symbolic,
            pieces[i], stepResults[i]) &&
          diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
          results[i + 1] == (results[i] && stepResults[i]))
  }

  function LinkNameIsDirectoryFs(fs: BenchWorld.FileSystem, linkName: BenchWorld.Path): bool
  {
    match IOContract.ResolvePathForMetadataFields(fs, linkName, true)
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      (match BenchWorld.FsNodeAt(fs, resolved)
       case Directory(_, _, _) => true
       case _ => false)
    case Err(_) => false
  }

  twostate predicate Spec(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    else if |cmd.operands| > 2 then
      var target := cmd.operands[|cmd.operands| - 1];
      io.stdout() == old(io.stdout()) &&
      (exists targetOk: bool, targetIsDir: bool, targetErr: int ::
        IOContract.IsDirectoryStrictContractFields(
          old(io.fs()), target, true, targetOk, targetIsDir, targetErr) &&
        (if !(targetOk && targetIsDir) then
           io.fs() == old(io.fs()) &&
           io.stderr() == old(io.stderr()) +
             TargetDirectoryErrorMessageSpec(target, if targetOk then 20 else targetErr) &&
           exit == 1
         else
           exists diagnostic: BenchWorld.Bytes, success: bool
             {:trigger LinkBatchRelation(old(io.fs()), io.fs(), old(io.now()),
               old(io.trustedFilesystem()), cmd.operands[..|cmd.operands| - 1],
               target, cmd.symbolic, diagnostic, success)} ::
             LinkBatchRelation(
               old(io.fs()), io.fs(), old(io.now()), old(io.trustedFilesystem()),
               cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
               diagnostic, success) &&
             io.stderr() == old(io.stderr()) + diagnostic &&
             exit == (if success then 0 else 1)))
    else
      var source := cmd.operands[0];
      var destination := LinkDestination(old(io.fs()), cmd.operands);
      io.stdout() == old(io.stdout()) &&
      (if cmd.symbolic then
         exists ok: bool, err: int ::
           IOContract.CreateSymlinkContractFields(
             old(io.fs()), old(io.now()), destination, source, ok, err, io.fs()) &&
           io.stderr() == old(io.stderr()) +
             (if ok then [] else CreateSymlinkErrorMessageSpec(destination, source, err)) &&
           exit == (if ok then 0 else 1)
       else
         exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
           IOContract.IsDirectoryStrictContractFields(
             old(io.fs()), source, false, sourceOk, sourceIsDir, sourceErr) &&
           (if !sourceOk then
              io.fs() == old(io.fs()) &&
              io.stderr() == old(io.stderr()) + FailedAccessMessageSpec(source, sourceErr) &&
              exit == 1
            else if sourceIsDir then
              io.fs() == old(io.fs()) &&
              io.stderr() == old(io.stderr()) + HardDirectoryMessageSpec(source) &&
              exit == 1
            else
              exists ok: bool, err: int ::
                IOContract.CreateHardLinkSpec(
                  old(io.fs()), old(io.now()), old(io.trustedFilesystem()),
                  io.fs(), source, destination, ok, err) &&
                io.stderr() == old(io.stderr()) +
                  (if ok then [] else CreateHardLinkErrorMessageSpec(source, destination, err)) &&
                exit == (if ok then 0 else 1)))
  }
}
