include "UnlinkSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "../../core/CliModel.dfy"

module UnlinkSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = UnlinkSchema
  import Utf8 = Utf8Semantics
  import CliModel
  import C = IOContract

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: unlink FILE\n"
    + "  or:  unlink OPTION\n"
    + "Call the unlink function to remove the specified FILE.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/unlink>\n"
    + "or available locally via: info '(coreutils) unlink invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "unlink (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Michael Stone.\n"
  }


  function LongOptionName(token: string): string
  {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var abbreviation := name[2..];
      if CliModel.HasPrefix("help", abbreviation) then "--help"
      else if CliModel.HasPrefix("version", abbreviation) then "--version"
      else name
    else name
  }

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    var text := if err.kind == CliTypes.UnknownOption then
        if |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-' then
          "unlink: unrecognized option '" + err.rawToken + "'\n" +
          "Try 'unlink --help' for more information.\n"
        else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
          "unlink: invalid option -- '" + [err.rawToken[1]] + "'\n" +
          "Try 'unlink --help' for more information.\n"
        else
          "unlink: invalid option\nTry 'unlink --help' for more information.\n"
      else if err.kind == CliTypes.UnexpectedValue then
        "unlink: option '" + LongOptionName(err.rawToken) +
        "' doesn't allow an argument\n" +
        "Try 'unlink --help' for more information.\n"
      else if err.kind == CliTypes.Ambiguous then
        "unlink: option '" + err.rawToken + "' is ambiguous\n" +
        "Try 'unlink --help' for more information.\n"
      else
        "unlink: " +
        (if err.kind == CliTypes.MissingValue
        then "missing option value"
        else "parse error") +
        " at token '" + err.rawToken + "'\n";
    Utf8.Encode(text)
  }

  twostate predicate UnlinkResult(
    io: BenchIO.IO,
    path: BenchWorld.Path,
    ok: bool,
    err: int
  )
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion
  {
    C.UnlinkPathSpec(
      old(io.fs()),
      old(io.now()),
      old(io.trustedFilesystem()),
      io.fs(),
      path,
      ok,
      err
    )
  }

  function MissingOperandText(): BenchWorld.Bytes
  {
    "unlink: missing operand\n"
    + "Try 'unlink --help' for more information.\n"
  }

  function ExtraOperandText(quotedOperand: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "unlink: extra operand " + quotedOperand + "\n"
    + "Try 'unlink --help' for more information.\n"
  }

  function CannotUnlinkText(
    quotedPath: BenchWorld.Bytes,
    reason: string
  ): BenchWorld.Bytes
  {
    "unlink: cannot unlink " + quotedPath + ": "
    + Utf8.Encode(reason) + "\n"
  }

  twostate predicate Spec(raw: Schema.UnlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
          ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandText() &&
      exit == 1
    else
      exists ok: bool, err: int ::
        UnlinkResult(io, raw.operands[0], ok, err) &&
        io.stdout() == old(io.stdout()) &&
        (if ok then
          io.stderr() == old(io.stderr()) && exit == 0
        else
          io.stderr() == old(io.stderr()) +
            CannotUnlinkText(C.QuoteafPathResult(raw.operands[0]), C.CLocaleErrnoTextResult(err)) &&
          exit == 1)
  }
}
