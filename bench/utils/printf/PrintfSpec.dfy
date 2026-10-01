include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/StringEscaping.dfy"
include "PrintfSchema.dfy"

module PrintfSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = PrintfSchema
  import SE = StringEscaping




  function HelpText(): BenchWorld.Bytes
  {
    "Usage: printf FORMAT [ARGUMENT]...\n"
    + "  or:  printf OPTION\n"
    + "Print ARGUMENT(s) according to FORMAT, or execute according to OPTION:\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "FORMAT controls the output as in C printf.  Interpreted sequences are:\n"
    + "\n"
    + "  \\\"      double quote\n"
    + "  \\\\      backslash\n"
    + "  \\a      alert (BEL)\n"
    + "  \\b      backspace\n"
    + "  \\c      produce no further output\n"
    + "  \\e      escape\n"
    + "  \\f      form feed\n"
    + "  \\n      new line\n"
    + "  \\r      carriage return\n"
    + "  \\t      horizontal tab\n"
    + "  \\v      vertical tab\n"
    + "  \\NNN    byte with octal value NNN (1 to 3 digits)\n"
    + "  \\xHH    byte with hexadecimal value HH (1 to 2 digits)\n"
    + "  \\uHHHH  Unicode (ISO/IEC 10646) character with hex value HHHH (4 digits)\n"
    + "  \\UHHHHHHHH  Unicode character with hex value HHHHHHHH (8 digits)\n"
    + "  %%      a single %\n"
    + "  %b      ARGUMENT as a string with '\\' escapes interpreted,\n"
    + "          except that octal escapes should have a leading 0 like \\0NNN\n"
    + "  %q      ARGUMENT is printed in a format that can be reused as shell input,\n"
    + "          escaping non-printable characters with the POSIX $'' syntax\n"
    + "\n"
    + "and all C format specifications ending with one of diouxXfeEgGcs, with\n"
    + "ARGUMENTs converted to proper type first.  Variable widths are handled.\n"
    + "\n"
    + "Your shell may have its own version of printf, which usually supersedes\n"
    + "the version described here.  Please refer to your shell's documentation\n"
    + "for details about the options it supports.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/printf>\n"
    + "or available locally via: info '(coreutils) printf invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "printf (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function MissingOperandMessage(): BenchWorld.Bytes
  {
    "printf: missing operand\nTry 'printf --help' for more information.\n"
  }

  function UnsupportedFormatMessage(): BenchWorld.Bytes
  {
    "printf: unsupported format in verified subset\n"
  }

  function ExcessArgumentsWarning(arg: string): BenchWorld.Bytes
  {
    "printf: warning: ignoring excess arguments, starting with " +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(arg)) + "\n"
  }

  function RequestExcessWarning(raw: Schema.PrintfCmdRaw): BenchWorld.Bytes
  {
    match raw.excessAfterRequest
    case Some(arg) => ExcessArgumentsWarning(arg)
    case None => []
  }

  datatype FormatFragment = FormatFragment(end: nat, afterArg: nat, output: BenchWorld.Bytes)
  datatype FragmentPlan = NoFragment | OneFragment(fragment: FormatFragment) |
    StopFragment(status: int, error: BenchWorld.Bytes)

  function IsHexDigit(c: char): bool
  {
    '0' <= c <= '9' || 'a' <= c <= 'f' || 'A' <= c <= 'F'
  }

  function HexDigitValue(c: char): nat
  {
    if '0' <= c <= '9' then c as int - '0' as int
    else if 'a' <= c <= 'f' then c as int - 'a' as int + 10
    else if 'A' <= c <= 'F' then c as int - 'A' as int + 10
    else 0
  }

  function OctalCount(format: string, start: nat): nat
    requires start <= |format|
    ensures start + OctalCount(format, start) <= |format|
  {
    if start == |format| || !BenchWorld.IsOctalDigit(format[start]) then 0
    else if start + 1 == |format| || !BenchWorld.IsOctalDigit(format[start + 1]) then 1
    else if start + 2 == |format| || !BenchWorld.IsOctalDigit(format[start + 2]) then 2
    else 3
  }

  function HexCount(format: string, start: nat): nat
    requires start <= |format|
    ensures start + HexCount(format, start) <= |format|
  {
    if start == |format| || !IsHexDigit(format[start]) then 0
    else if start + 1 == |format| || !IsHexDigit(format[start + 1]) then 1
    else 2
  }

  predicate HexSpan(format: string, start: nat, count: nat)
    decreases count
  {
    if count == 0 then start <= |format|
    else start + count <= |format| &&
         IsHexDigit(format[start + count - 1]) && HexSpan(format, start, count - 1)
  }

  function OctalValue(format: string, start: nat, count: nat): nat
    requires start + count <= |format|
    decreases count
  {
    if count == 0 then 0
    else OctalValue(format, start, count - 1) * 8 +
         (if BenchWorld.IsOctalDigit(format[start + count - 1])
          then BenchWorld.CharToDigit(format[start + count - 1]) else 0)
  }

  function HexValue(format: string, start: nat, count: nat): nat
    requires start + count <= |format|
    decreases count
  {
    if count == 0 then 0
    else HexValue(format, start, count - 1) * 16 +
         HexDigitValue(format[start + count - 1])
  }

  function HexText(value: nat, width: nat, upper: bool): BenchWorld.Bytes
    decreases width
  {
    if width == 0 then []
    else
      var digit := value % 16;
      HexText(value / 16, width - 1, upper) +
      [((if digit < 10 then '0' as int + digit
         else (if upper then 'A' as int else 'a' as int) + digit - 10) as char)]
  }

  function UnicodeBytes(value: nat): BenchWorld.Bytes
  {
    if value < 128 then [value as char]
    else if value < 0x10000 then "\\u" + HexText(value, 4, true)
    else "\\U" + HexText(value, 8, true)
  }

  function InvalidUnicodeMessage(value: nat, upper: bool): BenchWorld.Bytes
  {
    "printf: invalid universal character name \\" +
    (if upper then "U" + HexText(value, 8, false)
     else "u" + HexText(value, 4, false)) + "\n"
  }

  function MissingHexMessage(): BenchWorld.Bytes
  {
    "printf: missing hexadecimal number in escape\n"
  }

  ghost predicate FormatFragmentRelation(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat,
    end: nat,
    afterArg: nat,
    output: BenchWorld.Bytes
  )
  {
    start < |format| &&
    nextArg <= |args| &&
    if format[start] == '\\' then
      afterArg == nextArg &&
      if start + 1 == |format| then
        end == start + 1 && output == ['\\']
      else
        var escaped := format[start + 1];
        if escaped == 'a' then end == start + 2 && output == [7 as char]
        else if escaped == 'b' then end == start + 2 && output == [8 as char]
        else if escaped == 'e' then end == start + 2 && output == [27 as char]
        else if escaped == 'f' then end == start + 2 && output == [12 as char]
        else if escaped == 'n' then end == start + 2 && output == ['\n']
        else if escaped == 'r' then end == start + 2 && output == ['\r']
        else if escaped == 't' then end == start + 2 && output == ['\t']
        else if escaped == 'v' then end == start + 2 && output == [11 as char]
        else if escaped == '\\' then end == start + 2 && output == ['\\']
        else if escaped == '"' then end == start + 2 && output == ['"']
        else if BenchWorld.IsOctalDigit(escaped) then
          var digitStart := start + 1;
          var digits := OctalCount(format, digitStart);
          end == digitStart + digits &&
          output == [(OctalValue(format, digitStart, digits) % 256) as char]
        else if escaped == 'x' then
          var digits := HexCount(format, start + 2);
          digits > 0 && end == start + 2 + digits &&
          output == [(HexValue(format, start + 2, digits) % 256) as char]
        else if escaped == 'u' || escaped == 'U' then
          var width := if escaped == 'u' then 4 else 8;
          HexSpan(format, start + 2, width) &&
          var value := HexValue(format, start + 2, width);
          !(0xd800 <= value <= 0xdfff) &&
          end == start + 2 + width && output == UnicodeBytes(value)
        else
          escaped != 'c' && end == start + 2 &&
          output == ['\\'] + Utf8.EncodeChar(escaped)
    else if format[start] == '%' then
      start + 1 < |format| &&
      if format[start + 1] == '%' then
        end == start + 2 && afterArg == nextArg && output == ['%']
      else if format[start + 1] == 's' then
        end == start + 2 &&
        if nextArg < |args| then
          afterArg == nextArg + 1 && output == Utf8.Encode(args[nextArg])
        else
          afterArg == nextArg && output == []
      else
        false
    else
      end == start + 1 && afterArg == nextArg && output == Utf8.EncodeChar(format[start])
  }

  datatype FormatDerivation =
    FormatDone |
    FormatStep(fragment: FormatFragment, restOutput: BenchWorld.Bytes, rest: FormatDerivation) |
    FormatStop

  ghost predicate FormatStopRelation(format: string, start: nat, status: int, stderr: BenchWorld.Bytes)
  {
    start < |format| &&
    if format[start] == '\\' && start + 1 < |format| then
      var escaped := format[start + 1];
      if escaped == 'c' then status == 1 && stderr == []
      else if escaped == 'x' && HexCount(format, start + 2) == 0 then
        status == 2 && stderr == MissingHexMessage()
      else if escaped == 'u' || escaped == 'U' then
        var width := if escaped == 'u' then 4 else 8;
        if !HexSpan(format, start + 2, width) then
          status == 2 && stderr == MissingHexMessage()
        else
          var value := HexValue(format, start + 2, width);
          0xd800 <= value <= 0xdfff && status == 2 &&
          stderr == InvalidUnicodeMessage(value, escaped == 'U')
      else false
    else
      format[start] == '%' &&
      (start + 1 == |format| ||
       (format[start + 1] != '%' && format[start + 1] != 's')) &&
      status == 2 && stderr == UnsupportedFormatMessage()
  }

  ghost predicate FormatDerivationRelation(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat,
    used: nat,
    output: BenchWorld.Bytes,
    status: int,
    stderr: BenchWorld.Bytes,
    derivation: FormatDerivation
  )
    decreases derivation
  {
    start <= |format| &&
    startArg <= used <= |args| &&
    match derivation
    case FormatDone =>
      start == |format| && used == startArg && output == [] && status == 0 && stderr == []
    case FormatStep(fragment, restOutput, rest) =>
      FormatFragmentRelation(
        format, args, start, startArg,
        fragment.end, fragment.afterArg, fragment.output) &&
      output == fragment.output + restOutput &&
      FormatDerivationRelation(
        format, args, fragment.end, fragment.afterArg, used, restOutput, status, stderr, rest)
    case FormatStop =>
      used == startArg && output == [] && FormatStopRelation(format, start, status, stderr)
  }

  ghost predicate FormatPassRelation(
    format: string,
    args: seq<string>,
    startArg: nat,
    used: nat,
    output: BenchWorld.Bytes,
    status: int,
    stderr: BenchWorld.Bytes
  )
  {
    exists derivation: FormatDerivation ::
      FormatDerivationRelation(format, args, 0, startArg, used, output, status, stderr, derivation)
  }

  datatype RepeatedDerivation =
    RepeatedStop(used: nat, passOutput: BenchWorld.Bytes, passStatus: int, passError: BenchWorld.Bytes) |
    RepeatedDone(used: nat, passOutput: BenchWorld.Bytes) |
    RepeatedStep(nextArg: nat, passOutput: BenchWorld.Bytes,
                 restOutput: BenchWorld.Bytes, rest: RepeatedDerivation)

  ghost predicate RepeatedPassesFromRelation(
    format: string,
    args: seq<string>,
    startArg: nat,
    status: int,
    output: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    derivation: RepeatedDerivation
  )
    decreases derivation
  {
    match derivation
    case RepeatedStop(used, passOutput, passStatus, passError) =>
      (passStatus == 1 || passStatus == 2) &&
      FormatPassRelation(format, args, startArg, used, passOutput, passStatus, passError) &&
      status == passStatus && output == passOutput && stderr == passError
    case RepeatedDone(used, passOutput) =>
      FormatPassRelation(format, args, startArg, used, passOutput, 0, []) &&
      (used == startArg || used == |args|) && status == 0 && output == passOutput &&
      stderr == (if used == startArg && startArg < |args|
                 then ExcessArgumentsWarning(args[startArg]) else [])
    case RepeatedStep(nextArg, passOutput, restOutput, rest) =>
      startArg < nextArg <= |args| &&
      FormatPassRelation(format, args, startArg, nextArg, passOutput, 0, []) &&
      nextArg < |args| &&
      output == passOutput + restOutput &&
      RepeatedPassesFromRelation(format, args, nextArg, status, restOutput, stderr, rest)
  }

  ghost predicate RenderRelation(
    format: string,
    args: seq<string>,
    ok: bool,
    output: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes
  )
  {
    exists status: int, derivation: RepeatedDerivation ::
      (status == 0 || status == 1 || status == 2) &&
      ok == (status != 2) &&
      RepeatedPassesFromRelation(format, args, 0, status, output, stderr, derivation)
  }

  ghost predicate EvaluationRelation(
    raw: Schema.PrintfCmdRaw,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    code: int
  )
  {
    if Schema.HelpSelected(raw) then
      stdout == HelpText() && stderr == RequestExcessWarning(raw) && code == 0
    else if Schema.VersionSelected(raw) then
      stdout == VersionText() && stderr == RequestExcessWarning(raw) && code == 0
    else if |raw.operands| == 0 then
      stdout == [] && stderr == MissingOperandMessage() && code == 1
    else
      (code == 0 || code == 1) &&
      RenderRelation(
        raw.operands[0], raw.operands[1..], code == 0, stdout, stderr
      )
  }

  twostate predicate Spec(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes ::
      EvaluationRelation(raw, stdout, stderr, exit) &&
      io.stdout() == old(io.stdout()) + stdout &&
      io.stderr() == old(io.stderr()) + stderr
  }
}
