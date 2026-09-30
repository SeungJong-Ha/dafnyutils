include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "TrSchema.dfy"

module TrSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping




  datatype TrMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeMissingOperand(message: BenchWorld.Bytes)
    | ModeExtraOperand(operand: string)
    | ModeUnsupportedSet(operand: string)
    | ModeEmptySet2

  datatype TrCmd = TrCmd(
    mode: TrMode,
    deleteSet: bool,
    squeeze: bool,
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    warnings: BenchWorld.Bytes
  )

  datatype SetDecode = SetOk(bytes: BenchWorld.Bytes) | SetUnsupported(operand: string)
  datatype ReverseRange = NoReverseRange |
    FoundReverseRange(first: BenchWorld.RawByte, last: BenchWorld.RawByte)

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tr [OPTION]... SET1 [SET2]\n"
    + "Translate, squeeze, and/or delete characters from standard input,\n"
    + "writing to standard output.\n"
    + "\n"
    + "  -d, --delete          delete characters in SET1\n"
    + "  -s, --squeeze-repeats replace repeated characters listed in the last SET\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "Benchmark note: literal UTF-8 bytes and ordered ASCII ranges like a-z\n"
    + "and escaped bytes are implemented; character classes, repeats, complements,\n"
    + "truncate mode and locale-dependent collation are deferred.\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tr (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jim Meyering.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "tr: missing operand\nTry 'tr --help' for more information.\n"
  }

  function MissingSet2MessageSpec(operand: string, deleteAndSqueeze: bool): BenchWorld.Bytes
  {
    "tr: missing operand after " + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if deleteAndSqueeze then
         "\nTwo strings must be given when both deleting and squeezing repeats.\n"
       else
         "\nTwo strings must be given when translating.\n") +
      "Try 'tr --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(operand: string, explainDeleteLimit: bool): BenchWorld.Bytes
  {
    "tr: extra operand " + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if explainDeleteLimit then
         "\nOnly one string may be given when deleting without squeezing repeats.\n"
       else
         "\n") +
      "Try 'tr --help' for more information.\n"
  }

  function UnsupportedSetMessageSpec(operand: string): BenchWorld.Bytes
  {
    match FirstReverseRangeFrom(operand, 0)
    case FoundReverseRange(first, last) =>
      "tr: range-endpoints of '" + DisplayRangeByte(first) + "-" +
      DisplayRangeByte(last) +
      "' are in reverse collating sequence order\n"
    case NoReverseRange =>
      "tr: unsupported set syntax '" + Utf8.Encode(operand) +
      "' in this benchmark\n"
  }

  function EmptySet2MessageSpec(): BenchWorld.Bytes
  {
    "tr: when not deleting, string2 must be non-empty in this benchmark\n"
  }

  function FirstReverseRangeFrom(text: string, i: nat): ReverseRange
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      NoReverseRange
    else
      var first := AtomBytes(text, i);
      var next := AtomNext(text, i);
      if next + 1 < |text| && text[next] == '-' && |first| == 1 then
        var last := AtomBytes(text, next + 1);
        if |last| == 1 && first[0] as int > last[0] as int then
          FoundReverseRange(first[0], last[0])
        else
          FirstReverseRangeFrom(text, next)
      else
        FirstReverseRangeFrom(text, next)
  }

  function DisplayRangeByte(ch: BenchWorld.RawByte): BenchWorld.Bytes
  {
    if ch as int < 32 || ch as int >= 127 then
      ['\\',
       ((('0' as int) + (ch as int / 64)) as char),
       ((('0' as int) + (ch as int / 8) % 8) as char),
       ((('0' as int) + (ch as int % 8)) as char)]
    else [ch]
  }

  function IsOctal(ch: char): bool
  {
    '0' <= ch <= '7'
  }

  function OctalValue(ch: char): int
    requires IsOctal(ch)
  {
    ch as int - '0' as int
  }

  function SimpleEscape(ch: char): char
  {
    if ch == 'a' then 7 as char
    else if ch == 'b' then 8 as char
    else if ch == 'f' then 12 as char
    else if ch == 'n' then '\n'
    else if ch == 'r' then '\r'
    else if ch == 't' then '\t'
    else if ch == 'v' then 11 as char
    else ch
  }

  function AtomNext(text: string, i: nat): nat
    requires i < |text|
    ensures i < AtomNext(text, i) <= |text|
  {
    if text[i] != '\\' || i + 1 == |text| then i + 1
    else if IsOctal(text[i + 1]) then
      if i + 2 < |text| && IsOctal(text[i + 2]) then
        if i + 3 < |text| && IsOctal(text[i + 3]) &&
           OctalValue(text[i + 1]) < 4 then i + 4
        else i + 3
      else i + 2
    else i + 2
  }

  function AtomBytes(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
  {
    if text[i] != '\\' then Utf8.EncodeChar(text[i])
    else if i + 1 == |text| then ['\\']
    else if IsOctal(text[i + 1]) then
      if i + 2 < |text| && IsOctal(text[i + 2]) then
        if i + 3 < |text| && IsOctal(text[i + 3]) &&
           OctalValue(text[i + 1]) < 4 then
          [((OctalValue(text[i + 1]) * 64 +
             OctalValue(text[i + 2]) * 8 +
             OctalValue(text[i + 3])) as char)]
        else
          [((OctalValue(text[i + 1]) * 8 +
             OctalValue(text[i + 2])) as char)]
      else [(OctalValue(text[i + 1]) as char)]
    else EscapeBytes(text[i + 1])
  }

  function AmbiguousOctalWarningSpec(text: string, i: nat): BenchWorld.Bytes
    requires i + 3 < |text|
  {
    "tr: warning: the ambiguous octal escape \\" +
    Utf8.Encode(text[i + 1..i + 4]) +
    " is being\n\tinterpreted as the 2-byte sequence \\0" +
    Utf8.Encode(text[i + 1..i + 3]) + ", " +
    Utf8.EncodeChar(text[i + 3]) + "\n"
  }

  function TrailingBackslashWarningSpec(): BenchWorld.Bytes
  {
    "tr: warning: an unescaped backslash at end of string is not portable\n"
  }

  function WarningAtSpec(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
  {
    if text[i] != '\\' then []
    else if i + 1 == |text| then TrailingBackslashWarningSpec()
    else if i + 3 < |text| && IsOctal(text[i + 1]) &&
            IsOctal(text[i + 2]) && IsOctal(text[i + 3]) &&
            OctalValue(text[i + 1]) >= 4 then
      AmbiguousOctalWarningSpec(text, i)
    else []
  }

  function EscapeBytes(ch: char): BenchWorld.Bytes
  {
    if ch == 'a' || ch == 'b' || ch == 'f' || ch == 'n' ||
       ch == 'r' || ch == 't' || ch == 'v' then
      [SimpleEscape(ch)]
    else
      Utf8.EncodeChar(ch)
  }

  // Ghost, so the adjacent-pair test can be the existential it actually is and
  // the single-character test can be plain membership. `ContainsCharFrom` is
  // gone entirely: it was sequence membership written as index recursion.
  ghost predicate ContainsPair(text: string, first: char, second: char)
  {
    exists k :: 0 <= k < |text| - 1 && text[k] == first && text[k + 1] == second
  }

  ghost predicate StartsUnsupportedConstruct(text: string)
  {
    |text| > 0 && text[0] == '[' && (
      (1 < |text| && text[1] == ':' && ContainsPair(text[2..], ':', ']')) ||
      (1 < |text| && text[1] == '=' && ContainsPair(text[2..], '=', ']')) ||
      (2 < |text| && text[2] == '*' && ']' in text[3..])
    )
  }

  // Formal specification gap: GNU bracket classes, repeats,
  // complement/truncate modes and locale-dependent collation are intentionally
  // rejected by this relation until modeled explicitly.
  ghost predicate RangeExpansion(lo: char, hi: char, bytes: BenchWorld.Bytes)
  {
    0 <= lo as int < 256 &&
    0 <= hi as int < 256 &&
    lo as int <= hi as int &&
    |bytes| == (hi as int) - (lo as int) + 1 &&
    forall i :: 0 <= i < |bytes| ==>
                  bytes[i] as int == lo as int + i
  }

  ghost predicate SetAtomRelation(
    text: string, lo: nat, hi: nat, bytes: BenchWorld.Bytes
  )
  {
    lo < |text| &&
    if text[lo] != '\\' then
      hi == lo + 1 && bytes == Utf8.EncodeChar(text[lo])
    else if lo + 1 == |text| then
      hi == lo + 1 && bytes == ['\\']
    else if IsOctal(text[lo + 1]) then
      if lo + 2 < |text| && IsOctal(text[lo + 2]) then
        if lo + 3 < |text| && IsOctal(text[lo + 3]) &&
           OctalValue(text[lo + 1]) < 4 then
          hi == lo + 4 &&
          bytes == [((OctalValue(text[lo + 1]) * 64 +
                      OctalValue(text[lo + 2]) * 8 +
                      OctalValue(text[lo + 3])) as char)]
        else
          hi == lo + 3 &&
          bytes == [((OctalValue(text[lo + 1]) * 8 +
                      OctalValue(text[lo + 2])) as char)]
      else
        hi == lo + 2 &&
        bytes == [(OctalValue(text[lo + 1]) as char)]
    else
      hi == lo + 2 && bytes == EscapeBytes(text[lo + 1])
  }

  opaque ghost predicate SetUnitRelation(
    text: string,
    lo: nat,
    hi: nat,
    bytes: BenchWorld.Bytes
  )
  {
    lo < |text| &&
    !StartsUnsupportedConstruct(text[lo..]) &&
    exists atomEnd: nat, atomBytes: BenchWorld.Bytes ::
      SetAtomRelation(text, lo, atomEnd, atomBytes) &&
      if atomEnd < |text| && text[atomEnd] == '-' &&
         atomEnd + 1 < |text| then
        exists endEnd: nat, endBytes: BenchWorld.Bytes
          {:trigger SetAtomRelation(text, atomEnd + 1, endEnd, endBytes)} ::
          SetAtomRelation(text, atomEnd + 1, endEnd, endBytes) &&
          |atomBytes| == 1 && |endBytes| == 1 &&
          hi == endEnd &&
          RangeExpansion(atomBytes[0], endBytes[0], bytes)
      else
        hi == atomEnd && bytes == atomBytes
  }

  ghost predicate SetPartitionFrom(
    text: string,
    start: nat,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |text| &&
    outputCuts[|outputCuts| - 1] == |bytes| &&
    forall i
      {:trigger inputCuts[i], inputCuts[i + 1]}
      {:trigger bytes[outputCuts[i]..outputCuts[i + 1]]} ::
      0 <= i && i + 1 < |inputCuts| ==>
        inputCuts[i] < inputCuts[i + 1] <= |text| &&
        outputCuts[i] <= outputCuts[i + 1] <= |bytes| &&
        SetUnitRelation(
          text,
          inputCuts[i],
          inputCuts[i + 1],
          bytes[outputCuts[i]..outputCuts[i + 1]]
        )
  }

  ghost predicate SetPartition(
    text: string,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    SetPartitionFrom(text, 0, bytes, inputCuts, outputCuts)
  }

  ghost predicate SetBytesRelation(text: string, bytes: BenchWorld.Bytes)
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      SetPartition(text, bytes, inputCuts, outputCuts)
  }

  ghost predicate WarningPartitionFrom(
    text: string,
    start: nat,
    warnings: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |text| &&
    outputCuts[|outputCuts| - 1] == |warnings| &&
    forall i
      {:trigger inputCuts[i], inputCuts[i + 1]}
      {:trigger warnings[outputCuts[i]..outputCuts[i + 1]]} ::
      0 <= i && i + 1 < |inputCuts| ==>
        inputCuts[i] < inputCuts[i + 1] <= |text| &&
        inputCuts[i + 1] == AtomNext(text, inputCuts[i]) &&
        outputCuts[i] <= outputCuts[i + 1] <= |warnings| &&
        warnings[outputCuts[i]..outputCuts[i + 1]] ==
          WarningAtSpec(text, inputCuts[i])
  }

  ghost predicate WarningBytesRelation(
    text: string, warnings: BenchWorld.Bytes
  )
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      WarningPartitionFrom(text, 0, warnings, inputCuts, outputCuts)
  }

  ghost predicate CommandWarningsRelation(
    raw: TrSchema.TrCmdRaw,
    decoded: seq<SetDecode>,
    warnings: BenchWorld.Bytes
  )
    requires |decoded| == |raw.operands|
  {
    if |raw.operands| == 0 then
      warnings == []
    else
      exists first: BenchWorld.Bytes ::
        WarningBytesRelation(raw.operands[0], first) &&
        (if |raw.operands| > 1 && decoded[0].SetOk? then
           exists second: BenchWorld.Bytes ::
             WarningBytesRelation(raw.operands[1], second) &&
             warnings == first + second
         else warnings == first)
  }

  ghost predicate SetDecodeRelation(text: string, decoded: SetDecode)
  {
    (exists bytes: BenchWorld.Bytes ::
       SetBytesRelation(text, bytes) &&
       decoded == SetOk(bytes)) ||
    ((forall bytes: BenchWorld.Bytes :: !SetBytesRelation(text, bytes)) &&
     decoded == SetUnsupported(text))
  }

  ghost predicate DecodedOperandsRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>
  )
  {
    |decoded| == |operands| &&
    forall i :: 0 <= i < |operands| ==>
                  SetDecodeRelation(operands[i], decoded[i])
  }

  function DecodedBytes(decoded: SetDecode): BenchWorld.Bytes
  {
    match decoded
    case SetOk(bytes) => bytes
    case SetUnsupported(_) => []
  }

  ghost predicate FirstUnsupportedOperandRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>,
    operand: string
  )
  {
    |decoded| == |operands| &&
    exists i ::
      0 <= i < |operands| &&
      decoded[i] == SetUnsupported(operands[i]) &&
      operand == operands[i] &&
      forall j :: 0 <= j < i ==> decoded[j].SetOk?
  }

  ghost predicate CommandDecodedRelation(
    raw: TrSchema.TrCmdRaw,
    decoded: seq<SetDecode>,
    cmd: TrCmd
  )
  {
    DecodedOperandsRelation(raw.operands, decoded) &&
    cmd.deleteSet == raw.seenDelete &&
    cmd.squeeze == raw.seenSqueeze &&
    cmd.set1 ==
    (if |raw.operands| > 0 then DecodedBytes(decoded[0]) else []) &&
    cmd.set2 ==
    (if |raw.operands| > 1 then DecodedBytes(decoded[1]) else []) &&
    cmd.squeezeSet ==
    (if raw.seenSqueeze && |raw.operands| > 1 then
       DecodedBytes(decoded[1])
     else if |raw.operands| > 0 then
       DecodedBytes(decoded[0])
     else
       []) &&
    CommandWarningsRelation(raw, decoded, cmd.warnings) &&
    if raw.seenHelp &&
       (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      cmd.mode == ModeHelp
    else if raw.seenVersion then
      cmd.mode == ModeVersion
    else if |raw.operands| == 0 then
      cmd.mode == ModeMissingOperand(MissingOperandMessageSpec())
    else if !raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec(raw.operands[0], false))
    else if raw.seenDelete && raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec(raw.operands[0], true))
    else if raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| > 1 then
      cmd.mode == ModeExtraOperand(raw.operands[1])
    else if |raw.operands| > 2 then
      cmd.mode == ModeExtraOperand(raw.operands[2])
    else if exists operand ::
              FirstUnsupportedOperandRelation(raw.operands, decoded, operand) then
      exists operand ::
        FirstUnsupportedOperandRelation(raw.operands, decoded, operand) &&
        cmd.mode == ModeUnsupportedSet(operand)
    else if !raw.seenDelete && |raw.operands| == 2 &&
            |DecodedBytes(decoded[1])| == 0 then
      cmd.mode == ModeEmptySet2
    else
      cmd.mode == ModeRun
  }

  ghost predicate CommandRelation(raw: TrSchema.TrCmdRaw, cmd: TrCmd)
  {
    exists decoded: seq<SetDecode> ::
      CommandDecodedRelation(raw, decoded, cmd)
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==>
                     indices[i] < indices[j]
  }

  ghost predicate TranslationRelation(
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    inputByte: char,
    outputByte: char
  )
  {
    if inputByte !in set1 then
      outputByte == inputByte
    else
      |set2| > 0 &&
      exists i ::
        0 <= i < |set1| &&
        set1[i] == inputByte &&
        (forall j :: i < j < |set1| ==> set1[j] != inputByte) &&
        outputByte == set2[if i < |set2| then i else |set2| - 1]
  }

  ghost predicate DeleteTranslateRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    transformed: BenchWorld.Bytes
  )
  {
    exists kept: seq<nat> ::
      StrictlyIncreasing(kept) &&
      (forall k :: 0 <= k < |kept| ==> kept[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in kept) ==
                     (!cmd.deleteSet || input[i] !in cmd.set1)) &&
      |transformed| == |kept| &&
      (forall k :: 0 <= k < |kept| ==>
                     (if cmd.deleteSet || |cmd.set2| == 0 then
                        transformed[k] == input[kept[k]]
                      else
                        TranslationRelation(
                          cmd.set1,
                          cmd.set2,
                          input[kept[k]],
                          transformed[k]
                        )))
  }

  ghost predicate SqueezeStateRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    output: BenchWorld.Bytes
  )
  {
    exists emitted: seq<nat> ::
      StrictlyIncreasing(emitted) &&
      (forall k :: 0 <= k < |emitted| ==> emitted[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in emitted) ==
                     SqueezeEmittedAt(
                       input, squeezeSet, hasPrevious, previous, i
                     )) &&
      |output| == |emitted| &&
      (forall k :: 0 <= k < |emitted| ==>
                     output[k] == input[emitted[k]])
  }

  ghost predicate SqueezeEmittedAt(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    i: nat
  )
    requires i < |input|
  {
    input[i] !in squeezeSet ||
    (if i == 0 then
       !hasPrevious || input[i] != previous
     else
       input[i] != input[i - 1])
  }

  ghost predicate SqueezeRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    SqueezeStateRelation(input, squeezeSet, false, '\0', output)
  }

  ghost predicate OutputRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists transformed: BenchWorld.Bytes ::
      DeleteTranslateRelation(cmd, input, transformed) &&
      if cmd.squeeze then
        SqueezeRelation(transformed, cmd.squeezeSet, output)
      else
        output == transformed
  }

  twostate predicate Spec(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists cmd: TrCmd ::
      CommandRelation(raw, cmd) &&
      match cmd.mode
      case ModeHelp =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) + HelpTextSpec() &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
      case ModeVersion =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) + VersionTextSpec() &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
      case ModeMissingOperand(message) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + message &&
        exit == 1
      case ModeExtraOperand(operand) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
          ExtraOperandMessageSpec(operand, |raw.operands| == 2) &&
        exit == 1
      case ModeUnsupportedSet(operand) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + cmd.warnings +
          UnsupportedSetMessageSpec(operand) &&
        exit == 1
      case ModeEmptySet2 =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + EmptySet2MessageSpec() &&
        exit == 1
      case ModeRun =>
        io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
        (exists output: BenchWorld.Bytes ::
           OutputRelation(cmd, old(io.stdin()), output) &&
           io.stdout() == old(io.stdout()) + output) &&
        io.stderr() == old(io.stderr()) + cmd.warnings &&
        exit == 0
  }
}
