include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TrSchema.dfy"
include "TrSpec.dfy"

module TrCore {
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Spec = TrSpec
  import Utf8 = Utf8Semantics

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

  type SetDecode = Result.Result<BenchWorld.Bytes, string>
  datatype SetAtom = SetAtom(next: nat, bytes: BenchWorld.Bytes)

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

  function EscapeBytes(ch: char): BenchWorld.Bytes
  {
    if ch == 'a' || ch == 'b' || ch == 'f' || ch == 'n' ||
       ch == 'r' || ch == 't' || ch == 'v' then
      [SimpleEscape(ch)]
    else
      Utf8.EncodeChar(ch)
  }

  function AtomAt(text: string, i: nat): SetAtom
    requires i < |text|
    ensures i < AtomAt(text, i).next <= |text|
  {
    if text[i] != '\\' then
      SetAtom(i + 1, Utf8.EncodeChar(text[i]))
    else if i + 1 == |text| then
      SetAtom(i + 1, ['\\'])
    else if IsOctal(text[i + 1]) then
      if i + 2 < |text| && IsOctal(text[i + 2]) then
        if i + 3 < |text| && IsOctal(text[i + 3]) &&
           OctalValue(text[i + 1]) < 4 then
          SetAtom(i + 4, [((OctalValue(text[i + 1]) * 64 +
                            OctalValue(text[i + 2]) * 8 +
                            OctalValue(text[i + 3])) as char)])
        else
          SetAtom(i + 3, [((OctalValue(text[i + 1]) * 8 +
                            OctalValue(text[i + 2])) as char)])
      else
        SetAtom(i + 2, [(OctalValue(text[i + 1]) as char)])
    else
      SetAtom(i + 2, EscapeBytes(text[i + 1]))
  } by method {
    if text[i] != '\\' {
      return SetAtom(i + 1, Utf8.EncodeChar(text[i]));
    }
    if i + 1 == |text| {
      return SetAtom(i + 1, ['\\']);
    }
    if IsOctal(text[i + 1]) {
      var first := OctalValue(text[i + 1]);
      if i + 2 < |text| && IsOctal(text[i + 2]) {
        var second := OctalValue(text[i + 2]);
        if i + 3 < |text| && IsOctal(text[i + 3]) && first < 4 {
          return SetAtom(i + 4, [((first * 64 + second * 8 +
                                   OctalValue(text[i + 3])) as char)]);
        }
        return SetAtom(i + 3, [((first * 8 + second) as char)]);
      }
      return SetAtom(i + 2, [(first as char)]);
    }
    return SetAtom(i + 2, EscapeBytes(text[i + 1]));
  }

  function WarningBytesFrom(text: string, i: nat): BenchWorld.Bytes
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then []
    else Spec.WarningAtSpec(text, i) +
         WarningBytesFrom(text, AtomAt(text, i).next)
  } by method {
    if i == |text| {
      return [];
    }
    var atom := AtomAt(text, i);
    return Spec.WarningAtSpec(text, i) + WarningBytesFrom(text, atom.next);
  }

  function ContainsPairFrom(text: string, i: nat, first: char, second: char): bool
    requires i <= |text|
    decreases |text| - i
  {
    (i + 1 < |text| && text[i] == first && text[i + 1] == second) ||
    (i < |text| && ContainsPairFrom(text, i + 1, first, second))
  }

  function ContainsCharFrom(text: string, i: nat, target: char): bool
    requires i <= |text|
    decreases |text| - i
  {
    i < |text| && (text[i] == target || ContainsCharFrom(text, i + 1, target))
  }

  function StartsUnsupportedConstruct(text: string, i: nat): bool
    requires i <= |text|
  {
    i < |text| && text[i] == '[' && (
      (i + 1 < |text| && text[i + 1] == ':' && ContainsPairFrom(text, i + 2, ':', ']')) ||
      (i + 1 < |text| && text[i + 1] == '=' && ContainsPairFrom(text, i + 2, '=', ']')) ||
      (i + 2 < |text| && text[i + 2] == '*' && ContainsCharFrom(text, i + 3, ']'))
    )
  }

  function RangeChars(lo: char, hi: char): BenchWorld.Bytes
    requires 0 <= lo as int < 256
    requires 0 <= hi as int < 256
    requires lo as int <= hi as int
    decreases (hi as int) - (lo as int)
  {
    if lo == hi then
      [lo]
    else
      [lo] + RangeChars(((lo as int) + 1) as char, hi)
  }

  function DecodeSetFrom(text: string, i: nat): SetDecode
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      Result.Ok([])
    else if StartsUnsupportedConstruct(text, i) then
      Result.Err(text)
    else
      var atom := AtomAt(text, i);
      if atom.next < |text| && text[atom.next] == '-' && atom.next + 1 < |text| then
        var end := AtomAt(text, atom.next + 1);
        if |atom.bytes| == 1 && |end.bytes| == 1 &&
           atom.bytes[0] as int < 256 && end.bytes[0] as int < 256 &&
           atom.bytes[0] as int <= end.bytes[0] as int then
          match DecodeSetFrom(text, end.next)
          case Ok(rest) => Result.Ok(RangeChars(atom.bytes[0], end.bytes[0]) + rest)
          case Err(_) => Result.Err(text)
        else
          Result.Err(text)
      else
        match DecodeSetFrom(text, atom.next)
        case Ok(rest) => Result.Ok(atom.bytes + rest)
        case Err(_) => Result.Err(text)
  } by method {
    if i == |text| {
      return Result.Ok([]);
    } else if StartsUnsupportedConstruct(text, i) {
      return Result.Err(text);
    } else {
      var atom := AtomAt(text, i);
      if atom.next < |text| && text[atom.next] == '-' && atom.next + 1 < |text| {
        var end := AtomAt(text, atom.next + 1);
        if |atom.bytes| == 1 && |end.bytes| == 1 &&
           atom.bytes[0] as int < 256 && end.bytes[0] as int < 256 &&
           atom.bytes[0] as int <= end.bytes[0] as int {
          var tail := DecodeSetFrom(text, end.next);
          match tail
          case Ok(rest) =>
            return Result.Ok(RangeChars(atom.bytes[0], end.bytes[0]) + rest);
          case Err(_) =>
            return Result.Err(text);
        } else {
          return Result.Err(text);
        }
      } else {
        var tail := DecodeSetFrom(text, atom.next);
        match tail
        case Ok(rest) =>
          return Result.Ok(atom.bytes + rest);
        case Err(_) =>
          return Result.Err(text);
      }
    }
  }

  function DecodeSet(text: string): SetDecode
  {
    DecodeSetFrom(text, 0)
  } by method {
    return DecodeSetFrom(text, 0);
  }

  function HasUnsupportedOperand(operands: seq<string>): string
    decreases |operands|
  {
    if |operands| == 0 then
      ""
    else
      match DecodeSet(operands[0])
      case Ok(_) => HasUnsupportedOperand(operands[1..])
      case Err(_) => operands[0]
  } by method {
    if |operands| == 0 {
      return "";
    } else {
      var decoded := DecodeSet(operands[0]);
      match decoded
      case Ok(_) =>
        return HasUnsupportedOperand(operands[1..]);
      case Err(_) =>
        return operands[0];
    }
  }

  function SetBytes(text: string): BenchWorld.Bytes
  {
    match DecodeSet(text)
    case Ok(bytes) => bytes
    case Err(_) => []
  } by method {
    var decoded := DecodeSet(text);
    return
      match decoded
      case Ok(bytes) => bytes
      case Err(_) => [];
  }

  // Deferred GNU behavior: classes, equivalence classes, repeats,
  // complements, truncate mode and locale-dependent collation remain outside
  // this literal-byte benchmark slice.
  function Command(raw: TrSchema.TrCmdRaw): TrCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else if |raw.operands| == 0 then
        ModeMissingOperand(Spec.MissingOperandMessageSpec())
      else if !raw.seenDelete && !raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], false))
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], true))
      else if raw.seenDelete && !raw.seenSqueeze && |raw.operands| > 1 then
        ModeExtraOperand(raw.operands[1])
      else if |raw.operands| > 2 then
        ModeExtraOperand(raw.operands[2])
      else if HasUnsupportedOperand(raw.operands) != "" then
        ModeUnsupportedSet(HasUnsupportedOperand(raw.operands))
      else if !raw.seenDelete && |raw.operands| == 2 && |SetBytes(raw.operands[1])| == 0 then
        ModeEmptySet2
      else
        ModeRun;
    var set1 := if |raw.operands| > 0 then SetBytes(raw.operands[0]) else [];
    var set2 := if |raw.operands| > 1 then SetBytes(raw.operands[1]) else [];
    var squeezeSet :=
      if raw.seenSqueeze && |raw.operands| > 1 then set2 else set1;
    var warnings :=
      (if |raw.operands| > 0 then WarningBytesFrom(raw.operands[0], 0) else []) +
      (if |raw.operands| > 1 && DecodeSet(raw.operands[0]).Ok? then
         WarningBytesFrom(raw.operands[1], 0) else []);
    TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet, warnings)
  } by method {
    var unsupported := HasUnsupportedOperand(raw.operands);
    var set1: BenchWorld.Bytes := [];
    var set2: BenchWorld.Bytes := [];
    if |raw.operands| > 0 {
      set1 := SetBytes(raw.operands[0]);
    }
    if |raw.operands| > 1 {
      set2 := SetBytes(raw.operands[1]);
    }
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else if |raw.operands| == 0 then
        ModeMissingOperand(Spec.MissingOperandMessageSpec())
      else if !raw.seenDelete && !raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], false))
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], true))
      else if raw.seenDelete && !raw.seenSqueeze && |raw.operands| > 1 then
        ModeExtraOperand(raw.operands[1])
      else if |raw.operands| > 2 then
        ModeExtraOperand(raw.operands[2])
      else if unsupported != "" then
        ModeUnsupportedSet(unsupported)
      else if !raw.seenDelete && |raw.operands| == 2 && |set2| == 0 then
        ModeEmptySet2
      else
        ModeRun;
    var squeezeSet := if raw.seenSqueeze && |raw.operands| > 1 then set2 else set1;
    var warnings: BenchWorld.Bytes := [];
    if |raw.operands| > 0 {
      warnings := WarningBytesFrom(raw.operands[0], 0);
      if |raw.operands| > 1 && DecodeSet(raw.operands[0]).Ok? {
        warnings := warnings + WarningBytesFrom(raw.operands[1], 0);
      }
    }
    return TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet, warnings);
  }

  function Contains(bytes: BenchWorld.Bytes, ch: char): bool
    decreases |bytes|
  {
    |bytes| > 0 && (bytes[0] == ch || Contains(bytes[1..], ch))
  } by method {
    if |bytes| == 0 {
      return false;
    } else {
      return bytes[0] == ch || Contains(bytes[1..], ch);
    }
  }

  function TranslateWithCandidate(
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    ch: char,
    candidate: char
  ): char
    requires |set2| > 0
    ensures candidate is BenchWorld.RawByte ==>
              TranslateWithCandidate(set1, set2, ch, candidate) is BenchWorld.RawByte
    decreases |set1|
  {
    if |set1| == 0 then
      candidate
    else
      var nextCandidate := if set1[0] == ch then set2[0] else candidate;
      TranslateWithCandidate(set1[1..], if |set2| > 1 then set2[1..] else set2, ch, nextCandidate)
  } by method {
    if |set1| == 0 {
      return candidate;
    } else {
      var nextCandidate := if set1[0] == ch then set2[0] else candidate;
      return TranslateWithCandidate(
          set1[1..],
          if |set2| > 1 then set2[1..] else set2,
          ch,
          nextCandidate
        );
    }
  }

  function TranslateWith(set1: BenchWorld.Bytes, set2: BenchWorld.Bytes, ch: char): char
    requires |set2| > 0
    ensures ch is BenchWorld.RawByte ==> TranslateWith(set1, set2, ch) is BenchWorld.RawByte
  {
    TranslateWithCandidate(set1, set2, ch, ch)
  } by method {
    return TranslateWithCandidate(set1, set2, ch, ch);
  }

  function DeleteAndTranslate(cmd: TrCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 then
      []
    else if cmd.deleteSet && Contains(cmd.set1, data[0]) then
      DeleteAndTranslate(cmd, data[1..])
    else
      var out := if !cmd.deleteSet && |cmd.set2| > 0 then
                   TranslateWith(cmd.set1, cmd.set2, data[0])
                 else
                   data[0];
      [out] + DeleteAndTranslate(cmd, data[1..])
  } by method {
    if |data| == 0 {
      return [];
    } else {
      var selected := Contains(cmd.set1, data[0]);
      if cmd.deleteSet && selected {
        return DeleteAndTranslate(cmd, data[1..]);
      } else {
        var ch := data[0];
        if !cmd.deleteSet && |cmd.set2| > 0 {
          ch := TranslateWith(cmd.set1, cmd.set2, data[0]);
        }
        return [ch] + DeleteAndTranslate(cmd, data[1..]);
      }
    }
  }

  function SqueezeFrom(
    data: BenchWorld.Bytes,
    squeezeBytes: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char
  ): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 then
      []
    else if hasPrevious && data[0] == previous && Contains(squeezeBytes, data[0]) then
      SqueezeFrom(data[1..], squeezeBytes, true, previous)
    else
      [data[0]] + SqueezeFrom(data[1..], squeezeBytes, true, data[0])
  } by method {
    if |data| == 0 {
      return [];
    } else {
      var selected := Contains(squeezeBytes, data[0]);
      if hasPrevious && data[0] == previous && selected {
        return SqueezeFrom(data[1..], squeezeBytes, true, previous);
      } else {
        return [data[0]] + SqueezeFrom(data[1..], squeezeBytes, true, data[0]);
      }
    }
  }

  function RenderData(cmd: TrCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    var transformed := DeleteAndTranslate(cmd, data);
    if cmd.squeeze then SqueezeFrom(transformed, cmd.squeezeSet, false, '\0') else transformed
  } by method {
    var transformed := DeleteAndTranslate(cmd, data);
    if cmd.squeeze {
      return SqueezeFrom(transformed, cmd.squeezeSet, false, '\0');
    } else {
      return transformed;
    }
  }

  twostate predicate CoreSummary(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
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
        Spec.ExtraOperandMessageSpec(operand, |raw.operands| == 2) &&
      exit == 1
    case ModeUnsupportedSet(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + cmd.warnings +
        Spec.UnsupportedSetMessageSpec(operand) &&
      exit == 1
    case ModeEmptySet2 =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.EmptySet2MessageSpec() &&
      exit == 1
    case ModeRun =>
      io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
      io.stdout() == old(io.stdout()) + RenderData(cmd, old(io.stdin())) &&
      io.stderr() == old(io.stderr()) + cmd.warnings &&
      exit == 0
  }

  method RunCore(raw: TrSchema.TrCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preStdin := io.stdin();
    var cmd := Command(raw);

    match cmd.mode {
      case ModeHelp =>
        var _ := io.WriteStdout(Spec.HelpTextSpec(), BenchWorld.ThrowOnError);
        exit := 0;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeVersion =>
        var _ := io.WriteStdout(Spec.VersionTextSpec(), BenchWorld.ThrowOnError);
        exit := 0;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeMissingOperand(message) =>
        var _ := io.WriteStderr(message, BenchWorld.ThrowOnError);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeExtraOperand(operand) =>
        var _ := io.WriteStderr(Spec.ExtraOperandMessageSpec(operand, |raw.operands| == 2), BenchWorld.ThrowOnError);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeUnsupportedSet(operand) =>
        var _ := io.WriteStderr(cmd.warnings, BenchWorld.ThrowOnError);
        var _ := io.WriteStderr(Spec.UnsupportedSetMessageSpec(operand), BenchWorld.ThrowOnError);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeEmptySet2 =>
        var _ := io.WriteStderr(Spec.EmptySet2MessageSpec(), BenchWorld.ThrowOnError);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeRun =>
        var _ := io.WriteStderr(cmd.warnings, BenchWorld.ThrowOnError);
        var data :- assert io.ReadStdin(BenchWorld.ThrowOnError);
        assert IOContract.ReadStdinAllFields(preStdin, io.stdin(), data);
        assert data == preStdin;
        assert io.stdin() == IOContract.AfterReadStdinFields(preStdin);
        var out := RenderData(cmd, data);
        var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
        exit := 0;
    }
    assert CoreSummary(raw, io, exit);
  }
}
