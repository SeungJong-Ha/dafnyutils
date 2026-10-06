include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ExpandSchema.dfy"
include "ExpandSpec.dfy"

module ExpandCore {
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = ExpandSchema
  import Spec = ExpandSpec

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function MaxColumn(): nat
  {
    9223372036854775807
  }

  function DigitValue(ch: char): nat
    requires IsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function ParseNatFrom(text: string, i: nat, acc: nat): Schema.NatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      Schema.NatOk(acc)
    else if !IsDigit(text[i]) then
      Schema.NatErr
    else if acc > (MaxColumn() - DigitValue(text[i])) / 10 then
      Schema.NatErr
    else
      ParseNatFrom(text, i + 1, acc * 10 + DigitValue(text[i]))
  }

  function ParsePositiveNat(text: string): Schema.NatParse
  {
    if |text| == 0 then Schema.NatErr else ParseNatFrom(text, 0, 0)
  }

  function IsSeparator(ch: char): bool
  {
    ch == ',' || ch == ' ' || ch == '\t'
  }

  function IsMarker(ch: char): bool
  {
    ch == '+' || ch == '/'
  }

  function MarkerOf(ch: char): Schema.MarkerKind
    requires IsMarker(ch)
  {
    if ch == '+' then Schema.MarkerPlus else Schema.MarkerSlash
  }

  function FindTokenEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FindTokenEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || IsSeparator(text[start]) then
      start
    else
      FindTokenEnd(text, start + 1)
  }

  function FindDigitsEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FindDigitsEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || !IsDigit(text[start]) then
      start
    else
      FindDigitsEnd(text, start + 1)
  }

  function CombineDiagnostics(first: string, rest: string): string
  {
    if rest == "" then first else first + "\nexpand: " + rest
  }

  function SyntaxDiagnosticsFrom(
    text: string,
    i: nat,
    haveValue: bool,
    numberStart: nat,
    value: nat
  ): string
    requires i <= |text|
    requires !haveValue || numberStart <= i
    decreases |text| - i
  {
    if i == |text| then
      ""
    else if IsSeparator(text[i]) then
      SyntaxDiagnosticsFrom(text, i + 1, false, 0, 0)
    else if IsMarker(text[i]) then
      var rest := SyntaxDiagnosticsFrom(
                    text, i + 1, haveValue, numberStart, value
                  );
      if haveValue then
        CombineDiagnostics(
          Spec.MarkerNotAtStartMessage(
            MarkerOf(text[i]), text[i..]
          ),
          rest
        )
      else
        rest
    else if IsDigit(text[i]) then
      var start := if haveValue then numberStart else i;
      var accumulated := if haveValue then value else 0;
      var digit := DigitValue(text[i]);
      if accumulated > (MaxColumn() - digit) / 10 then
        var end := FindDigitsEnd(text, i);
        CombineDiagnostics(
          Spec.TooLargeMessage(text[start..end]),
          SyntaxDiagnosticsFrom(
            text, end, true, start, accumulated
          )
        )
      else
        SyntaxDiagnosticsFrom(
          text, i + 1, true, start,
          accumulated * 10 + digit
        )
    else
      Spec.InvalidCharacterMessage(text[i..])
  }

  function SyntaxDiagnostics(text: string): string
  {
    SyntaxDiagnosticsFrom(text, 0, false, 0, 0)
  }

  function ScanMarkers(part: string, i: nat, marker: Schema.MarkerKind, hasMarker: bool): Schema.MarkerScan
    requires i <= |part|
    ensures i <= ScanMarkers(part, i, marker, hasMarker).index <= |part|
    decreases |part| - i
  {
    if i == |part| || !IsMarker(part[i]) then
      Schema.MarkerScan(i, marker, hasMarker)
    else
      ScanMarkers(part, i + 1, MarkerOf(part[i]), true)
  }

  function LastStop(stops: seq<nat>): nat
    requires |stops| > 0
  {
    stops[|stops| - 1]
  }

  function CommitTabValue(
    acc: Schema.TabAccum,
    marker: Schema.MarkerKind,
    value: nat
  ): Schema.TabAccumParse
  {
    if marker == Schema.MarkerSlash then
      if acc.extendSize != 0 then
        Schema.TabAccumErr(
          Spec.RepeatOnlyLastMessage(Schema.MarkerSlash)
        )
      else
        Schema.TabAccumOk(Schema.TabAccum(
                            acc.stops, value, acc.incrementSize, marker
                          ))
    else if marker == Schema.MarkerPlus then
      if acc.incrementSize != 0 then
        Schema.TabAccumErr(
          Spec.RepeatOnlyLastMessage(Schema.MarkerPlus)
        )
      else
        Schema.TabAccumOk(Schema.TabAccum(
                            acc.stops, acc.extendSize, value, marker
                          ))
    else
      Schema.TabAccumOk(Schema.TabAccum(
                          acc.stops + [value], acc.extendSize,
                          acc.incrementSize, marker
                        ))
  }

  function ParseTabPart(part: string, acc: Schema.TabAccum): Schema.TabAccumParse
  {
    if |part| == 0 then
      Schema.TabAccumOk(acc)
    else
      var scan := ScanMarkers(part, 0, Schema.MarkerNone, false);
      var marker := if scan.hasMarker then scan.marker else acc.activeMarker;
      if scan.index == |part| then
        Schema.TabAccumOk(Schema.TabAccum(
                            acc.stops, acc.extendSize, acc.incrementSize, marker
                          ))
      else
        var end := FindDigitsEnd(part, scan.index);
        if end < |part| then
          if IsMarker(part[end]) then
            Schema.TabAccumErr(Spec.MarkerNotAtStartMessage(
                                 MarkerOf(part[end]), part[end..]
                               ))
          else
            Schema.TabAccumErr(
              Spec.InvalidCharacterMessage(part[end..])
            )
        else
          var digits := part[scan.index..end];
          match ParsePositiveNat(digits)
          case NatErr =>
            Schema.TabAccumErr(Spec.TooLargeMessage(digits))
          case NatOk(value) =>
            CommitTabValue(acc, marker, value)
  }

  function ParseTabTextFrom(text: string, start: nat, acc: Schema.TabAccum): Schema.TabAccumParse
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| then
      Schema.TabAccumOk(acc)
    else if IsSeparator(text[start]) then
      ParseTabTextFrom(text, start + 1, acc)
    else
      var end := FindTokenEnd(text, start);
      match ParseTabPart(text[start..end], acc)
      case TabAccumErr(value) => Schema.TabAccumErr(value)
      case TabAccumOk(next) => ParseTabTextFrom(text, end, next)
  }

  function ParseTabArgsFrom(
    args: seq<Schema.TabArg>, i: nat, limit: int,
    acc: Schema.TabAccum
  ): Schema.TabAccumParse
    requires i <= |args|
    decreases |args| - i
  {
    if i == |args| ||
       (limit >= 0 && args[i].tokenIndex >= limit) then
      Schema.TabAccumOk(acc)
    else
      var arg := args[i];
      var argAcc := Schema.TabAccum(
                      acc.stops,
                      acc.extendSize,
                      acc.incrementSize,
                      Schema.MarkerNone
                    );
      var diagnostics := SyntaxDiagnostics(arg.text);
      if diagnostics != "" then
        Schema.TabAccumErr(diagnostics)
      else
        match ParseTabTextFrom(arg.text, 0, argAcc)
        case TabAccumErr(value) => Schema.TabAccumErr(value)
        case TabAccumOk(next) =>
          ParseTabArgsFrom(args, i + 1, limit, next)
  }

  function StopsValidationError(
    stops: seq<nat>, i: nat, previous: nat
  ): string
    requires i <= |stops|
    decreases |stops| - i
  {
    if i == |stops| then ""
    else if stops[i] == 0 then Spec.ZeroTabMessage()
    else if stops[i] <= previous then Spec.AscendingTabsMessage()
    else StopsValidationError(stops, i + 1, stops[i])
  }

  function FinalizeTabAccum(acc: Schema.TabAccum): Schema.TabParse
  {
    var validationError := StopsValidationError(acc.stops, 0, 0);
    if validationError != "" then
      Schema.TabErr(validationError)
    else if acc.incrementSize != 0 && acc.extendSize != 0 then
      Schema.TabErr(Spec.MixedRepeatMessage())
    else if |acc.stops| == 0 then
      Schema.TabOk(Schema.TabStops(
                     [],
                     Schema.RepeatFixed(
                       if acc.extendSize != 0 then acc.extendSize
                       else if acc.incrementSize != 0 then acc.incrementSize
                       else 8
                     )
                   ))
    else if |acc.stops| == 1 &&
            acc.extendSize == 0 && acc.incrementSize == 0 then
      Schema.TabOk(Schema.TabStops(
                     [], Schema.RepeatFixed(acc.stops[0])
                   ))
    else
      Schema.TabOk(Schema.TabStops(
                     acc.stops,
                     if acc.extendSize != 0 then
                       Schema.RepeatFixed(acc.extendSize)
                     else if acc.incrementSize != 0 then
                       Schema.RepeatIncremental(acc.incrementSize)
                     else
                       Schema.RepeatNone
                   ))
  }

  function InputsFromOperands(operands: seq<string>): seq<Schema.Input>
    ensures |InputsFromOperands(operands)| == |operands|
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then Schema.Stdin else Schema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function HelpBeforeOther(raw: Schema.ExpandCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionBeforeInvalid(raw: Schema.ExpandCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  function RequestTokenIndex(raw: Schema.ExpandCmdRaw): int
  {
    if HelpBeforeOther(raw) then raw.helpTokenIndex
    else if VersionBeforeInvalid(raw) then raw.versionTokenIndex
    else -1
  }

  function ScanCommandOptions(
    raw: Schema.ExpandCmdRaw
  ): Schema.OptionScan
  {
    match ParseTabArgsFrom(
        raw.tabArgs, 0, RequestTokenIndex(raw),
        Schema.TabAccum([], 0, 0, Schema.MarkerNone)
      )
    case TabAccumErr(value) => Schema.ScanInvalidTabs(value)
    case TabAccumOk(acc) =>
      if HelpBeforeOther(raw) then Schema.ScanHelp
      else if VersionBeforeInvalid(raw) then Schema.ScanVersion
      else Schema.ScanContinue(acc)
  }

  function Command(raw: Schema.ExpandCmdRaw): Schema.ExpandCmd
  {
    match ScanCommandOptions(raw)
    case ScanInvalidTabs(value) =>
      Schema.ExpandCmd(
        Schema.ModeInvalidTabs,
        Schema.TabStops([], Schema.RepeatFixed(8)),
        false, value, []
      )
    case ScanHelp =>
      Schema.ExpandCmd(
        Schema.ModeHelp,
        Schema.TabStops([], Schema.RepeatFixed(8)),
        false, "", []
      )
    case ScanVersion =>
      Schema.ExpandCmd(
        Schema.ModeVersion,
        Schema.TabStops([], Schema.RepeatFixed(8)),
        false, "", []
      )
    case ScanContinue(acc) =>
      match FinalizeTabAccum(acc)
      case TabErr(value) =>
        Schema.ExpandCmd(
          Schema.ModeInvalidTabs,
          Schema.TabStops([], Schema.RepeatFixed(8)),
          false, value, []
        )
      case TabOk(tabs) =>
        var inputs := InputsFromOperands(raw.operands);
        Schema.ExpandCmd(
          Schema.ModeRun, tabs, raw.seenInitial, "",
          if |inputs| == 0 then [Schema.Stdin] else inputs
        )
  }


  function Spaces(count: nat): BenchWorld.Bytes
    decreases count
  {
    if count == 0 then [] else [' '] + Spaces(count - 1)
  }

  function NextFixedSpaces(width: nat, column: nat): nat
  {
    if width == 0 then 1 else
    var rem := column % width;
    if rem == 0 then width else width - rem
  }

  function NextIncrementalSpaces(base: nat, width: nat, column: nat): nat
  {
    if width == 0 then 1 else if column < base then base - column else
    var rem := (column - base) % width;
    if rem == 0 then width else width - rem
  }

  function NextStopSpaces(stops: seq<nat>, column: nat): nat
    decreases |stops|
  {
    if |stops| == 0 then
      1
    else if column < stops[0] then
      stops[0] - column
    else
      NextStopSpaces(stops[1..], column)
  }

  function HasFutureStop(stops: seq<nat>, column: nat): bool
    decreases |stops|
  {
    |stops| > 0 && (column < stops[0] || HasFutureStop(stops[1..], column))
  }

  function TabSpaces(tabs: Schema.TabStops, column: nat): nat
  {
    match tabs
    case TabStops(stops, repeat) =>
      if HasFutureStop(stops, column) then
        NextStopSpaces(stops, column)
      else
        match repeat
        case RepeatNone => 1
        case RepeatFixed(width) => NextFixedSpaces(width, column)
        case RepeatIncremental(width) =>
          if |stops| == 0 then
            NextFixedSpaces(width, column)
          else
            NextIncrementalSpaces(LastStop(stops), width, column)
  }

  function BackspaceColumn(column: nat): nat
  {
    if column == 0 then 0 else column - 1
  }

  function LeadingAfterByte(b: BenchWorld.RawByte, leading: bool): bool
  {
    if b == '\n' then true else leading && (b == ' ' || b == '\t')
  }

  function JoinPieces(pieces: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |pieces|
  {
    if |pieces| == 0 then [] else pieces[0] + JoinPieces(pieces[1..])
  }

  ghost predicate ByteExpansionSummary(
    tabs: Schema.TabStops,
    initialOnly: bool,
    b: BenchWorld.RawByte,
    column: nat,
    leading: bool,
    piece: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool
  )
  {
    var spaces := TabSpaces(tabs, column);
    if initialOnly && !leading then
      piece == [b] &&
      (if b == '\n' then
         nextColumn == 0 && nextLeading
       else
         nextColumn == column && !nextLeading)
    else if b == '\t' then
      piece == Spaces(spaces) &&
      nextColumn == column + spaces &&
      nextLeading == LeadingAfterByte(b, leading)
    else if b == '\n' then
      piece == ['\n'] &&
      nextColumn == 0 &&
      nextLeading == LeadingAfterByte(b, leading)
    else if b == (8 as char) then
      piece == [(8 as char)] &&
      nextColumn == BackspaceColumn(column) &&
      nextLeading == LeadingAfterByte(b, leading)
    else
      piece == [b] &&
      nextColumn == column + 1 &&
      nextLeading == LeadingAfterByte(b, leading)
  }

  ghost predicate DataExpansionWitnessSummary(
    tabs: Schema.TabStops,
    initialOnly: bool,
    data: BenchWorld.Bytes,
    column: nat,
    leading: bool,
    output: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool,
    pieces: seq<BenchWorld.Bytes>,
    columns: seq<nat>,
    leadings: seq<bool>
  )
  {
    |pieces| == |data| &&
    |columns| == |data| + 1 &&
    |leadings| == |data| + 1 &&
    columns[0] == column &&
    leadings[0] == leading &&
    columns[|data|] == nextColumn &&
    leadings[|data|] == nextLeading &&
    (forall i: nat :: i < |data| ==>
                        ByteExpansionSummary(
                          tabs, initialOnly, data[i], columns[i], leadings[i],
                          pieces[i], columns[i + 1], leadings[i + 1]
                        )) &&
    output == JoinPieces(pieces)
  }

  ghost predicate ReadStepSummary(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    stdinBefore: BenchWorld.Bytes,
    stdinAfter: BenchWorld.Bytes,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
  {
    match input
    case Stdin =>
      result == Result.Ok(stdinBefore) && stdinAfter == []
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path) &&
      stdinAfter == stdinBefore
  }

  ghost predicate InputPieceSummary(
    cmd: Schema.ExpandCmd,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              column: nat,
                              leading: bool,
                              output: BenchWorld.Bytes,
                              nextColumn: nat,
                              nextLeading: bool
  )
  {
    match result
    case Ok(data) =>
      exists pieces: seq<BenchWorld.Bytes>,
        columns: seq<nat>, leadings: seq<bool> ::
        DataExpansionWitnessSummary(
          cmd.tabs, cmd.initialOnly, data, column, leading,
          output, nextColumn, nextLeading, pieces, columns, leadings
        )
    case Err(_) =>
      output == [] && nextColumn == column && nextLeading == leading
  }

  ghost predicate ErrorPieceSummary(
    input: Schema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              output: BenchWorld.Bytes,
                              hadError: bool
  )
  {
    match input
    case Stdin =>
      output == [] && !hadError
    case File(path) =>
      match result
      case Ok(_) => output == [] && !hadError
      case Err(err) => output == Spec.ErrorMessage(path, err) && hadError
  }

  ghost predicate InputTracePrefixSummary(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorFlags: seq<bool>,
    columns: seq<nat>,
    leadings: seq<bool>,
    stdinStates: seq<BenchWorld.Bytes>,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
  {
    count <= |cmd.inputs| &&
    |results| == count &&
    |outputPieces| == count &&
    |errorPieces| == count &&
    |errorFlags| == count &&
    |columns| == count + 1 &&
    |leadings| == count + 1 &&
    |stdinStates| == count + 1 &&
    columns[0] == 0 &&
    leadings[0] &&
    stdinStates[0] == preStdin &&
    stdinStates[count] == currentStdin &&
    (forall i: nat :: i < count ==>
                        ReadStepSummary(
                          cmd.inputs[i], preFs, stdinStates[i], stdinStates[i + 1],
                          results[i],
                          preStreams
                        ) &&
                        InputPieceSummary(
                          cmd, results[i], columns[i], leadings[i],
                          outputPieces[i], columns[i + 1], leadings[i + 1]
                        ) &&
                        ErrorPieceSummary(
                          cmd.inputs[i], results[i], errorPieces[i], errorFlags[i]
                        )) &&
    output == JoinPieces(outputPieces) &&
    errorOutput == JoinPieces(errorPieces) &&
    hadError == (exists i: nat :: i < |errorFlags| && errorFlags[i])
  }

  ghost predicate InputTraceSummary(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
  {
    exists
      results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
      outputPieces: seq<BenchWorld.Bytes>,
      errorPieces: seq<BenchWorld.Bytes>,
      errorFlags: seq<bool>,
      columns: seq<nat>,
      leadings: seq<bool>,
      stdinStates: seq<BenchWorld.Bytes> ::
      InputTracePrefixSummary(
        cmd, preFs, preStdin, |cmd.inputs|, postStdin,
        output, errorOutput, hadError, results, outputPieces,
        errorPieces, errorFlags, columns, leadings, stdinStates,
        preStreams
      )
  }

  lemma JoinPiecesSnoc(
    pieces: seq<BenchWorld.Bytes>,
    piece: BenchWorld.Bytes
  )
    ensures JoinPieces(pieces + [piece]) ==
            JoinPieces(pieces) + piece
    decreases |pieces|
  {
    if |pieces| > 0 {
      JoinPiecesSnoc(pieces[1..], piece);
      assert (pieces + [piece])[1..] == pieces[1..] + [piece];
    }
  }

  lemma AppendInputTraceWitness(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorFlags: seq<bool>,
    columns: seq<nat>,
    leadings: seq<bool>,
    stdinStates: seq<BenchWorld.Bytes>,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              outputPiece: BenchWorld.Bytes,
                              errorPiece: BenchWorld.Bytes,
                              errorFlag: bool,
                              nextColumn: nat,
                              nextLeading: bool,
                              nextStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires InputTracePrefixSummary(
               cmd, preFs, preStdin, count, currentStdin,
               output, errorOutput, hadError, results, outputPieces,
               errorPieces, errorFlags, columns, leadings, stdinStates,
               preStreams
             )
    requires count < |cmd.inputs|
    requires ReadStepSummary(
               cmd.inputs[count], preFs, currentStdin, nextStdin, result,
               preStreams
             )
    requires InputPieceSummary(
               cmd, result, columns[count], leadings[count],
               outputPiece, nextColumn, nextLeading
             )
    requires ErrorPieceSummary(
               cmd.inputs[count], result, errorPiece, errorFlag
             )
    ensures InputTracePrefixSummary(
              cmd, preFs, preStdin, count + 1, nextStdin,
              output + outputPiece, errorOutput + errorPiece,
              hadError || errorFlag, results + [result],
              outputPieces + [outputPiece], errorPieces + [errorPiece],
              errorFlags + [errorFlag], columns + [nextColumn],
              leadings + [nextLeading], stdinStates + [nextStdin],
              preStreams
            )
  {
    reveal InputTracePrefixSummary();
    JoinPiecesSnoc(outputPieces, outputPiece);
    JoinPiecesSnoc(errorPieces, errorPiece);
    assert forall i: nat :: i < count + 1 ==>
                              ReadStepSummary(
                                cmd.inputs[i], preFs,
                                (stdinStates + [nextStdin])[i],
                                (stdinStates + [nextStdin])[i + 1],
                                (results + [result])[i],
                                preStreams
                              ) &&
                              InputPieceSummary(
                                cmd, (results + [result])[i],
                                (columns + [nextColumn])[i],
                                (leadings + [nextLeading])[i],
                                (outputPieces + [outputPiece])[i],
                                (columns + [nextColumn])[i + 1],
                                (leadings + [nextLeading])[i + 1]
                              ) &&
                              ErrorPieceSummary(
                                cmd.inputs[i], (results + [result])[i],
                                (errorPieces + [errorPiece])[i],
                                (errorFlags + [errorFlag])[i]
                              ) by {
      forall i: nat | i < count + 1
        ensures ReadStepSummary(
                  cmd.inputs[i], preFs,
                  (stdinStates + [nextStdin])[i],
                  (stdinStates + [nextStdin])[i + 1],
                  (results + [result])[i],
                  preStreams
                ) &&
                InputPieceSummary(
                  cmd, (results + [result])[i],
                  (columns + [nextColumn])[i],
                  (leadings + [nextLeading])[i],
                  (outputPieces + [outputPiece])[i],
                  (columns + [nextColumn])[i + 1],
                  (leadings + [nextLeading])[i + 1]
                ) &&
                ErrorPieceSummary(
                  cmd.inputs[i], (results + [result])[i],
                  (errorPieces + [errorPiece])[i],
                  (errorFlags + [errorFlag])[i]
                )
      {
        if i == count {
          assert (stdinStates + [nextStdin])[i] == currentStdin;
          assert (columns + [nextColumn])[i] == columns[count];
          assert (leadings + [nextLeading])[i] == leadings[count];
        }
      }
    }
    assert (exists i: nat ::
              i < |errorFlags + [errorFlag]| &&
              (errorFlags + [errorFlag])[i]) ==
           (hadError || errorFlag) by {
      if hadError {
        ghost var i: nat :| i < |errorFlags| && errorFlags[i];
      }
      if exists i: nat ::
          i < |errorFlags + [errorFlag]| &&
          (errorFlags + [errorFlag])[i] {
        ghost var i: nat :|
          i < |errorFlags + [errorFlag]| &&
          (errorFlags + [errorFlag])[i];
        if i < count {
          assert hadError;
        } else {
          assert i == count;
        }
      }
    }
  }

  method ExpandDataFromMethod(
    tabs: Schema.TabStops,
    initialOnly: bool,
    data: BenchWorld.Bytes,
    column: nat,
    leading: bool
  )
    returns (
      out: BenchWorld.Bytes,
      nextColumn: nat,
      nextLeading: bool,
      ghost pieces: seq<BenchWorld.Bytes>,
      ghost columns: seq<nat>,
      ghost leadings: seq<bool>
    )
    ensures DataExpansionWitnessSummary(
              tabs, initialOnly, data, column, leading,
              out, nextColumn, nextLeading, pieces, columns, leadings
            )
  {
    out := [];
    nextColumn := column;
    nextLeading := leading;
    pieces := [];
    columns := [column];
    leadings := [leading];
    var i := 0;
    while i < |data|
      invariant 0 <= i <= |data|
      invariant |pieces| == i
      invariant |columns| == i + 1
      invariant |leadings| == i + 1
      invariant columns[0] == column
      invariant leadings[0] == leading
      invariant columns[i] == nextColumn
      invariant leadings[i] == nextLeading
      invariant forall j: nat :: j < i ==>
        ByteExpansionSummary(
          tabs, initialOnly, data[j], columns[j], leadings[j],
          pieces[j], columns[j + 1], leadings[j + 1]
        )
      invariant out == JoinPieces(pieces)
      decreases |data| - i
    {
      var byte := data[i];
      var piece: BenchWorld.Bytes;
      var stepColumn: nat;
      var stepLeading: bool;
      if initialOnly && !nextLeading {
        piece := [byte];
        if byte == '\n' {
          stepColumn := 0;
          stepLeading := true;
        } else {
          stepColumn := nextColumn;
          stepLeading := false;
        }
      } else if byte == '\t' {
        var spaces := TabSpaces(tabs, nextColumn);
        piece := Spaces(spaces);
        stepColumn := nextColumn + spaces;
        stepLeading := LeadingAfterByte(byte, nextLeading);
      } else if byte == '\n' {
        piece := ['\n'];
        stepColumn := 0;
        stepLeading := LeadingAfterByte(byte, nextLeading);
      } else if byte == (8 as char) {
        piece := [(8 as char)];
        stepColumn := BackspaceColumn(nextColumn);
        stepLeading := LeadingAfterByte(byte, nextLeading);
      } else {
        piece := [byte];
        stepColumn := nextColumn + 1;
        stepLeading := LeadingAfterByte(byte, nextLeading);
      }
      assert ByteExpansionSummary(
        tabs, initialOnly, byte, nextColumn, nextLeading,
        piece, stepColumn, stepLeading
      );

      ghost var priorPieces := pieces;
      ghost var priorColumns := columns;
      ghost var priorLeadings := leadings;
      JoinPiecesSnoc(priorPieces, piece);
      out := out + piece;
      pieces := priorPieces + [piece];
      columns := priorColumns + [stepColumn];
      leadings := priorLeadings + [stepLeading];
      nextColumn := stepColumn;
      nextLeading := stepLeading;
      assert forall j: nat :: j < i + 1 ==>
        ByteExpansionSummary(
          tabs, initialOnly, data[j], columns[j], leadings[j],
          pieces[j], columns[j + 1], leadings[j + 1]
        ) by {
        forall j: nat | j < i + 1
          ensures ByteExpansionSummary(
            tabs, initialOnly, data[j], columns[j], leadings[j],
            pieces[j], columns[j + 1], leadings[j + 1]
          )
        {
          if j < i {
            assert pieces[j] == priorPieces[j];
            assert columns[j] == priorColumns[j];
            assert columns[j + 1] == priorColumns[j + 1];
            assert leadings[j] == priorLeadings[j];
            assert leadings[j + 1] == priorLeadings[j + 1];
          } else {
            assert j == i;
            assert data[j] == byte;
            assert pieces[j] == piece;
            assert columns[j] == priorColumns[i];
            assert leadings[j] == priorLeadings[i];
          }
        }
      }
      assert out == JoinPieces(pieces);
      i := i + 1;
    }
    reveal DataExpansionWitnessSummary();
  }

  method ProcessInputPieceMethod(
    cmd: Schema.ExpandCmd,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              column: nat,
                              leading: bool
  )
    returns (
      out: BenchWorld.Bytes,
      nextColumn: nat,
      nextLeading: bool
    )
    ensures InputPieceSummary(
              cmd, result, column, leading, out, nextColumn, nextLeading
            )
  {
    match result
    case Ok(data) =>
      ghost var pieces: seq<BenchWorld.Bytes>;
      ghost var columns: seq<nat>;
      ghost var leadings: seq<bool>;
      out, nextColumn, nextLeading, pieces, columns, leadings :=
        ExpandDataFromMethod(
          cmd.tabs, cmd.initialOnly, data, column, leading
        );
    case Err(_) =>
      out := [];
      nextColumn := column;
      nextLeading := leading;
  }

  method ErrorPieceMethod(input: Schema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>)
    returns (out: BenchWorld.Bytes, had: bool)
    ensures ErrorPieceSummary(input, result, out, had)
  {
    match input
    case Stdin =>
      out := [];
      had := false;
    case File(path) =>
      match result
      case Ok(_) =>
        out := [];
        had := false;
      case Err(err) =>
        out := Spec.ErrorMessage(path, err);
        had := true;
  }

  twostate predicate CoreSummary(
    raw: Schema.ExpandCmdRaw, io: BenchIO.IO, exit: int
  )
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeInvalidTabs then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) +
      Spec.InvalidTabsMessage(cmd.invalidTabsValue) &&
      exit == 1
    else
      exists output: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes, hadError: bool ::
        InputTraceSummary(
          cmd, old(io.fs()), old(io.stdin()), io.stdin(),
          output, errorOutput, hadError,
          old(io.trustedStreams())
        ) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0)
  }

  method RunCore(raw: Schema.ExpandCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);

    match cmd.mode
    case ModeHelp =>
      var help := Spec.HelpText();
      var _ := io.WriteStdout(help, BenchWorld.ThrowOnError);
      exit := 0;
    case ModeVersion =>
      var version := Spec.VersionText();
      var _ := io.WriteStdout(version, BenchWorld.ThrowOnError);
      exit := 0;
    case ModeInvalidTabs =>
      var msg := Spec.InvalidTabsMessage(cmd.invalidTabsValue);
      var _ := io.WriteStderr(msg, BenchWorld.ThrowOnError);
      exit := 1;
    case ModeRun =>
      var out: BenchWorld.Bytes := [];
      var err: BenchWorld.Bytes := [];
      var hadError := false;
      var column: nat := 0;
      var leading := true;
      ghost var results: seq<BenchWorld.IOResult<BenchWorld.Bytes>> := [];
      ghost var outputPieces: seq<BenchWorld.Bytes> := [];
      ghost var errorPieces: seq<BenchWorld.Bytes> := [];
      ghost var errorFlags: seq<bool> := [];
      ghost var columns: seq<nat> := [0];
      ghost var leadings: seq<bool> := [true];
      ghost var stdinStates: seq<BenchWorld.Bytes> := [preStdin];
      var inputCount: nat := |cmd.inputs|;
      var i: nat := 0;
      while i < inputCount
        invariant inputCount == |cmd.inputs|
        invariant 0 <= i <= inputCount
        invariant io.stdout() == preStdout
        invariant io.stderr() == preStderr
        invariant |columns| == i + 1 && columns[i] == column
        invariant |leadings| == i + 1 && leadings[i] == leading
        invariant |stdinStates| == i + 1 && stdinStates[i] == io.stdin()
        invariant InputTracePrefixSummary(
                    cmd, preFs, preStdin, i, io.stdin(),
                    out, err, hadError, results, outputPieces,
                    errorPieces, errorFlags, columns, leadings, stdinStates,
                    old(io.trustedStreams())
                  )
        decreases *
      {
        var input := cmd.inputs[i];
        var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
        ghost var currentStdin := io.stdin();
        match input {
          case Stdin =>
            ghost var beforeStdin := io.stdin();
            var data :- assert io.ReadStdin(BenchWorld.ThrowOnError);
            readResult := Result.Ok(data);
            assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
          case File(path) =>
            readResult := io.ReadFile(path);
            assert readResult == IOContract.ObservedReadFileResultFields(preFs, old(io.trustedStreams()), path);
        }
        assert ReadStepSummary(
            input, preFs, currentStdin, io.stdin(), readResult,
            old(io.trustedStreams())
          );

        var outPiece, nextColumn, nextLeading :=
          ProcessInputPieceMethod(cmd, readResult, column, leading);
        var errPiece, hadPiece := ErrorPieceMethod(input, readResult);
        AppendInputTraceWitness(
          cmd, preFs, preStdin, i, currentStdin,
          out, err, hadError, results, outputPieces,
          errorPieces, errorFlags, columns, leadings, stdinStates,
          readResult, outPiece, errPiece, hadPiece,
          nextColumn, nextLeading, io.stdin(),
          old(io.trustedStreams())
        );
        out := out + outPiece;
        err := err + errPiece;
        hadError := hadError || hadPiece;
        column := nextColumn;
        leading := nextLeading;
        results := results + [readResult];
        outputPieces := outputPieces + [outPiece];
        errorPieces := errorPieces + [errPiece];
        errorFlags := errorFlags + [hadPiece];
        columns := columns + [nextColumn];
        leadings := leadings + [nextLeading];
        stdinStates := stdinStates + [io.stdin()];
        var next: nat := i + 1;
        assert next <= inputCount;
        assert inputCount - next < inputCount - i;
        i := next;
      }
      assert InputTraceSummary(
          cmd, preFs, preStdin, io.stdin(), out, err, hadError,
          old(io.trustedStreams())
        );
      var _ := io.WriteStdout(out, BenchWorld.ThrowOnError);
      var _ := io.WriteStderr(err, BenchWorld.ThrowOnError);
      exit := if hadError then 1 else 0;
      assert InputTraceSummary(
          cmd, preFs, preStdin, io.stdin(), out, err, hadError,
          old(io.trustedStreams())
        );
      assert exists
          output: BenchWorld.Bytes,
          errorOutput: BenchWorld.Bytes,
          failed: bool ::
          InputTraceSummary(
            cmd, preFs, preStdin, io.stdin(),
            output, errorOutput, failed,
            old(io.trustedStreams())
          ) &&
          io.stdout() == preStdout + output &&
          io.stderr() == preStderr + errorOutput &&
          exit == (if failed then 1 else 0);

  }
}
