include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/StringEscaping.dfy"

module NlSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes
  import SE = StringEscaping

  datatype NlMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeInvalidBodyStyle(value: string)
    | ModeUnsupportedRegexBodyStyle(value: string)
    | ModeInvalidNumberFormat(value: string)
    | ModeInvalidOptions

  datatype NlOptionError =
    | InvalidBodyStyle(value: string)
    | InvalidNumberFormat(value: string)

  datatype BodyStyle = NumberAll | NumberNonEmpty | NumberNone
  datatype NumberFormat = FormatLeft | FormatRight | FormatRightZero
  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype NlCmdRaw = NlCmdRaw(
    bodyStyle: CliTypes.OptionalString,
    numberFormat: CliTypes.OptionalString,
    separator: CliTypes.OptionalString,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    optionErrors: seq<NlOptionError>,
    operands: seq<string>
  )

  datatype NlCmd = NlCmd(
    mode: NlMode,
    bodyStyle: BodyStyle,
    numberFormat: NumberFormat,
    separator: string,
    optionErrors: seq<NlOptionError>,
    inputs: seq<Input>
  )

  function InputsFromOperands(operands: seq<string>): seq<Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then Stdin else File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function BodyStyleMode(opt: CliTypes.OptionalString): NlMode
  {
    match opt
    case None => ModeRun
    case Some(value) =>
      if |value| == 0 then
        ModeInvalidBodyStyle(value)
      else if value[0] == 'p' then
        ModeUnsupportedRegexBodyStyle(value)
      else if value[0] == 'a' || value[0] == 't' || value[0] == 'n' then
        ModeRun
      else
        ModeInvalidBodyStyle(value)
  }

  function BodyStyleValue(opt: CliTypes.OptionalString): BodyStyle
  {
    match opt
    case Some(value) =>
      if |value| > 0 && value[0] == 'a' then
        NumberAll
      else if |value| > 0 && value[0] == 'n' then
        NumberNone
      else
        NumberNonEmpty
    case None => NumberNonEmpty
  }

  function NumberFormatMode(opt: CliTypes.OptionalString): NlMode
  {
    match opt
    case None => ModeRun
    case Some(value) =>
      if value == "ln" || value == "rn" || value == "rz" then
        ModeRun
      else
        ModeInvalidNumberFormat(value)
  }

  function NumberFormatValue(opt: CliTypes.OptionalString): NumberFormat
  {
    match opt
    case Some(value) =>
      if value == "ln" then
        FormatLeft
      else if value == "rz" then
        FormatRightZero
      else
        FormatRight
    case None => FormatRight
  }

  function SeparatorValue(opt: CliTypes.OptionalString): string
  {
    match opt
    case Some(value) => value
    case None => "\t"
  }

  function Command(raw: NlCmdRaw): NlCmd
  {
    var specialMode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    var bodyMode := BodyStyleMode(raw.bodyStyle);
    var formatMode := NumberFormatMode(raw.numberFormat);
    var mode :=
      if specialMode != ModeRun then
        specialMode
      else if |raw.optionErrors| > 0 then
        ModeInvalidOptions
      else if bodyMode != ModeRun then
        bodyMode
      else if formatMode != ModeRun then
        formatMode
      else
        ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == ModeRun && |inputs| == 0 then [Stdin] else inputs;
    NlCmd(
      mode,
      BodyStyleValue(raw.bodyStyle),
      NumberFormatValue(raw.numberFormat),
      SeparatorValue(raw.separator),
      raw.optionErrors,
      runInputs
    )
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("nl.body_numbering", ['b'], ["body-numbering"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.number_format", ['n'], ["number-format"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.number_separator", ['s'], ["number-separator"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("nl.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: NlCmdRaw)
  {
    var bodyStyle: CliTypes.OptionalString := CliTypes.None;
    var numberFormat: CliTypes.OptionalString := CliTypes.None;
    var separator: CliTypes.OptionalString := CliTypes.None;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var optionErrors: seq<NlOptionError> := [];
    var stopped := false;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if !stopped && occ.key == "nl.body_numbering" {
        bodyStyle := occ.value;
        match occ.value {
          case Some(value) =>
            if BodyStyleMode(occ.value) == ModeInvalidBodyStyle(value) {
              optionErrors := optionErrors + [InvalidBodyStyle(value)];
            }
          case None =>
        }
      }
      if !stopped && occ.key == "nl.number_format" {
        numberFormat := occ.value;
        match occ.value {
          case Some(value) =>
            if NumberFormatMode(occ.value) == ModeInvalidNumberFormat(value) {
              optionErrors := optionErrors + [InvalidNumberFormat(value)];
            }
          case None =>
        }
      }
      if !stopped && occ.key == "nl.number_separator" {
        separator := occ.value;
      }
      if !stopped && occ.key == "nl.help" {
        seenHelp := true;
        helpTokenIndex := occ.tokenIndex;
        stopped := true;
      }
      if !stopped && occ.key == "nl.version" {
        seenVersion := true;
        versionTokenIndex := occ.tokenIndex;
        stopped := true;
      }
      i := i + 1;
    }

    raw := NlCmdRaw(
      bodyStyle,
      numberFormat,
      separator,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      optionErrors,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "nl: unrecognized option '" + e.rawToken + "'\n" + TryHelp()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [e.rawToken[1]];
        "nl: invalid option -- '" + option + "'\n" + TryHelp()
      else
        "nl: invalid option\n" + TryHelp()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "nl: option '" + e.rawToken + "' requires an argument\n" + TryHelp()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [e.rawToken[|e.rawToken| - 1]];
        "nl: option requires an argument -- '" + option + "'\n" + TryHelp()
      else
        "nl: option requires an argument\n" + TryHelp()
    else if e.kind == CliTypes.Ambiguous then
      "nl: option '" + e.rawToken + "' is ambiguous\n" + TryHelp()
    else if e.kind == CliTypes.UnexpectedValue then
      "nl: option '" + e.rawToken + "' doesn't allow an argument\n" + TryHelp()
    else
      "nl: parse error at token '" + e.rawToken + "'\n"
  }

  function TryHelp(): BenchWorld.Bytes
  {
    "Try 'nl --help' for more information.\n"
  }

  function InvalidBodyStyleLine(value: string): BenchWorld.Bytes
  {
    "nl: invalid body numbering style: " +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) + "\n"
  }

  function InvalidNumberFormatLine(value: string): BenchWorld.Bytes
  {
    "nl: invalid line numbering format: " +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) + "\n"
  }

  function OptionErrorLine(error: NlOptionError): BenchWorld.Bytes
  {
    match error
    case InvalidBodyStyle(value) => InvalidBodyStyleLine(value)
    case InvalidNumberFormat(value) => InvalidNumberFormatLine(value)
  }

  function OptionErrorsText(errors: seq<NlOptionError>): BenchWorld.Bytes
    decreases |errors|
  {
    if |errors| == 0 then
      []
    else
      OptionErrorLine(errors[0]) + OptionErrorsText(errors[1..])
  }

  method PriorOptionState(
    argv: seq<string>,
    limit: int
  ) returns (errors: seq<NlOptionError>, request: CliTypes.PriorRequest)
    decreases *
  {
    errors := [];
    request := CliTypes.RequestNone;
    var i := 0;
    while i < |argv| && i < limit
      decreases |argv| - i
    {
      var token := argv[i];
      if token == "--" {
        return;
      }
      if token == "--help" {
        request := CliTypes.RequestHelp;
        return;
      }
      if token == "--version" {
        request := CliTypes.RequestVersion;
        return;
      }

      var value := "";
      var hasBodyValue := false;
      var hasFormatValue := false;
      var consumedNext := false;
      if token == "-b" || token == "--body-numbering" {
        if i + 1 < |argv| && i + 1 < limit {
          value := argv[i + 1];
          hasBodyValue := true;
          consumedNext := true;
        }
      } else if 17 <= |token| && token[..17] == "--body-numbering=" {
        value := token[17..];
        hasBodyValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'b' {
        value := token[2..];
        hasBodyValue := true;
      } else if token == "-n" || token == "--number-format" {
        if i + 1 < |argv| && i + 1 < limit {
          value := argv[i + 1];
          hasFormatValue := true;
          consumedNext := true;
        }
      } else if 16 <= |token| && token[..16] == "--number-format=" {
        value := token[16..];
        hasFormatValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'n' {
        value := token[2..];
        hasFormatValue := true;
      } else if token == "-s" || token == "--number-separator" {
        if i + 1 < |argv| && i + 1 < limit {
          consumedNext := true;
        }
      }

      if hasBodyValue && BodyStyleMode(CliTypes.Some(value)) == ModeInvalidBodyStyle(value) {
        errors := errors + [InvalidBodyStyle(value)];
      }
      if hasFormatValue && NumberFormatMode(CliTypes.Some(value)) == ModeInvalidNumberFormat(value) {
        errors := errors + [InvalidNumberFormat(value)];
      }

      if consumedNext {
        i := i + 2;
      } else {
        i := i + 1;
      }
    }
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<NlCmdRaw>)
    decreases *
  {
    var errors, request := PriorOptionState(argv, e.tokenIndex);
    if request == CliTypes.RequestHelp {
      plan := CliTypes.CliRun(NlCmdRaw(
        CliTypes.None, CliTypes.None, CliTypes.None,
        true, false, 0, -1, errors, []
      ));
      return;
    }
    if request == CliTypes.RequestVersion {
      plan := CliTypes.CliRun(NlCmdRaw(
        CliTypes.None, CliTypes.None, CliTypes.None,
        false, true, -1, 0, errors, []
      ));
      return;
    }
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], OptionErrorsText(errors) + msg);
  }
}
