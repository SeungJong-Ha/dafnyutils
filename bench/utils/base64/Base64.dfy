include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "Base64Schema.dfy"
include "Base64Core.dfy"
include "Base64Spec.dfy"
include "Base64Proof.dfy"

module Base64 {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = Base64Schema
  import Core = Base64Core
  import ES = Base64Spec
  import Proof = Base64Proof

  datatype FixedNatParse = FixedNatOk(value: nat) | FixedNatErr
  datatype FixedWrapParse = FixedWrapParse(
    hasInvalid: bool,
    invalidText: string,
    invalidTokenIndex: int,
    width: nat
  )

  function FixedIsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function FixedDigitValue(ch: char): nat
    requires FixedIsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function FixedParseNatFrom(text: string, i: nat, acc: nat): FixedNatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      FixedNatOk(acc)
    else if !FixedIsDigit(text[i]) then
      FixedNatErr
    else
      FixedParseNatFrom(text, i + 1, acc * 10 + FixedDigitValue(text[i]))
  }

  function FixedParseNat(text: string): FixedNatParse
  {
    if |text| == 0 then FixedNatErr else FixedParseNatFrom(text, 0, 0)
  }

  function FixedParseWrapArgs(
    args: seq<S.WidthArg>,
    width: nat
  ): FixedWrapParse
    decreases |args|
  {
    if |args| == 0 then
      FixedWrapParse(false, "", -1, width)
    else
      match FixedParseNat(args[0].text)
      case FixedNatErr =>
        FixedWrapParse(true, args[0].text, args[0].tokenIndex, width)
      case FixedNatOk(nextWidth) =>
        FixedParseWrapArgs(args[1..], nextWidth)
  }

  class {:termination false} Base64BenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.Base64CmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "base64";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.Base64CmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.Base64FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.Base64CmdRaw>)
      decreases *
    {
      var seenHelp := false;
      var seenVersion := false;
      var helpTokenIndex := -1;
      var versionTokenIndex := -1;
      var wrapArgs: seq<S.WidthArg> := [];

      var i := 0;
      while i < |argv| && i < err.tokenIndex
        decreases |argv| - i
      {
        var token := argv[i];
        var consumedNext := false;
        if token == "--help" {
          seenHelp := true;
          if helpTokenIndex == -1 {
            helpTokenIndex := i;
          }
        } else if token == "--version" {
          seenVersion := true;
          if versionTokenIndex == -1 {
            versionTokenIndex := i;
          }
        } else if token == "-w" || token == "--wrap" {
          if i + 1 < |argv| && i + 1 < err.tokenIndex {
            wrapArgs := wrapArgs + [S.WidthArg(argv[i + 1], i)];
            consumedNext := true;
          }
        } else if 7 <= |token| && token[..7] == "--wrap=" {
          wrapArgs := wrapArgs + [S.WidthArg(token[7..], i)];
        } else if |token| > 2 && token[0] == '-' && token[1] == 'w' {
          wrapArgs := wrapArgs + [S.WidthArg(token[2..], i)];
        }

        if consumedNext {
          i := i + 2;
        } else {
          i := i + 1;
        }
      }

      var raw := S.Base64CmdRaw(
        false,
        false,
        seenHelp,
        seenVersion,
        helpTokenIndex,
        versionTokenIndex,
        wrapArgs,
        []
      );
      var wrapPlan := FixedParseWrapArgs(wrapArgs, 76);
      if seenHelp &&
         (!seenVersion || helpTokenIndex <= versionTokenIndex) &&
         (!wrapPlan.hasInvalid || helpTokenIndex <= wrapPlan.invalidTokenIndex) {
        plan := CliTypes.CliRun(raw);
        return;
      }
      if seenVersion &&
         (!wrapPlan.hasInvalid || versionTokenIndex <= wrapPlan.invalidTokenIndex) {
        plan := CliTypes.CliRun(raw);
        return;
      }
      if wrapPlan.hasInvalid {
        plan := CliTypes.CliRun(raw);
        return;
      }

      var msg := S.Base64FormatParseError(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.Base64CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
