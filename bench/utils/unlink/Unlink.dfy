include "../../core/BenchmarkItem.dfy"
include "../../core/Utf8.dfy"
include "UnlinkSchema.dfy"
include "UnlinkSpec.dfy"
include "UnlinkCore.dfy"
include "UnlinkProof.dfy"

module Unlink {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import Utf8 = Utf8Semantics
  import S = UnlinkSchema
  import Core = UnlinkCore
  import Spec = UnlinkSpec
  import Proof = UnlinkProof
  import opened CliExtern

  class UnlinkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.UnlinkCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "unlink";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.UnlinkCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test GNU parse-error behavior, including early exits.
      msg := Spec.ParseErrorText(err);
    }

    method PlanParseFailure(
      e: CliTypes.ParseError,
      argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<S.UnlinkCmdRaw>)
      decreases *
    {
      if 0 < e.tokenIndex && e.tokenIndex < |argv| {
        var s := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..e.tokenIndex], s, cfg);
        match result {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            if raw.mode == S.ModeHelp || raw.mode == S.ModeVersion {
              plan := CliTypes.CliRun(raw);
              return;
            }
          case ParseFailure(_) =>
        }
      }
      var msg := Spec.ParseErrorText(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.UnlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
