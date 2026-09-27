include "../../core/BenchmarkItem.dfy"
include "UnlinkSpec.dfy"
include "UnlinkCore.dfy"
include "UnlinkProof.dfy"

module Unlink {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = UnlinkSchema
  import Core = UnlinkCore
  import Spec = UnlinkSpec
  import Proof = UnlinkProof

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
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.UnlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
