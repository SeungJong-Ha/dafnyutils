include "../../core/CliTypes.dfy"

module UnlinkSchema {
  import CliTypes

  // TODO: replace this wrapper with the utility's decoded command fields.
  datatype UnlinkCmdRaw = UnlinkCmdRaw(parsed: CliTypes.ParsedArgs)

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    // TODO: declare the accepted options and their argument requirements.
    assert false;
    schema := CliTypes.CliSchema([], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    // TODO: choose the parsing rules from the pinned GNU source.
    assert false;
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: UnlinkCmdRaw)
  {
    raw := UnlinkCmdRaw(parsed);
  }
}
