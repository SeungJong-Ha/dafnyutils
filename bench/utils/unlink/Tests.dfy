include "UnlinkSchema.dfy"

module UnlinkTests {
  import S = UnlinkSchema
  import C = CliTypes

  // Ordinary operands select execution mode and retain their pathname.
  method {:test} TestOrdinaryOperand() {
    var parsed := C.ParsedArgs("unlink", [], ["target"], false);
    var raw := S.Decode(parsed);
    expect raw.mode == S.ModeRun;
    expect raw.operands == ["target"];
  }

  // Help preceding version selects help mode.
  method {:test} TestHelpBeforeVersion() {
    var parsed := C.ParsedArgs("unlink", [
      C.OptOccurrence("unlink.help", C.Long("help"), C.None, 0, "--help"),
      C.OptOccurrence("unlink.version", C.Long("version"), C.None, 1, "--version")
    ], [], false);
    var raw := S.Decode(parsed);
    expect raw.mode == S.ModeHelp;
  }

}
