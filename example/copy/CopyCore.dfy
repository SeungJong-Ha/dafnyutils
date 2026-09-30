include "CopySpec.dfy"

module CopyCore {
  import BenchIO
  import CopySpec

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures CopySpec.CopyResult(io, readErr, writeErr)
  {
    var data;
    data, readErr := io.ReadStdin(BenchIO.BenchWorld.ReturnError);
    var committed;
    committed, writeErr := io.WriteStdout(data, BenchIO.BenchWorld.ReturnError);
  }
}
