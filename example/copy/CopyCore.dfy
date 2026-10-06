include "CopySpec.dfy"

module CopyCore {
  import BenchIO
  import CopySpec
  import C = IOContract

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures CopySpec.CopyResult(io, readErr, writeErr)
  {
    var read := io.ReadStdin(BenchIO.BenchWorld.ReturnError);
    var data := C.ReadResultData(read);
    readErr := C.ResultErrno(read);
    var write := io.WriteStdout(data, BenchIO.BenchWorld.ReturnError);
    writeErr := C.ResultErrno(write);
  }
}
