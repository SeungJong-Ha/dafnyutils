include "../../../bench/core/IO.dfy"

module StreamCopy {
  import BenchIO
  import C = IOContract

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures readErr == 0 && writeErr == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin())
  {
    var read := io.ReadStdin(BenchIO.BenchWorld.ReturnError);
    var data := C.ReadResultData(read);
    readErr := C.ResultErrno(read);
    var write := io.WriteStdout(data, BenchIO.BenchWorld.ReturnError);
    writeErr := C.ResultErrno(write);
  }

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var readErr, writeErr := CopyInput(BenchIO.Process());
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }
}
