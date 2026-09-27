include "Unlink.dfy"

module UnlinkCli {
  import BenchIO
  import BenchItem
  import Unlink

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    // Match the repository's .NET entry convention.
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["unlink"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Unlink.UnlinkBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
