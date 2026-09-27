include "UnlinkSpec.dfy"
include "UnlinkCore.dfy"

module UnlinkProof {
  import BenchIO
  import Schema = UnlinkSchema
  import Core = UnlinkCore
  import Spec = UnlinkSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.UnlinkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
