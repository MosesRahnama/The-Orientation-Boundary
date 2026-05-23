import OperatorKO7.Meta.ContextSCCTransport

/-!
# Phase D Context-SCC Transport Reach Checks

Reach checks for the Phase D context-SCC transport certificate surface. Every
public name listed in the dispatch is exercised by an `#check` here, and a few
small instance / projection facts on the canonical two-node `Bool` certificate
are stated as `example` results.

This file is a structural-shape sanity layer; it does not introduce any new
theorems. All assertions are decidable / immediate from the module surface.
-/

namespace OperatorKO7.ContextSCCTransport

open OperatorKO7.ContextSCCTransport
open OperatorKO7.FiniteGraphSCC
open OperatorKO7.FiniteGraphReachability

/-! ## Public-name reach checks -/

#check @ContextSCCTransportCertificate
#check @contextSCCTransportCertificate
#check @scc_transport_preserves_roundtrip
#check @context_closed_barrier_transports_via_scc_certificate
#check @context_scc_transport_preserves_DWO_boundary
#check @phaseD_context_scc_transport_closed

/-! ## Concrete-certificate projections

The canonical certificate `contextSCCTransportCertificate` is the two-node
fully-connected `Bool` graph. The projections below confirm the structure
fields resolve to the expected concrete carriers.
-/

example : contextSCCTransportCertificate.Node = Bool := rfl

example :
    contextSCCTransportCertificate.edge = boolFullEdge := rfl

example :
    contextSCCTransportCertificate.scc = boolFullEdge_hasNontrivialSCC := rfl

/-! ## Round-trip preservation on the canonical certificate -/

example :
    witnessSrc (α := Bool)
        contextSCCTransportCertificate.edge
        contextSCCTransportCertificate.scc
      ≠
    witnessDst (α := Bool)
        contextSCCTransportCertificate.edge
        contextSCCTransportCertificate.scc :=
  (scc_transport_preserves_roundtrip contextSCCTransportCertificate).1

example :
    Reachable (α := Bool)
        contextSCCTransportCertificate.edge
        (witnessSrc (α := Bool)
            contextSCCTransportCertificate.edge
            contextSCCTransportCertificate.scc)
        (witnessDst (α := Bool)
            contextSCCTransportCertificate.edge
            contextSCCTransportCertificate.scc) :=
  (scc_transport_preserves_roundtrip contextSCCTransportCertificate).2.1

example :
    Reachable (α := Bool)
        contextSCCTransportCertificate.edge
        (witnessDst (α := Bool)
            contextSCCTransportCertificate.edge
            contextSCCTransportCertificate.scc)
        (witnessSrc (α := Bool)
            contextSCCTransportCertificate.edge
            contextSCCTransportCertificate.scc) :=
  (scc_transport_preserves_roundtrip contextSCCTransportCertificate).2.2

/-! ## Phase D closure marker on the canonical certificate -/

example :=
  phaseD_context_scc_transport_closed contextSCCTransportCertificate

end OperatorKO7.ContextSCCTransport
