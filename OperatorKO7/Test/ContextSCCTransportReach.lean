import OperatorKO7.Meta.ContextSCCTransport

/-!
# Finite SCC and Boundary Coexistence Reach Checks

These checks exercise the finite SCC certificate, its abstract round-trip
theorem, and the independent KO7 boundary facts bundled with it. Projection
examples confirm the carrier and edge relation of the canonical two-node
`Bool` certificate.

The checks do not assert a map from graph nodes to KO7 terms or a transport from
graph edges to KO7 rewrite steps.
-/

namespace OperatorKO7.ContextSCCTransport

open OperatorKO7.ContextSCCTransport
open OperatorKO7.FiniteGraphSCC
open OperatorKO7.FiniteGraphReachability

/-! ## Public-name reach checks -/

#check @FiniteSCCCertificate
#check @boolSCCCertificate
#check @SCCRoundTrip
#check @scc_certificate_roundtrip
#check @scc_roundtrip_and_context_root_orientation
#check @scc_roundtrip_and_DWO_boundary
#check @finite_scc_boundary_coexistence_bundle

/-! ## Concrete-certificate projections

The canonical certificate `boolSCCCertificate` is the two-node
fully-connected `Bool` graph. The projections below confirm the structure
fields resolve to the expected concrete carriers.
-/

example : boolSCCCertificate.Node = Bool := rfl

example :
    boolSCCCertificate.edge = boolFullEdge := rfl

example :
    boolSCCCertificate.scc = boolFullEdge_hasNontrivialSCC := rfl

/-! ## Round-trip preservation on the canonical certificate -/

example :
    witnessSrc (α := Bool)
        boolSCCCertificate.edge
        boolSCCCertificate.scc
      ≠
    witnessDst (α := Bool)
        boolSCCCertificate.edge
        boolSCCCertificate.scc :=
  (scc_certificate_roundtrip boolSCCCertificate).1

example :
    Reachable (α := Bool)
        boolSCCCertificate.edge
        (witnessSrc (α := Bool)
            boolSCCCertificate.edge
            boolSCCCertificate.scc)
        (witnessDst (α := Bool)
            boolSCCCertificate.edge
            boolSCCCertificate.scc) :=
  (scc_certificate_roundtrip boolSCCCertificate).2.1

example :
    Reachable (α := Bool)
        boolSCCCertificate.edge
        (witnessDst (α := Bool)
            boolSCCCertificate.edge
            boolSCCCertificate.scc)
        (witnessSrc (α := Bool)
            boolSCCCertificate.edge
            boolSCCCertificate.scc) :=
  (scc_certificate_roundtrip boolSCCCertificate).2.2

/-! ## Coexistence bundle on the canonical certificate -/

example :=
  finite_scc_boundary_coexistence_bundle boolSCCCertificate

end OperatorKO7.ContextSCCTransport
