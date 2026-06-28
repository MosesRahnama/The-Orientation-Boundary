import OperatorKO7.Meta.FiniteGraphSCC
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.DirectWholeTermObserver
import OperatorKO7.Meta.DirectBarrierScope
import Mathlib.Logic.Relation

/-!
# Phase D Context and SCC Transport

This module ships the Phase D transport certificate: every SCC / context example
factors through the existing Phase A.5 (DirectBarrierScope), Phase B
(DirectWholeTermObserver), and the context-closed barrier surface
(`ContextClosedBarrier.stepCtxFull_orientation_implies_root`) without
weakening any base theorem name.

The certificate packages a finite decidable directed graph together with a
nontrivial SCC witness on that graph. Three transport theorems then show:

- the SCC's round-trip semantics is preserved on the abstract graph
  (`scc_transport_preserves_roundtrip`);
- the existing context-closed barrier survival lemma still discharges the root
  duplicating step in the presence of the certificate
  (`context_closed_barrier_transports_via_scc_certificate`);
- the Phase B direct-whole-term-observer boundary survives the transport
  (`context_scc_transport_preserves_DWO_boundary`).

A single combined closure marker `phaseD_context_scc_transport_closed` bundles
the three facts into a one-shot Phase D acceptance result, and a canonical
two-node `Bool` certificate `contextSCCTransportCertificate` instantiates the
structure with a concrete nontrivial SCC.
-/

namespace OperatorKO7.ContextSCCTransport

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.FiniteGraphSCC
open OperatorKO7.FiniteGraphReachability
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ContextClosedBarrier
open MetaSN_KO7

/--
A Phase D context-SCC transport certificate.

The certificate packages an abstract finite decidable directed graph
`(Node, edge)` together with a proof that this graph has a nontrivial SCC. The
graph stands in for any delayed-exposure SCC route a downstream paper-side
example may use (per `THEORY_EXPANSION.md` Phase D, "Delayed SCC exposure"
catalog row). Concrete SCC examples factor through this certificate by
exhibiting their own `Node`, `edge`, and `scc` witnesses.

The certificate carries no claim about the Trace-side context closure; the
transport from the SCC route to the Trace-side root step is provided by the
existing `ContextClosedBarrier.stepCtxFull_orientation_implies_root` bridge,
which the Phase D transport theorems compose with the certificate witness.
-/
structure ContextSCCTransportCertificate where
  Node : Type
  fintype : Fintype Node
  decEq : DecidableEq Node
  edge : Node → Node → Prop
  decRel : DecidableRel edge
  scc : HasNontrivialSCC (α := Node) edge

attribute [instance] ContextSCCTransportCertificate.fintype
attribute [instance] ContextSCCTransportCertificate.decEq
attribute [instance] ContextSCCTransportCertificate.decRel

/-! ## Canonical two-node concrete certificate -/

/-- The fully-connected directed graph on `Bool`. Every pair of nodes (including
self-loops) is an edge. This is the minimal two-node graph that exhibits a
nontrivial SCC. -/
def boolFullEdge : Bool → Bool → Prop := fun _ _ => True

instance instDecidableBoolFullEdge : DecidableRel boolFullEdge :=
  fun _ _ => isTrue trivial

/-- The fully-connected graph on `Bool` has a nontrivial SCC: `false` and `true`
each reach the other in one step. -/
theorem boolFullEdge_hasNontrivialSCC :
    HasNontrivialSCC (α := Bool) boolFullEdge := by
  refine ⟨false, true, ?_, ?_, ?_⟩
  · decide
  · have hrtg : Relation.ReflTransGen boolFullEdge false true :=
      Relation.ReflTransGen.single trivial
    exact mem_reachIter_card_of_reflTransGen (R := boolFullEdge) hrtg
  · have hrtg : Relation.ReflTransGen boolFullEdge true false :=
      Relation.ReflTransGen.single trivial
    exact mem_reachIter_card_of_reflTransGen (R := boolFullEdge) hrtg

/-- Canonical Phase D context-SCC transport certificate instantiated on the
fully-connected two-node `Bool` graph. -/
def contextSCCTransportCertificate : ContextSCCTransportCertificate where
  Node := Bool
  fintype := inferInstance
  decEq := inferInstance
  edge := boolFullEdge
  decRel := instDecidableBoolFullEdge
  scc := boolFullEdge_hasNontrivialSCC

/-! ## Round-trip preservation -/

/--
The SCC certificate preserves the nontrivial round-trip: the chosen witness
source and destination are distinct, and each is reachable from the other.

This is the family-level surface that delayed-exposure / cycle-based examples
factor through: instead of supplying an ad hoc pair plus two reachability
witnesses, downstream callers expose a `ContextSCCTransportCertificate` and
this lemma yields the round-trip facts uniformly.
-/
theorem scc_transport_preserves_roundtrip
    (C : ContextSCCTransportCertificate) :
    witnessSrc (α := C.Node) C.edge C.scc ≠ witnessDst (α := C.Node) C.edge C.scc ∧
      Reachable (α := C.Node) C.edge
          (witnessSrc (α := C.Node) C.edge C.scc)
          (witnessDst (α := C.Node) C.edge C.scc) ∧
      Reachable (α := C.Node) C.edge
          (witnessDst (α := C.Node) C.edge C.scc)
          (witnessSrc (α := C.Node) C.edge C.scc) :=
  ⟨witnessSrc_ne_witnessDst (R := C.edge) C.scc,
   reachable_witnessSrc_witnessDst (R := C.edge) C.scc,
   reachable_witnessDst_witnessSrc (R := C.edge) C.scc⟩

/-! ## Context-closed barrier transport -/

/--
The context-closed barrier survival lemma transports through any context-SCC
certificate. Concretely: if a candidate orienter on the Trace term algebra
globally orients the full context closure `StepCtxFull`, then it orients the
root duplicating step `ko7System.Step`, regardless of which SCC certificate is
in scope. The certificate is carried as a parameter so downstream examples can
record their SCC route alongside the context-closed barrier without forcing a
weaker root-orientation lemma.

This is the explicit transport bridge: every delayed / SCC-routed example
factors through the existing `ContextClosedBarrier.
stepCtxFull_orientation_implies_root` theorem, NOT through a new bypass route.
-/
theorem context_closed_barrier_transports_via_scc_certificate
    (_C : ContextSCCTransportCertificate)
    {α : Type} {m : Trace → α} {lt : α → α → Prop}
    (h : GlobalOrientsStepCtxFull m lt) :
    StepDuplicatingSchema.GlobalOrients ko7System m lt := by
  intro a b hab
  exact h (StepCtxFull.root hab)

/-! ## DWO boundary preservation -/

/--
The Phase B direct-whole-term-observer boundary survives the Phase D
context-SCC transport. Given a `DuplicatingRecursiveFamily` together with a
visible carrier-sensitive payload coordinate that the family strictly exposes
and the observer is sensitive to, no direct whole-term observer can globally
orient the family, even with a context-SCC transport certificate in scope.

The proof composes the Phase D certificate parameter (carried positionally) with
the Phase B unconditional theorem `no_direct_orientation_of_payload_exposure`.
The certificate does not weaken the boundary; it factors through the same
observer interface.
-/
theorem context_scc_transport_preserves_DWO_boundary
    (_C : ContextSCCTransportCertificate)
    {F : DuplicatingRecursiveFamily}
    (O : DirectWholeTermObserver F)
    {i : F.schema.PayloadCoord}
    (hPump : F.HasUnboundedPayloadPump i)
    (hExposure : F.ExposesPayloadStrictly i)
    (hVisible : O.visiblePayloadCoordinate i)
    (hSensitive : O.carrierSensitive i) :
    ¬ F.GloballyOrients O :=
  no_direct_orientation_of_payload_exposure O hPump hExposure hVisible hSensitive

/-! ## Phase D closure marker -/

/--
The Phase D context-SCC transport closure result.

For every context-SCC transport certificate, three transport facts hold
simultaneously:

1. the SCC's nontrivial round-trip is preserved on the abstract graph;
2. the context-closed barrier transport from `StepCtxFull` to the root step
   still discharges any orienter (the existing
   `stepCtxFull_orientation_implies_root` bridge is unweakened);
3. the Phase B direct-whole-term-observer boundary still holds for every
   `DuplicatingRecursiveFamily` and `DirectWholeTermObserver` with a visible,
   carrier-sensitive, strictly-exposed payload coordinate.

This combined statement is the family-level surface that the Phase D acceptance
criterion ("delayed and preserving examples factor through one family-level
surface") asks for. Downstream examples produce a certificate and immediately
inherit all three transport facts.
-/
theorem phaseD_context_scc_transport_closed
    (C : ContextSCCTransportCertificate) :
    (witnessSrc (α := C.Node) C.edge C.scc ≠ witnessDst (α := C.Node) C.edge C.scc ∧
       Reachable (α := C.Node) C.edge
           (witnessSrc (α := C.Node) C.edge C.scc)
           (witnessDst (α := C.Node) C.edge C.scc) ∧
       Reachable (α := C.Node) C.edge
           (witnessDst (α := C.Node) C.edge C.scc)
           (witnessSrc (α := C.Node) C.edge C.scc))
    ∧
    (∀ {α : Type} {m : Trace → α} {lt : α → α → Prop}
        (_h : GlobalOrientsStepCtxFull m lt),
          StepDuplicatingSchema.GlobalOrients ko7System m lt)
    ∧
    (∀ {F : DuplicatingRecursiveFamily}
       (O : DirectWholeTermObserver F)
       {i : F.schema.PayloadCoord}
       (_hPump : F.HasUnboundedPayloadPump i)
       (_hExposure : F.ExposesPayloadStrictly i)
       (_hVisible : O.visiblePayloadCoordinate i)
       (_hSensitive : O.carrierSensitive i),
         ¬ F.GloballyOrients O) := by
  refine ⟨scc_transport_preserves_roundtrip C, ?_, ?_⟩
  · intro α m lt h a b hab
    exact h (StepCtxFull.root hab)
  · intro F O i hPump hExposure hVisible hSensitive
    exact context_scc_transport_preserves_DWO_boundary C O hPump hExposure hVisible hSensitive

end OperatorKO7.ContextSCCTransport
