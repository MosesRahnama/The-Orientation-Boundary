import OperatorKO7.Meta.FiniteGraphSCC
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.DirectWholeTermObserver
import OperatorKO7.Meta.DirectBarrierScope
import Mathlib.Logic.Relation

/-!
# Finite SCC and Boundary Coexistence

This module packages a finite decidable directed graph with a nontrivial SCC and
places its round-trip theorem beside two independent KO7 boundary results. The
certificate contains no map from graph nodes to `Trace` and no edge-to-rewrite
transport law. Accordingly, the combined theorems assert coexistence, not
transport between the abstract graph and the KO7 rewrite relation.

The canonical two-node `Bool` certificate provides a concrete nontrivial SCC.
The KO7 components reuse
`ContextClosedBarrier.stepCtxFull_orientation_implies_root` and
`no_direct_orientation_of_payload_exposure` without changing their scopes.
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

/-- A finite decidable directed graph together with a witness of a nontrivial
strongly connected component. The structure carries no `Trace` interpretation. -/
structure FiniteSCCCertificate where
  Node : Type
  fintype : Fintype Node
  decEq : DecidableEq Node
  edge : Node → Node → Prop
  decRel : DecidableRel edge
  scc : HasNontrivialSCC (α := Node) edge

attribute [instance] FiniteSCCCertificate.fintype
attribute [instance] FiniteSCCCertificate.decEq
attribute [instance] FiniteSCCCertificate.decRel

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

/-- Finite SCC certificate instantiated by the fully connected two-node `Bool` graph. -/
def boolSCCCertificate : FiniteSCCCertificate where
  Node := Bool
  fintype := inferInstance
  decEq := inferInstance
  edge := boolFullEdge
  decRel := instDecidableBoolFullEdge
  scc := boolFullEdge_hasNontrivialSCC

/-! ## Abstract round trip -/

/-- The two distinguished nodes of a finite SCC certificate are distinct and
mutually reachable in the certificate's abstract graph. -/
def SCCRoundTrip (C : FiniteSCCCertificate) : Prop :=
  witnessSrc (α := C.Node) C.edge C.scc ≠ witnessDst (α := C.Node) C.edge C.scc ∧
    Reachable (α := C.Node) C.edge
        (witnessSrc (α := C.Node) C.edge C.scc)
        (witnessDst (α := C.Node) C.edge C.scc) ∧
    Reachable (α := C.Node) C.edge
        (witnessDst (α := C.Node) C.edge C.scc)
        (witnessSrc (α := C.Node) C.edge C.scc)

/-- Every finite SCC certificate supplies its distinguished abstract round trip. -/
theorem scc_certificate_roundtrip (C : FiniteSCCCertificate) : SCCRoundTrip C := by
  exact ⟨witnessSrc_ne_witnessDst (R := C.edge) C.scc,
    reachable_witnessSrc_witnessDst (R := C.edge) C.scc,
    reachable_witnessDst_witnessSrc (R := C.edge) C.scc⟩

/-! ## Independent KO7 boundary results -/

/-- Packages the certificate's abstract round trip with the independent fact
that orientation of `StepCtxFull` entails orientation of the KO7 root step. -/
theorem scc_roundtrip_and_context_root_orientation
    (C : FiniteSCCCertificate)
    {α : Type} {m : Trace → α} {lt : α → α → Prop}
    (h : GlobalOrientsStepCtxFull m lt) :
    SCCRoundTrip C ∧ StepDuplicatingSchema.GlobalOrients ko7System m lt := by
  exact ⟨scc_certificate_roundtrip C, stepCtxFull_orientation_implies_root h⟩

/-- Packages the certificate's abstract round trip with the direct-observer
barrier for a strictly exposed, visible, carrier-sensitive payload coordinate. -/
theorem scc_roundtrip_and_DWO_boundary
    (C : FiniteSCCCertificate)
    {F : DuplicatingRecursiveFamily}
    (O : DirectWholeTermObserver F)
    {i : F.schema.PayloadCoord}
    (hPump : F.HasUnboundedPayloadPump i)
    (hExposure : F.ExposesPayloadStrictly i)
    (hVisible : O.visiblePayloadCoordinate i)
    (hSensitive : O.carrierSensitive i) :
    SCCRoundTrip C ∧ ¬ F.GloballyOrients O := by
  exact ⟨scc_certificate_roundtrip C,
    no_direct_orientation_of_payload_exposure O hPump hExposure hVisible hSensitive⟩

/-! ## Coexistence bundle -/

/-- Bundles three separately scoped facts: the certificate's abstract SCC round
trip, the projection from full contextual orientation to KO7 root orientation,
and the direct-observer boundary. No graph node or edge is interpreted as a KO7
term or rewrite step. -/
theorem finite_scc_boundary_coexistence_bundle
    (C : FiniteSCCCertificate) :
    SCCRoundTrip C
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
  refine ⟨scc_certificate_roundtrip C, ?_, ?_⟩
  · intro α m lt h
    exact stepCtxFull_orientation_implies_root h
  · intro F O i hPump hExposure hVisible hSensitive
    exact no_direct_orientation_of_payload_exposure O hPump hExposure hVisible hSensitive

end OperatorKO7.ContextSCCTransport
