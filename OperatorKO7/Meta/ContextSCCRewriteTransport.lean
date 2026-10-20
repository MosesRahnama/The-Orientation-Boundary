import OperatorKO7.Meta.ContextSCCTransport
import OperatorKO7.Meta.MPO_FullStep

/-!
# From the finite SCC certificate to a rewrite relation

`Meta/ContextSCCTransport.lean` states plainly that its certificate "contains no map from graph
nodes to `Trace` and no edge-to-rewrite transport law", so its bundle asserts coexistence rather
than transport. This module supplies the transport that was missing, on the packet syntax the
certificate can carry rather than on `Trace`.

The construction is the obvious one and its content is the conclusion. A node of the certificate
becomes a one-node packet; an edge becomes a rewrite step between packets; reachability becomes the
reflexive transitive closure of that step. The nontrivial round trip of the certificate then lifts
to a rewrite cycle between two distinct packets, and a rewrite cycle is exactly non-termination:
`inducedStep_not_wellFounded` states that the reverse of the induced relation is not well founded,
for every certificate.

What this does not do is map nodes to `Trace`. The certificate has no such map and cannot acquire
one without naming the seven constructors, so the transport lands on the packet syntax and stops
there. `ko7_transport_needs_a_node_interpretation` records that boundary: a transport to `Trace`
would need a node interpretation, and the certificate carries none.

Relation: the induced packet rewrite relation. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.ContextSCCTransport

open OperatorKO7.FiniteGraphSCC
open OperatorKO7.FiniteGraphReachability

/-! ## The packet syntax the certificate induces -/

/-- A packet over a node type: the minimal syntax a graph node can be read into. -/
inductive Packet (Node : Type) where
  | at : Node → Packet Node

/-- The rewrite relation the certificate's edges induce on packets. -/
def inducedStep (C : FiniteSCCCertificate) : Packet C.Node → Packet C.Node → Prop
  | .at a, .at b => C.edge a b

/-- Reachability in the graph is the reflexive transitive closure of the induced rewrite step. -/
theorem reflTransGen_inducedStep_of_reachable (C : FiniteSCCCertificate) {a b : C.Node}
    (h : Reachable (α := C.Node) C.edge a b) :
    Relation.ReflTransGen (inducedStep C) (.at a) (.at b) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep

/-- **The transport.** Every finite SCC certificate induces a rewrite relation on packets in which
two distinct packets rewrite to each other. -/
theorem induced_rewrite_round_trip (C : FiniteSCCCertificate) :
    (Packet.at (witnessSrc (α := C.Node) C.edge C.scc) :
        Packet C.Node) ≠ Packet.at (witnessDst (α := C.Node) C.edge C.scc)
      ∧ Relation.ReflTransGen (inducedStep C)
          (.at (witnessSrc (α := C.Node) C.edge C.scc))
          (.at (witnessDst (α := C.Node) C.edge C.scc))
      ∧ Relation.ReflTransGen (inducedStep C)
          (.at (witnessDst (α := C.Node) C.edge C.scc))
          (.at (witnessSrc (α := C.Node) C.edge C.scc)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact witnessSrc_ne_witnessDst (R := C.edge) C.scc (Packet.at.inj h)
  · exact reflTransGen_inducedStep_of_reachable C
      (reachable_witnessSrc_witnessDst (R := C.edge) C.scc)
  · exact reflTransGen_inducedStep_of_reachable C
      (reachable_witnessDst_witnessSrc (R := C.edge) C.scc)

/-- The certificate's round trip is a cycle in the transitive closure of its edge relation. -/
theorem scc_transGen_cycle (C : FiniteSCCCertificate) :
    Relation.TransGen C.edge
        (witnessSrc (α := C.Node) C.edge C.scc) (witnessDst (α := C.Node) C.edge C.scc)
      ∧ Relation.TransGen C.edge
        (witnessDst (α := C.Node) C.edge C.scc) (witnessSrc (α := C.Node) C.edge C.scc) := by
  have hne := witnessSrc_ne_witnessDst (R := C.edge) C.scc
  refine ⟨?_, ?_⟩
  · rcases (reachable_iff_eq_or_transGen (R := C.edge)).1
      (reachable_witnessSrc_witnessDst (R := C.edge) C.scc) with h | h
    · exact absurd h.symm hne
    · exact h
  · rcases (reachable_iff_eq_or_transGen (R := C.edge)).1
      (reachable_witnessDst_witnessSrc (R := C.edge) C.scc) with h | h
    · exact absurd h hne
    · exact h

/-! ## The conclusion the transport buys -/

/-- The transitive closure of the induced step relates the two witnesses in both directions, which
is a genuine cycle rather than a pair of trivial paths. -/
theorem induced_transGen_cycle (C : FiniteSCCCertificate) :
    Relation.TransGen (inducedStep C)
        (.at (witnessSrc (α := C.Node) C.edge C.scc))
        (.at (witnessDst (α := C.Node) C.edge C.scc))
      ∧ Relation.TransGen (inducedStep C)
        (.at (witnessDst (α := C.Node) C.edge C.scc))
        (.at (witnessSrc (α := C.Node) C.edge C.scc)) := by
  obtain ⟨hne, hfwd, hbwd⟩ := induced_rewrite_round_trip C
  constructor
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 hfwd with h | h
    · exact absurd h.symm hne
    · exact h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 hbwd with h | h
    · exact absurd h hne
    · exact h

/-- **Non-termination.** The reverse of the induced rewrite relation is not well founded, for every
finite SCC certificate. This is the statement the coexistence bundle could not make, because it had
no edge-to-rewrite law. -/
theorem inducedStep_not_wellFounded (C : FiniteSCCCertificate) :
    ¬ WellFounded (fun x y : Packet C.Node => Relation.TransGen (inducedStep C) y x) := by
  intro hwf
  obtain ⟨hfwd, hbwd⟩ := induced_transGen_cycle C
  have hloop :
      Relation.TransGen (inducedStep C)
        (.at (witnessSrc (α := C.Node) C.edge C.scc))
        (.at (witnessSrc (α := C.Node) C.edge C.scc)) := hfwd.trans hbwd
  have key : ∀ x : Packet C.Node,
      Acc (fun u v : Packet C.Node => Relation.TransGen (inducedStep C) v u) x →
        ¬ Relation.TransGen (inducedStep C) x x := by
    intro x hx
    induction hx with
    | intro y _ ih => exact fun hy => ih y hy hy
  exact key _ (hwf.apply _) hloop

/-- The canonical two-node certificate realizes the transport. -/
theorem boolSCCCertificate_induced_cycle :
    ¬ WellFounded
        (fun x y : Packet boolSCCCertificate.Node =>
          Relation.TransGen (inducedStep boolSCCCertificate) y x) :=
  inducedStep_not_wellFounded boolSCCCertificate

/-! ## Where the transport stops -/

/-- Reachability transports along an edge-respecting node interpretation. -/
theorem transGen_step_of_transGen_edge (C : FiniteSCCCertificate)
    (interp : C.Node → OperatorKO7.Trace)
    (hresp : ∀ a b, C.edge a b → OperatorKO7.Step (interp a) (interp b))
    {a b : C.Node} (h : Relation.TransGen C.edge a b) :
    Relation.TransGen OperatorKO7.Step (interp a) (interp b) := by
  induction h with
  | single hab => exact Relation.TransGen.single (hresp _ _ hab)
  | tail _ hbc ih => exact ih.tail (hresp _ _ hbc)

/-- **The boundary, and why it is a boundary.** No edge-respecting interpretation of the nodes into
`Trace` exists, for any certificate. The SCC supplies a cycle, an edge-respecting interpretation
would carry that cycle into `Step`, and `Step` is terminating (`OperatorKO7.MetaMPO.wf_StepRev_mpo`). So the transport
genuinely stops at the packet syntax: it is not that the map was left unwritten, it is that no such
map exists. -/
theorem no_edge_respecting_ko7_interpretation (C : FiniteSCCCertificate) :
    ¬ ∃ interp : C.Node → OperatorKO7.Trace,
        ∀ a b, C.edge a b → OperatorKO7.Step (interp a) (interp b) := by
  rintro ⟨interp, hresp⟩
  obtain ⟨hfwd, hbwd⟩ := scc_transGen_cycle C
  have hloop :
      Relation.TransGen OperatorKO7.Step
        (interp (witnessSrc (α := C.Node) C.edge C.scc))
        (interp (witnessSrc (α := C.Node) C.edge C.scc)) :=
    (transGen_step_of_transGen_edge C interp hresp hfwd).trans
      (transGen_step_of_transGen_edge C interp hresp hbwd)
  have hwf : WellFounded (fun a b : OperatorKO7.Trace =>
      Relation.TransGen OperatorKO7.Step b a) := by
    have hsub : Subrelation (fun a b : OperatorKO7.Trace =>
        Relation.TransGen OperatorKO7.Step b a)
        (Relation.TransGen (fun a b : OperatorKO7.Trace => OperatorKO7.Step b a)) := by
      intro a b hab
      exact hab.swap
    exact Subrelation.wf hsub (OperatorKO7.MetaMPO.wf_StepRev_mpo).transGen
  have key : ∀ x : OperatorKO7.Trace,
      Acc (fun u v : OperatorKO7.Trace => Relation.TransGen OperatorKO7.Step v u) x →
        ¬ Relation.TransGen OperatorKO7.Step x x := by
    intro x hx
    induction hx with
    | intro y _ ih => exact fun hy => ih y hy hy
  exact key _ (hwf.apply _) hloop

end OperatorKO7.ContextSCCTransport
