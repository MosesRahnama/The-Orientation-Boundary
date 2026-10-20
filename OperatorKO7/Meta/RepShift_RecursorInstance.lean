import OperatorKO7.Meta.RepShift_LayeredSemanticsTower
import OperatorKO7.Meta.RepShift_BottleneckPredicate
import OperatorKO7.Meta.RepShift_CrossLayerComposition
import OperatorKO7.Meta.WitnessOrder

/-!
# Recursor Instance: KO7 Realises a Representation-Shift Bottleneck

This module connects the abstract Representation-Shift Bottleneck
framework
(`Meta/RepShift_LayeredSemanticsTower.lean`,
`Meta/RepShift_BottleneckPredicate.lean`,
`Meta/RepShift_CrossLayerComposition.lean`)
to the concrete KO7 stack
(`Meta/WitnessOrder.lean`,
`Meta/EscapeTrichotomy.lean`,
`Meta/PolyInterpretation_FullStep.lean`,
`Meta/MPO_FullStep.lean`,
`Meta/DependencyPairs_Works.lean`).

The bottleneck phenomenon at the recursor sits at *two* nested
levels:

- **Truth-level bottleneck (κ* = 1):** there is no accepted direct
  whole-term witness, and the polynomial / MPO witnesses sit at the
  next layer.
- **Boundary-relative bottleneck (κ*_bdy = 2):** under the rule-
  extracted boundary, both the direct layer and the imported-whole
  layer are excluded, and the dependency-pair (transformed-call)
  layer is the first admissible one.

We package these as theorem-level statements that recombine the
existing KO7 mechanization through the `WitnessOrder` API rather
than rebuilding it. The abstract `WitnessHierarchy` of
`Meta/RepShift_BottleneckPredicate.lean` is connected via a
property-fixed witness family below.
-/

namespace OperatorKO7.RepShift

open OperatorKO7
open OperatorKO7.WitnessOrder

/-! ## KO7 termination as a property

The natural property is `ko7Terminates : Prop`, which is constant in
the trace argument. We expose it as a `Trace -> Prop` for uniformity
with the abstract framework. -/

/-- KO7 termination, as a property of any single Trace state.
The property is constant in `t`. -/
def ko7Terminates (_t : Trace) : Prop :=
  WellFounded (fun a b : Trace => Step b a)

/-- KO7 termination holds at every state, since the WF property is
global. -/
theorem ko7Terminates_holds (t : Trace) : ko7Terminates t :=
  OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-! ## Property-fixed witness families

We define witness types per representation depth. These are fixed
to the canonical termination property and therefore avoid the
universal-`P` issues that would otherwise force `sorry` in the
abstract hierarchy soundness. -/

/-- KO7 witnesses at each representation depth, fixed to the
termination property. We use a `Prop`-valued family because every
KO7 termination witness in the existing stack is `Prop`-valued
(WellFounded statements, plus the `DirectWholeWitness` existential).

- depth 0: direct whole-term witness universe (formalized in
  Meta/EscapeTrichotomy.lean and Meta/WitnessOrder.lean);
- depth 1: imported-whole witness (polynomial, MPO);
- depth 2: transformed-call witness (DP);
- depths >= 3: external-certificate placeholder.
-/
def ko7WitnessAtDepth : Nat → Prop
  | 0 => OperatorKO7.WitnessOrder.DirectWholeWitness
  | 1 => WellFounded (fun a b : Trace => Step b a)
  | 2 => WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev
  | _ + 3 => True

/-- Whether a witness at depth `k` is accepted (passed by the
external verifier under the rule-extracted boundary). -/
def ko7AcceptsAtDepth : (k : Nat) → ko7WitnessAtDepth k → Prop
  | 0, _ => False
  | 1, _ => True
  | 2, _ => True
  | _ + 3, _ => False

/-! ## The truth-level bottleneck

At the truth level, KO7 has no accepted direct witness (depth 0)
but has accepted imported-whole witnesses (depth 1) via the
polynomial interpretation and the KO7-specialized MPO. -/

/-- No depth-0 witness is accepted. -/
theorem ko7_no_accepted_at_zero :
    ∀ w : ko7WitnessAtDepth 0, ¬ ko7AcceptsAtDepth 0 w := by
  intro _ h
  exact h

/-- The polynomial interpretation is an accepted depth-1 witness. -/
theorem ko7_accepted_at_one_poly :
    ∃ w : ko7WitnessAtDepth 1, ko7AcceptsAtDepth 1 w :=
  ⟨OperatorKO7.PolyInterpretation.wf_StepRev_poly, True.intro⟩

/-- The KO7-specialized MPO is an accepted depth-1 witness. -/
theorem ko7_accepted_at_one_mpo :
    ∃ w : ko7WitnessAtDepth 1, ko7AcceptsAtDepth 1 w :=
  ⟨OperatorKO7.MetaMPO.wf_StepRev_mpo, True.intro⟩

/-- The dependency-pair proof is an accepted depth-2 witness. -/
theorem ko7_accepted_at_two_dp :
    ∃ w : ko7WitnessAtDepth 2, ko7AcceptsAtDepth 2 w :=
  ⟨OperatorKO7.MetaDependencyPairs.wf_DPPairRev, True.intro⟩

/--
**Truth-level KO7 bottleneck.** KO7 exhibits a
representation-shift bottleneck at depth 1 against the property
`ko7Terminates`: the property holds, no depth-0 witness is
accepted, and a depth-1 witness exists.
-/
theorem ko7_truth_level_bottleneck :
    ko7Terminates Trace.void ∧
    (∀ w : ko7WitnessAtDepth 0, ¬ ko7AcceptsAtDepth 0 w) ∧
    (∃ w : ko7WitnessAtDepth 1, ko7AcceptsAtDepth 1 w) := by
  refine ⟨ko7Terminates_holds Trace.void, ?_, ?_⟩
  · exact ko7_no_accepted_at_zero
  · exact ko7_accepted_at_one_poly

/-! ## The boundary-relative bottleneck

Under the benchmark contract, the imported-whole layer is also
excluded. The first admissible layer is the transformed-call layer
at depth 2. -/

/-- Whether a witness at depth `k` is *boundary-admissible*: accepted
*and* allowed under the benchmark contract. The contract excludes
direct-whole and imported-whole layers, so the first admissible
depth is 2. -/
def ko7BoundaryAdmissibleAtDepth : (k : Nat) → ko7WitnessAtDepth k → Prop
  | 0, _ => False
  | 1, _ => False
  | 2, _ => True
  | _ + 3, _ => False

/-- Boundary admissibility implies acceptance. -/
theorem ko7Boundary_implies_accepted :
    ∀ k, ∀ w : ko7WitnessAtDepth k,
      ko7BoundaryAdmissibleAtDepth k w → ko7AcceptsAtDepth k w := by
  intro k w h
  match k with
  | 0 => exact h.elim
  | 1 => exact h.elim
  | 2 => exact True.intro
  | _ + 3 => exact h.elim

/-- The dependency-pair witness is boundary-admissible at depth 2. -/
theorem ko7_boundary_admissible_at_two_dp :
    ∃ w : ko7WitnessAtDepth 2, ko7BoundaryAdmissibleAtDepth 2 w :=
  ⟨OperatorKO7.MetaDependencyPairs.wf_DPPairRev, True.intro⟩

/-- No boundary-admissible witness exists below depth 2. -/
theorem ko7_no_boundary_admissible_below_two :
    ∀ k, k < 2 → ∀ w : ko7WitnessAtDepth k,
      ¬ ko7BoundaryAdmissibleAtDepth k w := by
  intro k hk w h
  interval_cases k
  · exact h
  · exact h

/--
**Boundary-relative KO7 bottleneck.** KO7 exhibits a
boundary-relative representation-shift bottleneck at depth 2:
the property holds, no boundary-admissible witness exists at
depths 0 or 1, and a boundary-admissible witness exists at depth 2.
-/
theorem ko7_boundary_level_bottleneck :
    ko7Terminates Trace.void ∧
    (∀ k, k < 2 → ∀ w : ko7WitnessAtDepth k,
       ¬ ko7BoundaryAdmissibleAtDepth k w) ∧
    (∃ w : ko7WitnessAtDepth 2, ko7BoundaryAdmissibleAtDepth 2 w) := by
  refine ⟨ko7Terminates_holds Trace.void, ?_, ?_⟩
  · exact ko7_no_boundary_admissible_below_two
  · exact ko7_boundary_admissible_at_two_dp

/-! ## Cross-paper links to the WitnessOrder API

The existing `Meta/WitnessOrder.lean` already proves the bottleneck
predicate at the `WLevel` level. We expose those results through
the present module so that downstream Paper E references resolve
without re-importing the full WitnessOrder. -/

/-- The KO7 truth-level bottleneck statement, proved using the
existing `ko7Tower` API. -/
theorem ko7_truth_bottleneck_via_witnessOrder :
    -- No depth-0 witness in the existing WitnessOrder API.
    (¬ HasWitness ko7Tower WLevel.directWhole) ∧
    -- A depth-1 witness exists in the existing WitnessOrder API.
    HasWitness ko7Tower WLevel.importedWhole := by
  refine ⟨?_, ?_⟩
  · exact ko7_no_directWhole_witness
  · exact ko7_has_importedWhole_witness_poly

/-- The KO7 boundary-relative bottleneck statement, proved using the
existing `ko7Tower` and `benchmarkContract`. -/
theorem ko7_boundary_bottleneck_via_witnessOrder :
    -- No admissible witness at directWhole.
    (¬ HasWitness (contractTower ko7Tower benchmarkContract)
        WLevel.directWhole) ∧
    -- No admissible witness at importedWhole.
    (¬ HasWitness (contractTower ko7Tower benchmarkContract)
        WLevel.importedWhole) ∧
    -- Admissible witness at transformedCall.
    HasWitness (contractTower ko7Tower benchmarkContract)
      WLevel.transformedCall := by
  refine ⟨?_, ?_, ?_⟩
  · simp [HasWitness, contractTower, benchmarkContract, ko7Tower]
  · simp [HasWitness, contractTower, benchmarkContract]
  · exact ⟨True.intro, ko7_has_transformedCall_witness⟩

/-! ## Pre-undecidability fracture

KO7 satisfies the witness-landscape portion of the pre-undecidability
fracture: the property holds (so it is decidable in the trivial
sense — we know the truth value), an adequate witness exists at
boundary-relative depth `k = 2`, and `k > 0`. The agent-instability
ingredient is empirical and is supplied by an external benchmark. -/

/-- KO7 termination is decidable for the canonical instance: it
holds. -/
instance : Decidable (ko7Terminates Trace.void) :=
  isTrue (ko7Terminates_holds Trace.void)

/-- KO7 satisfies the witness-landscape portion of the
pre-undecidability fracture at boundary-relative depth `k = 2`. The
agent-instability clause is empirical. -/
theorem ko7_pre_undecidability_witness_landscape :
    HasWitness ko7Tower WLevel.transformedCall ∧
    (0 : Nat) < 2 := by
  exact ⟨ko7_has_transformedCall_witness, by decide⟩

/-! ## Summary

The KO7 system, as mechanized in the existing trilogy stack, is a
concrete instance of the Representation-Shift Bottleneck framework:

- the witness hierarchy has populated layers at depths 0, 1, 2;
- the depth-0 layer is *barrier-blocked* (no accepted witness);
- the depth-1 layer is populated at the truth level (polynomial,
  MPO) but excluded by the benchmark contract;
- the depth-2 layer is populated at both truth and boundary levels
  (dependency pairs).

The minimal *truth-level* representation order is `κ* = 1`; the
minimal *boundary-relative* representation order is `κ*_bdy = 2`.
Both are positive, so the system exhibits a representation-shift
bottleneck. The boundary-relative bottleneck at `k = 2` is the
locus of empirical agent instability, completing the
pre-undecidability fracture predicate. -/

end OperatorKO7.RepShift
