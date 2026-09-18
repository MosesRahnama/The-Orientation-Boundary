import OperatorKO7.Meta.RepShift_RecursorInstance

/-!
# Foundational representation-shift integration

This module closes two interfaces used by the operational-inexpressibility
manuscript.

First, it turns the concrete KO7 route witnesses from
`RepShift_RecursorInstance` into actual `RepresentationShiftBottleneck`
records for the KO7 termination predicate.  The truth-level hierarchy admits
the polynomial witness at depth one.  The boundary-relative hierarchy admits
the dependency-pair witness at depth two.  Wrong-depth theorems supply
negative instances for both records.

Second, it gives a finite countermodel for stronger readings of
`LayerInterface`.  A constant abstraction from `Nat` to `PUnit` satisfies the
stored unit law and supports a sound property transport.  The same abstraction
is many-to-one, has no left inverse, and fails to preserve a selected
nonconstant property through the canonical all-concretizations predicate.

The countermodel fixes the scope of the existing interface: its unit field and
a supplied property transport carry property-level soundness.  Faithful state
reconstruction requires additional hypotheses.
-/

set_option autoImplicit false

namespace OperatorKO7.RepShift

open OperatorKO7

/-! ## Concrete KO7 bottleneck records -/

/-- A truth-level route witness gated to the actual KO7 termination predicate.
The first component is accepted at depth `k`; the second component prevents
the hierarchy from manufacturing witnesses for unrelated predicates. -/
def ko7TruthWitnessFamily
    (k : Nat) (P : Trace → Prop) (_t : Trace) : Type :=
  { w : ko7WitnessAtDepth k // ko7AcceptsAtDepth k w } ×
    PLift (P = ko7Terminates)

/-- The KO7 truth-level hierarchy over the accepted route witnesses from
`RepShift_RecursorInstance`. -/
def ko7TruthWitnessHierarchy : WitnessHierarchy Trace where
  W := ko7TruthWitnessFamily
  accepts := fun _ => True
  sound := by
    intro _k P t w _hAccepted
    rw [w.2.down]
    exact ko7Terminates_holds t

/-- The truth-level hierarchy has no adequate witness at depth zero. -/
theorem ko7TruthWitnessHierarchy_no_adequate_at_zero :
    ¬ ko7TruthWitnessHierarchy.hasAdequateAtDepth
      0 ko7Terminates Trace.void := by
  rintro ⟨⟨⟨⟨w, hw⟩, _hProperty⟩, _hAccepted⟩⟩
  exact (ko7_no_accepted_at_zero w) hw

/-- The polynomial proof gives an adequate truth-level witness at depth one. -/
theorem ko7TruthWitnessHierarchy_has_adequate_at_one :
    ko7TruthWitnessHierarchy.hasAdequateAtDepth
      1 ko7Terminates Trace.void := by
  rcases ko7_accepted_at_one_poly with ⟨w, hw⟩
  refine
    ⟨⟨⟨⟨w, hw⟩, PLift.up rfl⟩,
      True.intro⟩⟩

/-- KO7 realizes the abstract representation-shift bottleneck at truth depth
one.  The record contains the terminating property, the empty depth-zero
fiber, and the polynomial witness at depth one. -/
theorem ko7_truth_representationShiftBottleneck :
    RepresentationShiftBottleneck
      ko7TruthWitnessHierarchy ko7Terminates Trace.void 1 := by
  refine
    { property_holds := ko7Terminates_holds Trace.void
      no_witness_below := ?_
      witness_at_k := ko7TruthWitnessHierarchy_has_adequate_at_one }
  intro j hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  subst j
  exact ko7TruthWitnessHierarchy_no_adequate_at_zero

/-- Depth two fails truth-level minimality because the accepted depth-one
polynomial witness already exists. -/
theorem ko7_truth_depth_two_not_representationShiftBottleneck :
    ¬ RepresentationShiftBottleneck
      ko7TruthWitnessHierarchy ko7Terminates Trace.void 2 := by
  intro h
  exact h.no_witness_below 1 (by omega)
    ko7TruthWitnessHierarchy_has_adequate_at_one

/-- A boundary-relative route witness gated to the actual KO7 termination
predicate.  Its route component must pass the benchmark
boundary-admissibility predicate. -/
def ko7BoundaryWitnessFamily
    (k : Nat) (P : Trace → Prop) (_t : Trace) : Type :=
  { w : ko7WitnessAtDepth k // ko7BoundaryAdmissibleAtDepth k w } ×
    PLift (P = ko7Terminates)

/-- The KO7 boundary-relative hierarchy over admissible route witnesses. -/
def ko7BoundaryWitnessHierarchy : WitnessHierarchy Trace where
  W := ko7BoundaryWitnessFamily
  accepts := fun _ => True
  sound := by
    intro _k P t w _hAccepted
    rw [w.2.down]
    exact ko7Terminates_holds t

/-- The boundary-relative hierarchy has no adequate witness at depth zero. -/
theorem ko7BoundaryWitnessHierarchy_no_adequate_at_zero :
    ¬ ko7BoundaryWitnessHierarchy.hasAdequateAtDepth
      0 ko7Terminates Trace.void := by
  rintro ⟨⟨⟨⟨_w, hw⟩, _hProperty⟩, _hAccepted⟩⟩
  exact hw

/-- The boundary-relative hierarchy has no adequate witness at depth one. -/
theorem ko7BoundaryWitnessHierarchy_no_adequate_at_one :
    ¬ ko7BoundaryWitnessHierarchy.hasAdequateAtDepth
      1 ko7Terminates Trace.void := by
  rintro ⟨⟨⟨⟨_w, hw⟩, _hProperty⟩, _hAccepted⟩⟩
  exact hw

/-- The dependency-pair proof gives an adequate boundary-relative witness at
depth two. -/
theorem ko7BoundaryWitnessHierarchy_has_adequate_at_two :
    ko7BoundaryWitnessHierarchy.hasAdequateAtDepth
      2 ko7Terminates Trace.void := by
  rcases ko7_boundary_admissible_at_two_dp with ⟨w, hw⟩
  refine
    ⟨⟨⟨⟨w, hw⟩, PLift.up rfl⟩,
      True.intro⟩⟩

/-- KO7 realizes the abstract boundary-relative bottleneck at depth two. -/
theorem ko7_boundary_representationShiftBottleneck :
    RepresentationShiftBottleneck
      ko7BoundaryWitnessHierarchy ko7Terminates Trace.void 2 := by
  refine
    { property_holds := ko7Terminates_holds Trace.void
      no_witness_below := ?_
      witness_at_k := ko7BoundaryWitnessHierarchy_has_adequate_at_two }
  intro j hj
  rcases Nat.lt_succ_iff.mp hj with hjLe
  cases j with
  | zero => exact ko7BoundaryWitnessHierarchy_no_adequate_at_zero
  | succ j =>
      cases j with
      | zero => exact ko7BoundaryWitnessHierarchy_no_adequate_at_one
      | succ j => omega

/-- Depth one fails the boundary-relative bottleneck because its witness fiber
is empty. -/
theorem ko7_boundary_depth_one_not_representationShiftBottleneck :
    ¬ RepresentationShiftBottleneck
      ko7BoundaryWitnessHierarchy ko7Terminates Trace.void 1 := by
  intro h
  exact ko7BoundaryWitnessHierarchy_no_adequate_at_one h.witness_at_k

/-- Depth three fails boundary-relative minimality because the dependency-pair
witness already exists at depth two. -/
theorem ko7_boundary_depth_three_not_representationShiftBottleneck :
    ¬ RepresentationShiftBottleneck
      ko7BoundaryWitnessHierarchy ko7Terminates Trace.void 3 := by
  intro h
  exact h.no_witness_below 2 (by omega)
    ko7BoundaryWitnessHierarchy_has_adequate_at_two

/-! ## A many-to-one interface countermodel -/

/-- A semantic layer whose witnesses are proofs of the requested property. -/
def proofCarryingLayer (S : Type) : SemanticLayer S where
  step := fun _ _ => False
  witnesses := fun P x => PLift (P x)

/-- The corresponding verifier accepts each proof-carrying witness. -/
def proofCarryingVerifier (S : Type) : Verifier (proofCarryingLayer S) where
  accepts := fun _ => True
  sound := by
    intro _P _x w _hAccepted
    exact w.down

/-- A constant abstraction from natural-number states to one abstract state.
Its concretization is the full natural-number carrier. -/
def natToUnitLayerInterface :
    LayerInterface (proofCarryingLayer Nat) (proofCarryingLayer PUnit) where
  alpha := fun _ => PUnit.unit
  gamma := fun _ => Set.univ
  galois_unit := fun x => Set.mem_univ x

/-- The interface satisfies the stored unit law on every natural-number
state. -/
theorem natToUnitLayerInterface_unit (x : Nat) :
    x ∈ natToUnitLayerInterface.gamma (natToUnitLayerInterface.alpha x) :=
  natToUnitLayerInterface.galois_unit x

/-- The abstraction collapses the distinct states zero and one. -/
theorem natToUnitLayerInterface_alpha_not_injective :
    ¬ Function.Injective natToUnitLayerInterface.alpha := by
  intro hInjective
  have h01 : (0 : Nat) = 1 := hInjective rfl
  exact Nat.zero_ne_one h01

/-- The many-to-one abstraction admits no state-valued left inverse. -/
theorem natToUnitLayerInterface_no_leftInverse :
    ¬ ∃ beta : PUnit → Nat,
        Function.LeftInverse beta natToUnitLayerInterface.alpha := by
  rintro ⟨beta, hLeft⟩
  have h0 : beta PUnit.unit = 0 := by
    simpa [natToUnitLayerInterface] using hLeft 0
  have h1 : beta PUnit.unit = 1 := by
    simpa [natToUnitLayerInterface] using hLeft 1
  have h01 : (0 : Nat) = 1 := h0.symm.trans h1
  exact Nat.zero_ne_one h01

/-- The concretization fiber over the sole abstract state contains two
distinct concrete states. -/
theorem natToUnitLayerInterface_gamma_has_distinct_states :
    (0 : Nat) ∈ natToUnitLayerInterface.gamma PUnit.unit ∧
      (1 : Nat) ∈ natToUnitLayerInterface.gamma PUnit.unit ∧
      (0 : Nat) ≠ 1 := by
  exact ⟨Set.mem_univ 0, Set.mem_univ 1, Nat.zero_ne_one⟩

/-- A nonconstant lower-layer property used to test canonical abstraction. -/
def isZeroState (n : Nat) : Prop := n = 0

/-- The canonical all-concretizations property for `isZeroState` fails at the
abstract image of state one.  The unit law alone therefore carries no
arbitrary-property preservation theorem. -/
theorem natToUnitLayerInterface_isZero_not_canonically_preserved :
    ¬ canonicalAbstractedProperty
      natToUnitLayerInterface isZeroState
      (natToUnitLayerInterface.alpha 1) := by
  intro hCanonical
  have hOne : isZeroState 1 :=
    hCanonical 1 (Set.mem_univ 1)
  exact Nat.one_ne_zero hOne

/-- A lower-layer property with a direct arithmetic proof at every state. -/
def belowSuccessor (n : Nat) : Prop := n ≤ n + 1

/-- Its one-state abstract property. -/
def abstractBelowSuccessor (_u : PUnit) : Prop := True

/-- A supplied property transport across the many-to-one interface. -/
def belowSuccessorTransport :
    WitnessTransport
      natToUnitLayerInterface
      (proofCarryingVerifier Nat)
      (proofCarryingVerifier PUnit)
      belowSuccessor
      abstractBelowSuccessor where
  transfer := by
    intro n _w
    exact Nat.le_succ n

/-- An accepted higher-layer witness for the abstract property. -/
def abstractBelowSuccessorAdequateWitness :
    adequateWitnesses
      (proofCarryingVerifier PUnit)
      abstractBelowSuccessor
      PUnit.unit :=
  ⟨PLift.up True.intro, True.intro⟩

/-- The higher layer contains an adequate witness for the abstract property. -/
theorem abstractBelowSuccessor_has_adequate_witness :
    Nonempty
      (adequateWitnesses
        (proofCarryingVerifier PUnit)
        abstractBelowSuccessor
        PUnit.unit) :=
  ⟨abstractBelowSuccessorAdequateWitness⟩

/-- The supplied transport recovers the concrete arithmetic property at a
specific nonzero state. -/
theorem belowSuccessorTransport_recovers_seven : belowSuccessor 7 := by
  exact belowSuccessorTransport.transfer 7
    abstractBelowSuccessorAdequateWitness

/-- A valid property transport and a noninjective abstraction coexist in the
same concrete interface.  Property-level soundness therefore carries no
faithful-state consequence. -/
theorem property_transport_coexists_with_noninjective_abstraction :
    Nonempty
      (WitnessTransport
        natToUnitLayerInterface
        (proofCarryingVerifier Nat)
        (proofCarryingVerifier PUnit)
        belowSuccessor
        abstractBelowSuccessor) ∧
      ¬ Function.Injective natToUnitLayerInterface.alpha := by
  exact
    ⟨⟨belowSuccessorTransport⟩,
      natToUnitLayerInterface_alpha_not_injective⟩

end OperatorKO7.RepShift
