import OperatorKO7.Meta.MutualDuplication_FiniteSchema_GraphSearch

/-!
# Executable Finite H3 Graph Search

This module upgrades the H3 finite-cycle graph layer from explicit successor-edge
certificate data to an explicit finite encoded search space with executable lookup
and cycle search.

The scope is intentionally narrow. The search runs only over the explicit finite
encoded edge space supplied in the input object. Soundness transports any successful
search result to the existing theorem-visible graph-search certificate. Completeness
is likewise scoped only to that explicit encoded space.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace FiniteCycleGraphSearch

/-- Explicit finite encoded search space for H3 cycle edges. -/
structure EncodedSearchSpace (k : Nat) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : Fin (k + 1) → T → T → T → T
  Step : T → T → Prop
  encodedEdges : Finset (Fin (k + 1) × Fin (k + 1))
  step_succ_of_mem :
    ∀ {i j : Fin (k + 1)}, (i, j) ∈ encodedEdges → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace EncodedSearchSpace

/-- Relation view of the finite encoded edge space. -/
abbrev Edge {k : Nat} (S : EncodedSearchSpace k) (i j : Fin (k + 1)) : Prop :=
  (i, j) ∈ S.encodedEdges

/-- The required finite-cycle successor edge at node `i`. -/
def requiredSuccessorPair {k : Nat} (_S : EncodedSearchSpace k) (i : Fin (k + 1)) :
    Fin (k + 1) × Fin (k + 1) :=
  (i, FiniteCycleBuilder.advance i)

/-- Executable lookup for a concrete encoded edge. -/
def edgeLookup? {k : Nat} (S : EncodedSearchSpace k)
    (i j : Fin (k + 1)) : Bool :=
  decide (S.Edge i j)

/-- Executable lookup for the required successor edge at index `i`. -/
def successorEdge? {k : Nat} (S : EncodedSearchSpace k)
    (i : Fin (k + 1)) : Bool :=
  S.edgeLookup? i (FiniteCycleBuilder.advance i)

/-- A successful finite search has found every required successor edge in the encoded
search space. -/
structure CycleCandidate {k : Nat} (S : EncodedSearchSpace k) : Type where
  hasSuccessorEdge : ∀ i : Fin (k + 1), S.Edge i (FiniteCycleBuilder.advance i)

/-- A theorem-visible failure boundary for the executable search. -/
structure MissingSuccessorEdgeStatus {k : Nat} (S : EncodedSearchSpace k) : Type where
  index : Fin (k + 1)
  missing : ¬ S.Edge index (FiniteCycleBuilder.advance index)

/-- Assemble a cycle candidate exactly when every required successor edge is present in the
explicit finite encoded search space. -/
def assembleCycleCandidate? {k : Nat} (S : EncodedSearchSpace k) :
    Option (CycleCandidate S) :=
  if h : ∀ i : Fin (k + 1), S.Edge i (FiniteCycleBuilder.advance i) then
    some ⟨h⟩
  else
    none

/-- Top-level executable H3 cycle search over the explicit finite encoded edge space. -/
def searchCycle? {k : Nat} (S : EncodedSearchSpace k) : Option (CycleCandidate S) :=
  S.assembleCycleCandidate?

/-- Any successful executable search transports to the existing theorem-visible graph-search
certificate surface. -/
def CycleCandidate.toGraphSearchCertificate {k : Nat} {S : EncodedSearchSpace k}
    (W : CycleCandidate S) : GraphSearchCertificate k where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := S.recur
  Edge := S.Edge
  Step := S.Step
  local_graph_edge := W.hasSuccessorEdge
  step_succ_of_edge := by
    intro i j hij b s n
    exact S.step_succ_of_mem hij b s n

/-- Search soundness: every returned candidate yields a theorem-visible graph-search
certificate. -/
def cycleCandidate_sound {k : Nat} {S : EncodedSearchSpace k}
    (W : CycleCandidate S) :
    GraphSearchCertificate k :=
  W.toGraphSearchCertificate

/-- Finite completeness for the explicit encoded search space: if every required successor edge
is present, the executable search returns a witness. -/
theorem exists_searchCycle?_eq_some {k : Nat} {S : EncodedSearchSpace k}
    (hall : ∀ i : Fin (k + 1), S.Edge i (FiniteCycleBuilder.advance i)) :
    ∃ W : CycleCandidate S, S.searchCycle? = some W := by
  refine ⟨⟨hall⟩, ?_⟩
  simp [searchCycle?, assembleCycleCandidate?, hall]

/-- The executable search fails exactly when the explicit finite encoded search space is missing
at least one required successor edge. -/
theorem searchCycle?_eq_none_iff_missingSuccessorEdgeStatus {k : Nat}
    (S : EncodedSearchSpace k) :
    S.searchCycle? = none ↔ Nonempty (MissingSuccessorEdgeStatus S) := by
  unfold searchCycle? assembleCycleCandidate?
  by_cases h : ∀ i : Fin (k + 1), S.Edge i (FiniteCycleBuilder.advance i)
  · constructor
    · intro hnone
      simp [h] at hnone
    · intro hmiss
      rcases hmiss with ⟨m⟩
      exact False.elim (m.missing (h m.index))
  · have hmiss : Nonempty (MissingSuccessorEdgeStatus S) := by
      push_neg at h
      rcases h with ⟨i, hi⟩
      exact ⟨⟨i, hi⟩⟩
    constructor
    · intro _
      exact hmiss
    · intro _
      simp [h]

end EncodedSearchSpace

end FiniteCycleGraphSearch

namespace Constructors

/-- Two-rule constructor data as an explicit finite encoded H3 search space. -/
def TwoRuleData.toEncodedSearchSpace
    (D : TwoRuleData) :
    FiniteCycleGraphSearch.EncodedSearchSpace 1 where
  T := TwoRuleData.T D
  base := TwoRuleData.base D
  succ := TwoRuleData.succ D
  wrap := TwoRuleData.wrap D
  recur := fun i =>
    match i.1 with
    | 0 => TwoRuleData.recurA D
    | _ => TwoRuleData.recurB D
  Step := TwoRuleData.Step D
  encodedEdges := Finset.univ.filter fun p => p.2 = FiniteCycleBuilder.advance p.1
  step_succ_of_mem := by
    intro i j hij b s n
    have hj : j = FiniteCycleBuilder.advance i := by
      simpa [Finset.mem_filter] using hij
    subst j
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using
        TwoRuleData.stepA_succ D b s n
    · simpa [FiniteCycleBuilder.advance] using
        TwoRuleData.stepB_succ D b s n

/-- Three-rule constructor data as an explicit finite encoded H3 search space. -/
def ThreeRuleData.toEncodedSearchSpace
    (D : ThreeRuleData) :
    FiniteCycleGraphSearch.EncodedSearchSpace 2 where
  T := ThreeRuleData.T D
  base := ThreeRuleData.base D
  succ := ThreeRuleData.succ D
  wrap := ThreeRuleData.wrap D
  recur := fun i =>
    match i.1 with
    | 0 => ThreeRuleData.recur0 D
    | 1 => ThreeRuleData.recur1 D
    | _ => ThreeRuleData.recur2 D
  Step := ThreeRuleData.Step D
  encodedEdges := Finset.univ.filter fun p => p.2 = FiniteCycleBuilder.advance p.1
  step_succ_of_mem := by
    intro i j hij b s n
    have hj : j = FiniteCycleBuilder.advance i := by
      simpa [Finset.mem_filter] using hij
    subst j
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using
        ThreeRuleData.step0_succ D b s n
    · simpa [FiniteCycleBuilder.advance] using
        ThreeRuleData.step1_succ D b s n
    · simpa [FiniteCycleBuilder.advance] using
        ThreeRuleData.step2_succ D b s n

end Constructors

  namespace FiniteCycleGraphSearch

namespace KCycleSystem

/-- Concrete encoded H3 search space for the two-rule witness system. -/
def twoRuleWitnessEncodedSearchSpace : EncodedSearchSpace 1 :=
  OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toEncodedSearchSpace
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData

/-- Concrete encoded H3 search space for the three-rule witness system. -/
def threeRuleWitnessEncodedSearchSpace : EncodedSearchSpace 2 :=
  OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toEncodedSearchSpace
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessData

/-- The executable H3 search succeeds on the concrete two-rule witness space. -/
theorem twoRuleWitness_searchCycle?_succeeds :
    ∃ W : EncodedSearchSpace.CycleCandidate twoRuleWitnessEncodedSearchSpace,
      EncodedSearchSpace.searchCycle? twoRuleWitnessEncodedSearchSpace = some W := by
  exact EncodedSearchSpace.exists_searchCycle?_eq_some (S := twoRuleWitnessEncodedSearchSpace) <| by
    intro i
    simp [twoRuleWitnessEncodedSearchSpace,
      OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toEncodedSearchSpace,
      EncodedSearchSpace.Edge, Finset.mem_filter]

/-- The executable H3 search succeeds on the concrete three-rule witness space. -/
theorem threeRuleWitness_searchCycle?_succeeds :
    ∃ W : EncodedSearchSpace.CycleCandidate threeRuleWitnessEncodedSearchSpace,
      EncodedSearchSpace.searchCycle? threeRuleWitnessEncodedSearchSpace = some W := by
  exact EncodedSearchSpace.exists_searchCycle?_eq_some (S := threeRuleWitnessEncodedSearchSpace) <| by
    intro i
    simp [threeRuleWitnessEncodedSearchSpace,
      OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toEncodedSearchSpace,
      EncodedSearchSpace.Edge, Finset.mem_filter]

end KCycleSystem

end FiniteCycleGraphSearch

end OperatorKO7.MutualDuplicationFiniteSchema
