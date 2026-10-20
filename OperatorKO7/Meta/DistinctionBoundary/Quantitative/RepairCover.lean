import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Minimum repair cover

A finite set `bad` records the defects under consideration. An intervention `j` covers the subset
`closes j`, and a repair family is a finite set cover. One intervention may cover several defects.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v

variable {B : Type u} {J : Type v}

/-- Every listed defect belongs to the union covered by the chosen interventions. -/
def IsRepairCover [DecidableEq B] [DecidableEq J]
    (bad : Finset B) (closes : J -> Finset B) (chosen : Finset J) : Prop :=
  bad ⊆ chosen.biUnion closes

/-- Every finite intervention subset that is a repair cover. -/
noncomputable def repairCandidates [Fintype J] [DecidableEq B] [DecidableEq J]
    (bad : Finset B) (closes : J -> Finset B) : Finset (Finset J) := by
  classical
  exact (Finset.univ : Finset J).powerset.filter (IsRepairCover bad closes)

theorem mem_repairCandidates_iff [Fintype J] [DecidableEq B] [DecidableEq J]
    (bad : Finset B) (closes : J -> Finset B) (chosen : Finset J) :
    chosen ∈ repairCandidates bad closes <-> IsRepairCover bad closes chosen := by
  simp [repairCandidates]

theorem repairCandidates_nonempty [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ) :
    (repairCandidates bad closes).Nonempty := by
  refine ⟨Finset.univ, ?_⟩
  exact (mem_repairCandidates_iff bad closes Finset.univ).2 hcoverable

/-- Minimum cardinality among the repair covers, under a premise that the full intervention family
covers `bad`. -/
noncomputable def repairCoverNumber [Fintype J] [DecidableEq B] [DecidableEq J]
    (bad : Finset B) (closes : J -> Finset B)
    (hcoverable : IsRepairCover bad closes Finset.univ) : Nat :=
  (repairCandidates bad closes).inf'
    (repairCandidates_nonempty hcoverable) Finset.card

/-- Bound the minimum by the cardinality of any supplied repair cover. -/
theorem repairCoverNumber_le_card [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    {chosen : Finset J} (hchosen : IsRepairCover bad closes chosen) :
    repairCoverNumber bad closes hcoverable <= chosen.card := by
  apply Finset.inf'_le
  exact (mem_repairCandidates_iff bad closes chosen).2 hchosen

/-- If each selected intervention covers at most `M` defects, a family of `k` interventions covers
at most `k * M` defects. -/
theorem repairCover_counting_bound [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B} {chosen : Finset J} {M : Nat}
    (hchosen : IsRepairCover bad closes chosen)
    (hmax : forall j, (closes j).card <= M) :
    bad.card <= chosen.card * M := by
  exact (Finset.card_le_card hchosen).trans
    (Finset.card_biUnion_le_card_mul chosen closes M (fun j _ => hmax j))

/-- If each intervention covers at most positive `M` defects, the minimum cover cardinality is at
least `ceil(|bad| / M)`. -/
theorem repairCoverNumber_lower_bound [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    {M : Nat} (hM : 0 < M)
    (hmax : forall j, (closes j).card <= M) :
    bad.card ⌈/⌉ M <= repairCoverNumber bad closes hcoverable := by
  unfold repairCoverNumber
  apply Finset.le_inf'
  intro chosen hcandidate
  apply (ceilDiv_le_iff_le_mul hM).2
  have hcount := repairCover_counting_bound
    ((mem_repairCandidates_iff bad closes chosen).1 hcandidate) hmax
  simpa [Nat.mul_comm] using hcount

/-- Supplied singleton interventions give an upper bound of one intervention per defect. -/
theorem repairCoverNumber_le_bad_card_of_singletons
    [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    (singletonRepair : B -> J)
    (hsingleton : forall b, b ∈ bad -> closes (singletonRepair b) = {b}) :
    repairCoverNumber bad closes hcoverable <= bad.card := by
  let chosen : Finset J := bad.image singletonRepair
  have hchosen : IsRepairCover bad closes chosen := by
    intro b hb
    rw [Finset.mem_biUnion]
    refine ⟨singletonRepair b, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨b, hb, rfl⟩
    · rw [hsingleton b hb]
      simp
  exact (repairCoverNumber_le_card hcoverable hchosen).trans Finset.card_image_le

/-- With singleton repairs and the premise that each intervention covers at most one defect, the
minimum cover cardinality equals `bad.card`. -/
theorem repairCoverNumber_eq_bad_card_of_independent_singletons
    [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    (hmaxOne : forall j, (closes j).card <= 1)
    (singletonRepair : B -> J)
    (hsingleton : forall b, b ∈ bad -> closes (singletonRepair b) = {b}) :
    repairCoverNumber bad closes hcoverable = bad.card := by
  apply le_antisymm
  · exact repairCoverNumber_le_bad_card_of_singletons
      hcoverable singletonRepair hsingleton
  · simpa using repairCoverNumber_lower_bound hcoverable (M := 1) (by omega) hmaxOne

/-- Natural-number cost of a chosen repair family. -/
def repairCoverCost [DecidableEq J] (cost : J -> Nat) (chosen : Finset J) : Nat :=
  ∑ j ∈ chosen, cost j

/-- Minimum weighted repair cost over the same finite cover family. -/
noncomputable def minimumRepairCoverCost [Fintype J] [DecidableEq B] [DecidableEq J]
    (bad : Finset B) (closes : J -> Finset B) (cost : J -> Nat)
    (hcoverable : IsRepairCover bad closes Finset.univ) : Nat :=
  (repairCandidates bad closes).inf'
    (repairCandidates_nonempty hcoverable) (repairCoverCost cost)

theorem minimumRepairCoverCost_le [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B} {cost : J -> Nat}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    {chosen : Finset J} (hchosen : IsRepairCover bad closes chosen) :
    minimumRepairCoverCost bad closes cost hcoverable <= repairCoverCost cost chosen := by
  apply Finset.inf'_le
  exact (mem_repairCandidates_iff bad closes chosen).2 hchosen

/-- Unit lower bounds on intervention costs make the weighted optimum at least the unweighted cover
cardinality. -/
theorem repairCoverNumber_le_minimumRepairCoverCost
    [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B} {cost : J -> Nat}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    (hcost : forall j, 1 <= cost j) :
    repairCoverNumber bad closes hcoverable <=
      minimumRepairCoverCost bad closes cost hcoverable := by
  unfold minimumRepairCoverCost
  apply Finset.le_inf'
  intro chosen hcandidate
  have hcover := (mem_repairCandidates_iff bad closes chosen).1 hcandidate
  calc
    repairCoverNumber bad closes hcoverable <= chosen.card :=
      repairCoverNumber_le_card hcoverable hcover
    _ = ∑ j ∈ chosen, 1 := by simp
    _ <= ∑ j ∈ chosen, cost j := by
      exact Finset.sum_le_sum (fun j _ => hcost j)

/-! ## Shared-guard fixture -/

/-- Two distinct bad pairs. -/
def sharedBadPairs : Finset (Fin 2) := Finset.univ

/-- The sole intervention closes both bad pairs. -/
def sharedGuardCoverage (_ : Fin 1) : Finset (Fin 2) := Finset.univ

theorem sharedGuard_coverable :
    IsRepairCover sharedBadPairs sharedGuardCoverage Finset.univ := by
  intro b hb
  simp [sharedGuardCoverage]

/-- The single intervention covers both defects, giving cover number one. -/
theorem sharedGuard_repairCoverNumber_eq_one :
    repairCoverNumber sharedBadPairs sharedGuardCoverage sharedGuard_coverable = 1 := by
  apply le_antisymm
  · have hchosen : IsRepairCover sharedBadPairs sharedGuardCoverage
        (Finset.univ : Finset (Fin 1)) := sharedGuard_coverable
    have hle := repairCoverNumber_le_card sharedGuard_coverable hchosen
    simpa using hle
  · have hbound := repairCoverNumber_lower_bound sharedGuard_coverable
      (M := 2) (by omega) (fun j => by simp [sharedGuardCoverage])
    norm_num [sharedBadPairs] at hbound
    exact hbound

/-- In the shared-guard fixture, the cover number differs from the number of defects. -/
theorem sharedGuard_refutes_naive_defect_equality :
    repairCoverNumber sharedBadPairs sharedGuardCoverage sharedGuard_coverable ≠
      sharedBadPairs.card := by
  rw [sharedGuard_repairCoverNumber_eq_one]
  norm_num [sharedBadPairs]

/-- Ten defects with per-intervention coverage at most three require at least four interventions. -/
theorem ten_bad_max_three_requires_four
    [Fintype J] [DecidableEq B] [DecidableEq J]
    {bad : Finset B} {closes : J -> Finset B}
    (hcoverable : IsRepairCover bad closes Finset.univ)
    (hbad : bad.card = 10)
    (hmax : forall j, (closes j).card <= 3) :
    4 <= repairCoverNumber bad closes hcoverable := by
  have hbound := repairCoverNumber_lower_bound hcoverable
    (M := 3) (by omega) hmax
  rw [hbad] at hbound
  norm_num at hbound
  omega

#print axioms repairCoverNumber_lower_bound
#print axioms repairCoverNumber_le_bad_card_of_singletons
#print axioms repairCoverNumber_eq_bad_card_of_independent_singletons
#print axioms repairCoverNumber_le_minimumRepairCoverCost
#print axioms sharedGuard_repairCoverNumber_eq_one
#print axioms sharedGuard_refutes_naive_defect_equality
#print axioms ten_bad_max_three_requires_four

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
