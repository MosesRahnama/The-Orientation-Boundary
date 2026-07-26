import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Quantitative distinction-witness rank

## Formal Scope

Witness rank is defined generically from explicit adequacy existence. The base and licensed profiles are declared fixtures, and all nonexistence statements remain restricted to their stated witness universes.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- An upward-closed profile of grades carrying an adequate distinction
witness. -/
structure GradedAdequacy where
  adequate : Nat -> Prop
  upward : forall {i j}, i <= j -> adequate i -> adequate j
  inhabited : exists i, adequate i

/-- The least grade carrying an adequate witness. -/
noncomputable def witnessRank (G : GradedAdequacy) : Nat :=
  by
    classical
    exact Nat.find G.inhabited

theorem witnessRank_adequate (G : GradedAdequacy) : G.adequate (witnessRank G) :=
  by
    classical
    simpa [witnessRank] using Nat.find_spec G.inhabited

theorem witnessRank_le_of_adequate (G : GradedAdequacy) {j : Nat}
    (hj : G.adequate j) : witnessRank G <= j :=
  by
    classical
    simpa [witnessRank] using Nat.find_min' G.inhabited hj

theorem not_adequate_below_witnessRank (G : GradedAdequacy) {j : Nat}
    (hj : j < witnessRank G) : Not (G.adequate j) :=
  by
    classical
    apply Nat.find_min G.inhabited
    simpa [witnessRank] using hj

/-- Adequacy persists at every grade above the minimum. -/
theorem adequate_at_and_above_witnessRank (G : GradedAdequacy) {j : Nat}
    (hj : witnessRank G <= j) : G.adequate j :=
  G.upward hj (witnessRank_adequate G)

/-- A witness-preserving translation from `G` to `H` cannot increase the least
adequate grade. -/
theorem witnessRank_antitone_of_gradewise_preservation (G H : GradedAdequacy)
    (preserves : forall i, G.adequate i -> H.adequate i) :
    witnessRank H <= witnessRank G :=
  witnessRank_le_of_adequate H (preserves _ (witnessRank_adequate G))

/-- A profile without any adequate grade is a scope wall. This definition is
kept outside `GradedAdequacy`, whose purpose is to carry profiles with a rank. -/
def IsWitnessScopeWall (adequate : Nat -> Prop) : Prop :=
  forall i, Not (adequate i)

theorem witnessScopeWall_iff_no_grade (adequate : Nat -> Prop) :
    IsWitnessScopeWall adequate <-> Not (exists i, adequate i) := by
  constructor
  · intro h ⟨i, hi⟩
    exact h i hi
  · intro h i hi
    exact h ⟨i, hi⟩

/-! ## Concrete rank-zero, rank-one, and wall profiles -/

def baseAdequacy : GradedAdequacy where
  adequate := fun _ => True
  upward := by intros; trivial
  inhabited := ⟨0, trivial⟩

def licensedAdequacy : GradedAdequacy where
  adequate := fun i => 1 <= i
  upward := by
    intro i j hij hi
    exact hi.trans hij
  inhabited := ⟨1, le_rfl⟩

theorem baseAdequacy_rank_zero : witnessRank baseAdequacy = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact witnessRank_le_of_adequate baseAdequacy trivial

theorem licensedAdequacy_rank_one : witnessRank licensedAdequacy = 1 := by
  apply le_antisymm
  · exact witnessRank_le_of_adequate licensedAdequacy le_rfl
  · have hnot : Not (licensedAdequacy.adequate 0) := by simp [licensedAdequacy]
    by_contra h
    have hz : witnessRank licensedAdequacy = 0 := Nat.eq_zero_of_not_pos h
    exact hnot (hz ▸ witnessRank_adequate licensedAdequacy)

theorem impossibleAdequacy_is_scopeWall :
    IsWitnessScopeWall (fun _ : Nat => False) := by
  intro i h
  exact h

theorem rank_one_is_not_rank_zero : witnessRank licensedAdequacy != 0 := by
  rw [licensedAdequacy_rank_one]
  norm_num

#print axioms witnessRank_adequate
#print axioms witnessRank_le_of_adequate
#print axioms adequate_at_and_above_witnessRank
#print axioms witnessRank_antitone_of_gradewise_preservation
#print axioms licensedAdequacy_rank_one
#print axioms impossibleAdequacy_is_scopeWall

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
