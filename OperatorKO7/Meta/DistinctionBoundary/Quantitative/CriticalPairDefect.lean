import Mathlib
import OperatorKO7.Meta.Rewriting.ConfluenceDecision

/-!
This module counts emitted critical pairs whose supplied normalizer outputs differ. The
confluence equivalence assumes a well-founded reverse step relation and irreducibility of every
normalizer output. Finite fixtures exercise the list-level definitions.







-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Pairs from a finite list whose chosen normal forms disagree. -/
def normalizedPairDefects {alpha : Type u} [DecidableEq alpha]
    (nf : alpha -> alpha) (pairs : List (alpha × alpha)) : List (alpha × alpha) :=
  pairs.filter (fun q => decide (nf q.1 != nf q.2))

/-- Definition with formal content given by the displayed type and body. -/
def normalizedPairDefectCount {alpha : Type u} [DecidableEq alpha]
    (nf : alpha -> alpha) (pairs : List (alpha × alpha)) : Nat :=
  (normalizedPairDefects nf pairs).length

/-- Definition with formal content given by the displayed type and body.
-/
def normalizedPairDefectRate {alpha : Type u} [DecidableEq alpha]
    (nf : alpha -> alpha) (pairs : List (alpha × alpha)) : ℚ :=
  if pairs.isEmpty then 0
  else normalizedPairDefectCount nf pairs / pairs.length

/-- Definition with formal content given by the displayed type and body.
-/
def badCriticalPairs [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) :
    List (Term sigma (RenVar nu) × Term sigma (RenVar nu)) :=
  normalizedPairDefects norm.nf (criticalPairs R)

/-- Number of emitted critical-pair defects. -/
def criticalPairDefectCount [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) : Nat :=
  normalizedPairDefectCount norm.nf (criticalPairs R)

/-- Definition with formal content given by the displayed type and body. -/
def criticalPairDefectRate [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) : ℚ :=
  normalizedPairDefectRate norm.nf (criticalPairs R)

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem criticalPairDefectCount_eq_zero_iff_decideConfluence
    [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) :
    criticalPairDefectCount R norm = 0 <-> decideConfluence R norm = true := by
  simp [criticalPairDefectCount, normalizedPairDefectCount,
    normalizedPairDefects, decideConfluence]

/-- The displayed proposition follows from the stated hypotheses.






-/
theorem criticalPairDefectCount_eq_zero_iff_confluent
    [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {norm : Normalizer (renameTRS R)}
    (hSN : WellFounded (flip (Step (renameTRS R))))
    (hnf : norm.IsNF) :
    criticalPairDefectCount R norm = 0 <->
      AbsConfluent (Step (renameTRS R)) := by
  constructor
  · intro hzero
    apply decideConfluence_sound
    · exact (criticalPairDefectCount_eq_zero_iff_decideConfluence R norm).1 hzero
    · exact hSN
  · intro hconf
    apply (criticalPairDefectCount_eq_zero_iff_decideConfluence R norm).2
    exact decideConfluence_complete norm hconf hnf

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem criticalPairDefectCount_le_criticalPairs_length
    [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) :
    criticalPairDefectCount R norm <= (criticalPairs R).length := by
  exact List.length_filter_le _ _

/-- A positive defect count exhibits a concrete emitted pair with unequal
normalizer outputs. -/
theorem criticalPairDefectCount_pos_iff_exists_bad
    [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (norm : Normalizer (renameTRS R)) :
    0 < criticalPairDefectCount R norm <->
      exists q, q ∈ criticalPairs R /\ norm.nf q.1 != norm.nf q.2 := by
  simp [criticalPairDefectCount, normalizedPairDefectCount,
    normalizedPairDefects]

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body. -/
def threePairOneBadProfile : List (Nat × Nat) :=
  [(0, 0), (1, 2), (3, 3)]

theorem threePairOneBadProfile_count :
    normalizedPairDefectCount id threePairOneBadProfile = 1 := by
  decide

theorem threePairOneBadProfile_rate :
    normalizedPairDefectRate id threePairOneBadProfile = (1 / 3 : ℚ) := by
  norm_num [normalizedPairDefectRate, normalizedPairDefectCount,
    normalizedPairDefects, threePairOneBadProfile]

/-! Declarations for the section below. -/

namespace EmptySystem

/-- Definition with formal content given by the displayed type and body. -/
def trs : TRS Nat Nat := []

/-- Definition with formal content given by the displayed type and body. -/
def norm : Normalizer (renameTRS trs) where
  nf := id
  nf_reach := fun t => StepStar.refl _ t

theorem no_step {s t : Term Nat (RenVar Nat)} :
    Not (Step (renameTRS trs) s t) := by
  intro h
  induction h with
  | root hroot =>
      rcases hroot with ⟨rule, hrule, _⟩
      simp [trs, renameTRS] at hrule
  | arg _ _ _ _ ih => exact ih

theorem norm_isNF : norm.IsNF := by
  intro t u
  exact no_step

theorem strongly_normalizing :
    WellFounded (flip (Step (renameTRS trs))) :=
  ⟨fun t => Acc.intro t (fun _ h => False.elim (no_step h))⟩

theorem defectCount_eq_zero : criticalPairDefectCount trs norm = 0 := by
  rfl

theorem confluent : AbsConfluent (Step (renameTRS trs)) :=
  (criticalPairDefectCount_eq_zero_iff_confluent strongly_normalizing norm_isNF).1
    defectCount_eq_zero

end EmptySystem

#print axioms criticalPairDefectCount_eq_zero_iff_decideConfluence
#print axioms criticalPairDefectCount_eq_zero_iff_confluent
#print axioms criticalPairDefectCount_pos_iff_exists_bad
#print axioms threePairOneBadProfile_count
#print axioms threePairOneBadProfile_rate
#print axioms EmptySystem.confluent

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
