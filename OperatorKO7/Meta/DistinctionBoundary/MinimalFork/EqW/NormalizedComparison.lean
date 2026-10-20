import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.GuardedRoot

/-!
# Context-stable repair II: normalize arguments before comparing

This strategy is deterministic and explicitly strategy-scoped. It computes a
canonical verdict for each argument recursively, compares those canonical
verdicts, and emits exactly one outer verdict. It is not the unrestricted
contextual closure of `MiniEqWGuardedRootStep`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Canonical recursive normalization for the minimal comparator language. -/
def miniEqWNormalize : MiniEqWTerm → MiniEqWTerm
  | .same => .same
  | .different => .different
  | .eqW a b =>
      if miniEqWNormalize a = miniEqWNormalize b then .same else .different

/-- Canonical normalization always returns one of the two verdict constants. -/
theorem miniEqWNormalize_is_verdict (t : MiniEqWTerm) :
    miniEqWNormalize t = .same ∨ miniEqWNormalize t = .different := by
  induction t with
  | same => exact Or.inl rfl
  | different => exact Or.inr rfl
  | eqW a b _ _ =>
      simp only [miniEqWNormalize]
      by_cases h : miniEqWNormalize a = miniEqWNormalize b
      · simp [h]
      · simp [h]

/-- Canonical normalization is idempotent. -/
theorem miniEqWNormalize_idempotent (t : MiniEqWTerm) :
    miniEqWNormalize (miniEqWNormalize t) = miniEqWNormalize t := by
  rcases miniEqWNormalize_is_verdict t with h | h <;> rw [h] <;> rfl

/-- One atomic normalized-argument comparison step. -/
inductive NormalizedComparisonStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | compare (a b : MiniEqWTerm) :
      NormalizedComparisonStep (.eqW a b)
        (if miniEqWNormalize a = miniEqWNormalize b then .same else .different)

/-- The strategy has exactly one target at every comparison source. -/
theorem normalizedComparison_functional
    {s l r : MiniEqWTerm}
    (hl : NormalizedComparisonStep s l)
    (hr : NormalizedComparisonStep s r) : l = r := by
  cases hl
  cases hr
  rfl

/-- Every normalized comparison step strictly lowers `miniEqWCount`. -/
theorem normalizedComparison_count_decreases
    {s t : MiniEqWTerm} (h : NormalizedComparisonStep s t) :
    miniEqWCount t < miniEqWCount s := by
  cases h with
  | compare a b =>
      by_cases hab : miniEqWNormalize a = miniEqWNormalize b
      · simp [hab, miniEqWCount]
      · simp [hab, miniEqWCount]

/-- Normalize-before-compare is strongly normalizing. -/
theorem normalizedComparison_SN : WellFounded (flip NormalizedComparisonStep) :=
  wf_flip_of_nat_decrease miniEqWCount normalizedComparison_count_decreases

/-- Normalize-before-compare is confluent at every source. -/
theorem normalizedComparison_confluent (source : MiniEqWTerm) :
    ConfluentAt NormalizedComparisonStep source :=
  confluentAt_of_functional (R := NormalizedComparisonStep)
    normalizedComparison_functional source

/-- A term is already canonical for this strategy when normalization fixes it. -/
def MiniEqWNormalizeFixed (t : MiniEqWTerm) : Prop :=
  miniEqWNormalize t = t

/-- On already canonical arguments, normalized comparison agrees exactly with
the guarded root comparison. -/
theorem normalizedComparison_iff_guardedRoot_of_fixed
    {a b t : MiniEqWTerm}
    (ha : MiniEqWNormalizeFixed a)
    (hb : MiniEqWNormalizeFixed b) :
    NormalizedComparisonStep (.eqW a b) t ↔
      MiniEqWGuardedRootStep (.eqW a b) t := by
  simp only [MiniEqWNormalizeFixed] at ha hb
  by_cases hab : a = b
  · subst b
    constructor
    · intro h
      cases h
      simpa using (MiniEqWGuardedRootStep.refl a)
    · intro h
      cases h with
      | refl _ => simpa using (NormalizedComparisonStep.compare a a)
      | diff _ _ hne => exact False.elim (hne rfl)
  · have hnormne : miniEqWNormalize a ≠ miniEqWNormalize b := by
      intro h
      apply hab
      rw [ha, hb] at h
      exact h
    constructor
    · intro h
      cases h
      simpa [hnormne] using (MiniEqWGuardedRootStep.diff a b hab)
    · intro h
      cases h with
      | refl _ => exact False.elim (hab rfl)
      | diff _ _ _ =>
          simpa [hnormne] using (NormalizedComparisonStep.compare a b)

/-- Roadmap-stable evaluator name. -/
def normalizeThenCompare := miniEqWNormalize

/-- Roadmap-stable determinism theorem. -/
theorem normalizeThenCompare_deterministic
    {s l r : MiniEqWTerm}
    (hl : NormalizedComparisonStep s l)
    (hr : NormalizedComparisonStep s r) : l = r :=
  normalizedComparison_functional hl hr

/-- Roadmap-stable confluence theorem. -/
theorem normalizeThenCompare_confluent (source : MiniEqWTerm) :
    ConfluentAt NormalizedComparisonStep source :=
  normalizedComparison_confluent source

/-- The two verdict constants are fixed points. -/
theorem miniEqW_same_fixed : MiniEqWNormalizeFixed .same := rfl

theorem miniEqW_different_fixed : MiniEqWNormalizeFixed .different := rfl

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
