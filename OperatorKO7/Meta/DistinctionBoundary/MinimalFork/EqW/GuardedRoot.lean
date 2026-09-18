import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Confluence

/-!
# Guarded root repair: legality, determinism, and maximality

The independent admissibility condition is: remain a raw root subrelation and
never admit the totalized difference edge on a diagonal source. Under only those
conditions, every admitted edge lies in `MiniEqWGuardedRootStep`; hence the
latter is the greatest diagonal-safe restriction of the raw root relation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Independent semantic policy for a diagonal-safe raw root subrelation. -/
structure DiagonalSafeRootSubrel (R : MiniEqWTerm → MiniEqWTerm → Prop) : Prop where
  sub_raw : ∀ {s t}, R s t → MiniEqWRootStep s t
  no_diagonal_difference : ∀ a,
    ¬ R (.eqW a a) .different

/-- The canonical guarded relation satisfies the independent safety policy. -/
theorem guardedRoot_diagonalSafe :
    DiagonalSafeRootSubrel MiniEqWGuardedRootStep where
  sub_raw := miniEqW_guardedRoot_sub_raw
  no_diagonal_difference := miniEqW_guarded_diagonal_no_different

/-- Any diagonal-safe raw root subrelation is contained in the guarded relation. -/
theorem diagonalSafeRoot_sub_guarded
    {R : MiniEqWTerm → MiniEqWTerm → Prop}
    (H : DiagonalSafeRootSubrel R) :
    ∀ {s t}, R s t → MiniEqWGuardedRootStep s t := by
  intro s t hR
  have hraw := H.sub_raw hR
  cases hraw with
  | refl a =>
      exact MiniEqWGuardedRootStep.refl a
  | diff a b =>
      by_cases hab : a = b
      · subst b
        exact False.elim ((H.no_diagonal_difference a) hR)
      · exact MiniEqWGuardedRootStep.diff a b hab

/-- Greatest-restriction crown: guarded root is safe and contains every other
safe raw root restriction. -/
theorem guardedRoot_greatest_diagonalSafe_restriction :
    DiagonalSafeRootSubrel MiniEqWGuardedRootStep ∧
      ∀ {R : MiniEqWTerm → MiniEqWTerm → Prop},
        DiagonalSafeRootSubrel R →
          ∀ {s t}, R s t → MiniEqWGuardedRootStep s t :=
  ⟨guardedRoot_diagonalSafe,
    fun H => diagonalSafeRoot_sub_guarded H⟩

/-- If a safe restriction also retains every guarded edge, it is exactly the
canonical guarded root relation. -/
theorem diagonalSafeRoot_eq_guarded_of_keeps
    {R : MiniEqWTerm → MiniEqWTerm → Prop}
    (H : DiagonalSafeRootSubrel R)
    (hkeep : ∀ {s t}, MiniEqWGuardedRootStep s t → R s t) :
    ∀ {s t}, R s t ↔ MiniEqWGuardedRootStep s t := by
  intro s t
  exact ⟨diagonalSafeRoot_sub_guarded H, hkeep⟩

/-- Off the diagonal, guarded and raw root relations agree exactly. -/
theorem guarded_offDiagonal_iff_raw
    {a b t : MiniEqWTerm} (hne : a ≠ b) :
    MiniEqWGuardedRootStep (.eqW a b) t ↔
      MiniEqWRootStep (.eqW a b) t := by
  constructor
  · exact miniEqW_guardedRoot_sub_raw
  · intro h
    cases h with
    | refl _ => exact False.elim (hne rfl)
    | diff _ _ => exact MiniEqWGuardedRootStep.diff a b hne

/-- The raw diagonal difference edge exists and the guarded relation refuses it. -/
theorem guarded_refuses_exactly_diagonal_diff (a : MiniEqWTerm) :
    MiniEqWRootStep (.eqW a a) .different ∧
      ¬ MiniEqWGuardedRootStep (.eqW a a) .different :=
  ⟨MiniEqWRootStep.diff a a, miniEqW_guarded_diagonal_no_different a⟩

/-- Executable one-step guarded root evaluator. `none` means the source is not a
root comparison redex; it is not an undecidability verdict. -/
def miniEqWGuardedEval : MiniEqWTerm → Option MiniEqWTerm
  | .eqW a b => if a = b then some .same else some .different
  | _ => none

/-- The executable evaluator is sound and complete for the guarded root relation. -/
theorem guardedRootStep_iff_eval {s t : MiniEqWTerm} :
    MiniEqWGuardedRootStep s t ↔ miniEqWGuardedEval s = some t := by
  constructor
  · intro h
    cases h with
    | refl a => simp [miniEqWGuardedEval]
    | diff a b hne => simp [miniEqWGuardedEval, hne]
  · intro h
    cases s with
    | same => simp [miniEqWGuardedEval] at h
    | different => simp [miniEqWGuardedEval] at h
    | eqW a b =>
        by_cases hab : a = b
        · subst b
          simp [miniEqWGuardedEval] at h
          subst t
          exact MiniEqWGuardedRootStep.refl a
        · simp [miniEqWGuardedEval, hab] at h
          subst t
          exact MiniEqWGuardedRootStep.diff a b hab

/-- Root confluence together with greatest admissible-policy status. -/
theorem guarded_root_repair_crown :
    (∀ source, ConfluentAt MiniEqWGuardedRootStep source) ∧
      DiagonalSafeRootSubrel MiniEqWGuardedRootStep ∧
      (∀ {R : MiniEqWTerm → MiniEqWTerm → Prop},
        DiagonalSafeRootSubrel R →
          ∀ {s t}, R s t → MiniEqWGuardedRootStep s t) :=
  ⟨guarded_root_confluent, guardedRoot_diagonalSafe,
    fun H => diagonalSafeRoot_sub_guarded H⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
