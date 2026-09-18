import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Syntax
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Raw and guarded root equality-witness relations

Raw relation:
* `eqW(x,x) -> same`
* `eqW(x,y) -> different` for every pair, including the diagonal.

Guarded relation:
* `eqW(x,x) -> same`
* `eqW(x,y) -> different` only when `x ≠ y`.

These are root-only relations. Context closure is defined separately.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- The exact two-rule unguarded root relation. -/
inductive MiniEqWRootStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | refl (t : MiniEqWTerm) : MiniEqWRootStep (.eqW t t) .same
  | diff (s t : MiniEqWTerm) : MiniEqWRootStep (.eqW s t) .different

/-- The guarded root repair deletes only diagonal difference steps. -/
inductive MiniEqWGuardedRootStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | refl (t : MiniEqWTerm) : MiniEqWGuardedRootStep (.eqW t t) .same
  | diff (s t : MiniEqWTerm) (hne : s ≠ t) :
      MiniEqWGuardedRootStep (.eqW s t) .different

/-- Every guarded root step is a raw root step. -/
theorem miniEqW_guardedRoot_sub_raw
    {s t : MiniEqWTerm} (h : MiniEqWGuardedRootStep s t) :
    MiniEqWRootStep s t := by
  cases h with
  | refl x => exact MiniEqWRootStep.refl x
  | diff x y _ => exact MiniEqWRootStep.diff x y

/-- The raw diagonal has both one-step verdicts. -/
theorem miniEqW_raw_closed_diagonal_peak :
    MiniEqWRootStep miniEqWClosedDiagonal .same ∧
      MiniEqWRootStep miniEqWClosedDiagonal .different :=
  ⟨MiniEqWRootStep.refl .same, MiniEqWRootStep.diff .same .same⟩

/-- Guarded root rewriting admits the equal diagonal verdict. -/
theorem miniEqW_guarded_diagonal_equal (t : MiniEqWTerm) :
    MiniEqWGuardedRootStep (.eqW t t) .same :=
  MiniEqWGuardedRootStep.refl t

/-- Guarded root rewriting refuses a diagonal difference verdict. -/
theorem miniEqW_guarded_diagonal_no_different (t : MiniEqWTerm) :
    ¬ MiniEqWGuardedRootStep (.eqW t t) .different := by
  intro h
  cases h with
  | diff _ _ hne => exact hne rfl

/-- Every syntactically off-diagonal query still emits the difference verdict. -/
theorem miniEqW_guarded_offDiagonal_difference
    {s t : MiniEqWTerm} (hne : s ≠ t) :
    MiniEqWGuardedRootStep (.eqW s t) .different :=
  MiniEqWGuardedRootStep.diff s t hne

/-- Root sources and targets are completely classified for the raw relation. -/
theorem miniEqW_rawRoot_iff {s t : MiniEqWTerm} :
    MiniEqWRootStep s t ↔
      (∃ x, s = .eqW x x ∧ t = .same) ∨
      (∃ x y, s = .eqW x y ∧ t = .different) := by
  constructor
  · intro h
    cases h with
    | refl x => exact Or.inl ⟨x, rfl, rfl⟩
    | diff x y => exact Or.inr ⟨x, y, rfl, rfl⟩
  · intro h
    rcases h with ⟨x, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
    · exact MiniEqWRootStep.refl x
    · exact MiniEqWRootStep.diff x y

/-- Root sources and targets are completely classified for the guarded relation. -/
theorem miniEqW_guardedRoot_iff {s t : MiniEqWTerm} :
    MiniEqWGuardedRootStep s t ↔
      (∃ x, s = .eqW x x ∧ t = .same) ∨
      (∃ x y, x ≠ y ∧ s = .eqW x y ∧ t = .different) := by
  constructor
  · intro h
    cases h with
    | refl x => exact Or.inl ⟨x, rfl, rfl⟩
    | diff x y hne => exact Or.inr ⟨x, y, hne, rfl, rfl⟩
  · intro h
    rcases h with ⟨x, rfl, rfl⟩ | ⟨x, y, hne, rfl, rfl⟩
    · exact MiniEqWGuardedRootStep.refl x
    · exact MiniEqWGuardedRootStep.diff x y hne

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
