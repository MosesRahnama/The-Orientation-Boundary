/-!
# Witness-rank predicates

`WitnessTower` contains an arbitrary level type, a natural-valued rank, and a
proposition indicating witness availability. `kappaLe T n` asserts existence
of a witness at rank at most `n`; `kappaGt T n` asserts the pointwise absence
of such witnesses. `BoundaryAt` is an alias for `kappaGt`, so it also holds for
a tower with no witnesses at any rank. The two-level fixture separately proves
both a rank-zero boundary and witness availability by rank one.

The least adequate rank `kappaStar`, conditional on witness existence, is
defined and related to `BoundaryAt` in
`Meta/MetaMetaLayer/KappaStarBoundary.lean`. This file supplies the predicates
used by that construction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary

/-- A witness tower over a level type `Level` ranked into the naturals. `has l` is the proposition that
the domain has a witness at level `l`; the cheapest levels have the smallest rank. -/
structure WitnessTower where
  Level : Type
  rank : Level → Nat
  has : Level → Prop

namespace WitnessTower

/-- Some witness exists at or below rank `n` (the domain is certifiable by rank `n`). -/
def kappaLe (T : WitnessTower) (n : Nat) : Prop :=
  ∃ l : T.Level, T.rank l ≤ n ∧ T.has l

/-- Every level of rank at most `n` lacks a witness. -/
def kappaGt (T : WitnessTower) (n : Nat) : Prop :=
  ∀ l : T.Level, T.rank l ≤ n → ¬ T.has l

/-- Alias for absence of witnesses at ranks at most `n`. Witness existence above `n` is a separate
condition. -/
def BoundaryAt (T : WitnessTower) (n : Nat) : Prop :=
  kappaGt T n

theorem boundaryAt_iff_kappaGt (T : WitnessTower) (n : Nat) :
    BoundaryAt T n ↔ kappaGt T n := Iff.rfl

/-- `BoundaryAt T n` excludes a witness at each level whose rank is at most `n`. -/
theorem boundary_no_cheap_witness (T : WitnessTower) (n : Nat)
    (h : BoundaryAt T n) (l : T.Level) (hl : T.rank l ≤ n) :
    ¬ T.has l :=
  h l hl

/-- `kappaLe` and `kappaGt` at the same rank are mutually exclusive: a tower cannot both have and lack a
witness at or below `n`. -/
theorem not_kappaLe_and_kappaGt (T : WitnessTower) (n : Nat) :
    ¬ (kappaLe T n ∧ kappaGt T n) := by
  rintro ⟨⟨l, hl, hhas⟩, hgt⟩
  exact hgt l hl hhas

/-- Monotonicity of certifiability: a witness at or below `m` is also a witness at or below any larger
`n`. Certifiability only improves as the admissible rank rises. -/
theorem kappaLe_mono (T : WitnessTower) {m n : Nat} (hmn : m ≤ n) (h : kappaLe T m) :
    kappaLe T n := by
  obtain ⟨l, hl, hhas⟩ := h
  exact ⟨l, Nat.le_trans hl hmn, hhas⟩

/-! ## Two-level fixture -/

/-- A two-level tower with no witness at rank zero and a witness at rank one. -/
def directBlockedTower : WitnessTower where
  Level := Bool
  rank := fun b => if b then 1 else 0
  has := fun b => b = true

/-- The two-level fixture has no witness at rank zero. -/
theorem directBlockedTower_boundary_at_zero : BoundaryAt directBlockedTower 0 := by
  intro l hl
  cases l with
  | false => simp [directBlockedTower]
  | true => simp [directBlockedTower] at hl

/-- The two-level fixture has a witness by rank one. -/
theorem directBlockedTower_kappaLe_one : kappaLe directBlockedTower 1 := by
  exact ⟨true, by simp [directBlockedTower], by simp [directBlockedTower]⟩

/-- Combines rank-zero absence with witness availability by rank one. -/
theorem directBlockedTower_is_boundary :
    BoundaryAt directBlockedTower 0 ∧ kappaLe directBlockedTower 1 :=
  ⟨directBlockedTower_boundary_at_zero, directBlockedTower_kappaLe_one⟩

end WitnessTower

end OperatorKO7.Meta.UniversalBoundary
