import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# Exact diagonal-fork schema

Unlike the legacy portability schema, this authoritative schema stores only the
one-step relation. Joinability is definitionally the actual exact-length
reflexive-transitive closure `Quantitative.Reach R`; callers cannot inject extra
closure edges.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u

/-- Internalized equality/difference verdict architecture over an exact relation. -/
structure ExactDiagonalForkSchema (T : Type u) where
  R : T → T → Prop
  E : T → T → T
  Z : T
  D : T → T → T
  refl_rule : ∀ a, R (E a a) Z
  diff_rule : ∀ a b, R (E a b) (D a b)

variable {T : Type u}

/-- Local joinability of one-step successors, using `Reach S.R`. -/
def LocalJoinAt (S : ExactDiagonalForkSchema T) (source : T) : Prop :=
  ∀ {l r}, S.R source l → S.R source r → Joinable S.R l r

/-- Joinability of the equal and totalized-difference diagonal verdicts. -/
def DiagonalVerdictsJoin (S : ExactDiagonalForkSchema T) (a : T) : Prop :=
  Joinable S.R S.Z (S.D a a)

/-- The terminal-diagonal hypotheses that turn verdict distinction into a
mechanical nonjoinability theorem. -/
structure TerminalDiagonal (S : ExactDiagonalForkSchema T) (a : T) : Prop where
  equal_normal : NormalForm S.R S.Z
  different_normal : NormalForm S.R (S.D a a)
  verdicts_distinct : S.Z ≠ S.D a a

/-- A diagonal source is determined when its only one-step outputs are the two
schema verdicts. -/
def DiagonalDetermined (S : ExactDiagonalForkSchema T) (a : T) : Prop :=
  ∀ {t}, S.R (S.E a a) t → t = S.Z ∨ t = S.D a a

/-- The exact schema always has the two designated diagonal one-step exits. -/
theorem exact_diagonal_peak (S : ExactDiagonalForkSchema T) (a : T) :
    S.R (S.E a a) S.Z ∧ S.R (S.E a a) (S.D a a) :=
  ⟨S.refl_rule a, S.diff_rule a a⟩

/-- Reflexive joinability in the exact closure. -/
theorem exact_joinable_refl (R : T → T → Prop) (x : T) : Joinable R x x :=
  ⟨x, reach_refl x, reach_refl x⟩

/-- Joinability is symmetric. -/
theorem exact_joinable_symm {R : T → T → Prop} {x y : T}
    (h : Joinable R x y) : Joinable R y x := by
  rcases h with ⟨z, hx, hy⟩
  exact ⟨z, hy, hx⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
