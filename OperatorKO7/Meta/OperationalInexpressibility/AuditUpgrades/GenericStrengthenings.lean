import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.SchemaNormMismatch

/-!
# Two statement strengthenings free of the concrete kernel

Proves: (1) no additive whole-term measure with arbitrary natural weights, the wrapper weight
zero included, orients the duplicating step of a step-duplicating schema, with the step argument
`S(base)`; (2) on the constant wrapper vector with `i, |b| ≥ 1`, the six coincidences of the four
observables (distinct components, support count, maximum, additive size) hold at `i = 1`,
`|b| = 1`, `i = |b| = 1`, `i = |b|`, `|b| = 1` and `i = 1`, so the four values are pairwise distinct
if and only if `i ≥ 2`, `|b| ≥ 2` and `i ≠ |b|`.
Relation: the schema step `wrap s (recur b s n) ← recur b s (succ n)`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: natural-valued weights; `i`, `|b|` natural numbers.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.GenericStrengthenings

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-! ## (1) Additive barrier for every natural weight vector -/

/-- An additive whole-term measure with natural weights and no positivity condition. -/
structure NonnegAdditiveMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) = w_recur + eval b + eval s + eval n

/-- No additive measure with natural weights orients the duplicating step; the step argument
`S(base)` already defeats it. -/
theorem no_nonnegAdditive_orients_dup_step {S : StepDuplicatingSchema}
    (M : NonnegAdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base (S.succ S.base) S.base
  simp only [M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur] at hspec
  omega

/-! ## (2) The four observables of the constant wrapper vector -/

theorem seedRank_eq_support_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    diagonalSeedRank i = diagonalSupportCount p i ↔ i = 1 := by
  rw [diagonalSeedRank_eq_one i hi, diagonalSupportCount_of_pos p i hp]
  omega

theorem seedRank_eq_max_iff (p i : Nat) (hi : 1 ≤ i) :
    diagonalSeedRank i = ellInfNormOnDiagonal p i ↔ p = 1 := by
  rw [diagonalSeedRank_eq_one i hi, ellInfNormOnDiagonal_pos p i hi]
  omega

theorem seedRank_eq_additive_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    diagonalSeedRank i = ell1NormOnDiagonal p i ↔ i = 1 ∧ p = 1 := by
  rw [diagonalSeedRank_eq_one i hi, ell1NormOnDiagonal_eq]
  constructor
  · intro h
    have hsum : i + p ≤ 2 := by nlinarith
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem support_eq_max_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    diagonalSupportCount p i = ellInfNormOnDiagonal p i ↔ i = p := by
  rw [diagonalSupportCount_of_pos p i hp, ellInfNormOnDiagonal_pos p i hi]

theorem support_eq_additive_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    diagonalSupportCount p i = ell1NormOnDiagonal p i ↔ p = 1 := by
  rw [diagonalSupportCount_of_pos p i hp, ell1NormOnDiagonal_eq]
  constructor
  · intro h
    have h' : i * p = i * 1 := by rw [Nat.mul_one]; exact h.symm
    exact Nat.eq_of_mul_eq_mul_left hi h'
  · rintro rfl
    rw [Nat.mul_one]

theorem max_eq_additive_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    ellInfNormOnDiagonal p i = ell1NormOnDiagonal p i ↔ i = 1 := by
  rw [ellInfNormOnDiagonal_pos p i hi, ell1NormOnDiagonal_eq]
  constructor
  · intro h
    have h' : i * p = 1 * p := by rw [Nat.one_mul]; exact h.symm
    exact Nat.eq_of_mul_eq_mul_right hp h'
  · rintro rfl
    rw [Nat.one_mul]

/-- The four observables are pairwise distinct exactly when `i ≥ 2`, `|b| ≥ 2` and `i ≠ |b|`. -/
theorem four_observables_pairwise_distinct_iff (p i : Nat) (hi : 1 ≤ i) (hp : 1 ≤ p) :
    (diagonalSeedRank i ≠ diagonalSupportCount p i ∧
      diagonalSeedRank i ≠ ellInfNormOnDiagonal p i ∧
      diagonalSeedRank i ≠ ell1NormOnDiagonal p i ∧
      diagonalSupportCount p i ≠ ellInfNormOnDiagonal p i ∧
      diagonalSupportCount p i ≠ ell1NormOnDiagonal p i ∧
      ellInfNormOnDiagonal p i ≠ ell1NormOnDiagonal p i) ↔
      (2 ≤ i ∧ 2 ≤ p ∧ i ≠ p) := by
  rw [Ne, seedRank_eq_support_iff p i hi hp, Ne, seedRank_eq_max_iff p i hi, Ne,
    seedRank_eq_additive_iff p i hi hp, Ne, support_eq_max_iff p i hi hp, Ne,
    support_eq_additive_iff p i hi hp, Ne, max_eq_additive_iff p i hi hp]
  omega

/-- At `i = 2` and `|b| = 3` the four observables take the four distinct values `1, 2, 3, 6`. -/
theorem four_observables_sample :
    diagonalSeedRank 2 = 1 ∧ diagonalSupportCount 3 2 = 2 ∧
      ellInfNormOnDiagonal 3 2 = 3 ∧ ell1NormOnDiagonal 3 2 = 6 := by
  decide

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.GenericStrengthenings
