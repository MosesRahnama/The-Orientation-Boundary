import OperatorKO7.Meta.UUET.Quantum.FiniteHilbert

set_option autoImplicit false

/-!
# Positive-semidefinite finite operators

Relation: the Mathlib complex positive-semidefinite order.
Closure: rank-one outer products and nonnegative real scaling.
Trust: kernel-checked matrix positivity lemmas.
Scope: finite complex matrices; no infinite-dimensional spectral claim.
-/

namespace OperatorKO7.Meta.UUET.Quantum

open Matrix
open scoped ComplexOrder

/-- Canonical UUET spelling of finite matrix positive semidefiniteness. -/
def PositiveSemidefinite {ι : Type} [Fintype ι] (A : Operator ι) : Prop :=
  A.PosSemidef

/-- Every rank-one outer product is positive semidefinite. -/
theorem outer_positiveSemidefinite {ι : Type} [Fintype ι] (ψ : Ket ι) :
    PositiveSemidefinite (outer ψ) := by
  exact Matrix.posSemidef_self_mul_conjTranspose (ketColumn ψ)

/-- Nonnegative real scaling preserves positive semidefiniteness. -/
theorem real_smul_positiveSemidefinite {ι : Type} [Fintype ι]
    {A : Operator ι} (hA : PositiveSemidefinite A) {r : ℝ} (hr : 0 <= r) :
    PositiveSemidefinite ((r : ℂ) • A) := by
  refine ⟨?_, ?_⟩
  · show ((r : ℂ) • A)ᴴ = (r : ℂ) • A
    rw [Matrix.conjTranspose_smul, hA.1.eq, Complex.star_def, Complex.conj_ofReal]
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr hr) (hA.2 x)

/-- Explicit negative fixture: a diagonal operator with entry `-1` is not PSD. -/
noncomputable def negativeDiagonalQubit : Operator (Fin 2) :=
  Matrix.diagonal ![-1, 0]

theorem negativeDiagonalQubit_not_positiveSemidefinite :
    Not (PositiveSemidefinite negativeDiagonalQubit) := by
  intro h
  have h0 := (Matrix.posSemidef_diagonal_iff.mp h) 0
  norm_num [negativeDiagonalQubit] at h0

/-! Imported NameGate and TypeGate. -/
#check @Matrix.posSemidef_self_mul_conjTranspose
#check @Matrix.posSemidef_diagonal_iff
#check @Complex.zero_le_real
#check @PositiveSemidefinite

#check @outer_positiveSemidefinite
#print axioms outer_positiveSemidefinite
#check @real_smul_positiveSemidefinite
#print axioms real_smul_positiveSemidefinite
#check @negativeDiagonalQubit_not_positiveSemidefinite
#print axioms negativeDiagonalQubit_not_positiveSemidefinite

end OperatorKO7.Meta.UUET.Quantum
