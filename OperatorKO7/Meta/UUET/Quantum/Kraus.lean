import OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation
import OperatorKO7.Meta.UUET.Quantum.DensityMatrix
import OperatorKO7.Meta.UUET.Quantum.PhaseTwirl

set_option autoImplicit false

/-!
# Finite Kraus families

Relation: equality of finite Kraus-sum channel actions.
Closure: finite operator-sum representations and their completeness equation.
Trust: kernel-checked matrix positivity and finite sums.
Scope: complete positivity is represented by explicit Kraus form; no abstract-CP converse.
-/

namespace OperatorKO7.Meta.UUET.Quantum

open Matrix
open scoped ComplexOrder

/-- Application of a finite Kraus family. -/
noncomputable def krausApply {m n k : Nat}
    (K : Fin k -> Matrix (Fin m) (Fin n) ℂ)
    (ρ : Operator (Fin n)) : Operator (Fin m) :=
  OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus K ρ

/-- Kraus completeness equation for trace preservation. -/
def KrausTracePreserving {m n k : Nat}
    (K : Fin k -> Matrix (Fin m) (Fin n) ℂ) : Prop :=
  (∑ a, (K a)ᴴ * K a : Operator (Fin n)) = 1

/-- A Kraus sum maps PSD inputs to PSD outputs. -/
theorem krausApply_positiveSemidefinite {m n k : Nat}
    (K : Fin k -> Matrix (Fin m) (Fin n) ℂ)
    {ρ : Operator (Fin n)} (hρ : PositiveSemidefinite ρ) :
    PositiveSemidefinite (krausApply K ρ) := by
  exact OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus_posSemidef K hρ

/-- Computational-basis projectors used by the qubit measurement channel. -/
noncomputable def qubitProjector (i : Fin 2) : Operator (Fin 2) :=
  OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.krausP i

theorem projectiveKraus_tracePreserving :
    KrausTracePreserving qubitProjector := by
  exact OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.meas_kraus_isTP

/-- Negative fixture: an empty Kraus family is not trace preserving on a qubit. -/
theorem emptyKraus_not_tracePreserving :
    Not (KrausTracePreserving (m := 2) (n := 2)
      (fun i : Fin 0 => (Fin.elim0 i : Matrix (Fin 2) (Fin 2) ℂ))) := by
  intro h
  have h00 := congrArg (fun A : Operator (Fin 2) => A 0 0) h
  norm_num [KrausTracePreserving] at h00

/-! Imported NameGate and TypeGate. -/
#check @OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus
#check @OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.cpMapKraus_posSemidef
#check @OperatorKO7.Meta.ReverseBridge.QMLaw_FiniteDilation.meas_kraus_isTP
#check @krausApply

#check @krausApply_positiveSemidefinite
#print axioms krausApply_positiveSemidefinite
#check @projectiveKraus_tracePreserving
#print axioms projectiveKraus_tracePreserving
#check @emptyKraus_not_tracePreserving
#print axioms emptyKraus_not_tracePreserving


/-! ## Bayesian conditioning on the diagonal subalgebra -/

/-- The square-root likelihood operator for a finite classical outcome. -/
noncomputable def likelihoodFilter {ι : Type} [DecidableEq ι]
    (ℓ : ι → ℝ) : Operator ι :=
  Matrix.diagonal (fun i => (Real.sqrt (ℓ i) : ℂ))

/-- A diagonal Kraus branch is unnormalized classical likelihood multiplication. -/
theorem likelihoodFilter_diagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (p ℓ : ι → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i) :
    likelihoodFilter ℓ * Matrix.diagonal (fun i => (p i : ℂ)) *
        (likelihoodFilter ℓ)ᴴ =
      Matrix.diagonal (fun i => ((ℓ i * p i : ℝ) : ℂ)) := by
  ext i j
  change (Matrix.diagonal (fun i => (Real.sqrt (ℓ i) : ℂ)) *
    Matrix.diagonal (fun i => (p i : ℂ)) *
    (Matrix.diagonal (fun i => (Real.sqrt (ℓ i) : ℂ)))ᴴ) i j = _
  rw [diagonal_conjugation_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Complex.star_def, Complex.conj_ofReal]
    have hs : (Real.sqrt (ℓ i) : ℂ) * (Real.sqrt (ℓ i) : ℂ) = (ℓ i : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (hℓ i)
    calc
      _ = ((Real.sqrt (ℓ i) : ℂ) * (Real.sqrt (ℓ i) : ℂ)) * (p i : ℂ) := by ring
      _ = _ := by rw [hs]; push_cast; rfl
  · simp [hij]

/-- The branch probability is the classical evidence normalizer. -/
theorem likelihoodFilter_trace {ι : Type} [Fintype ι] [DecidableEq ι]
    (p ℓ : ι → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i) :
    Matrix.trace (likelihoodFilter ℓ * Matrix.diagonal (fun i => (p i : ℂ)) *
        (likelihoodFilter ℓ)ᴴ) =
      ((∑ i, ℓ i * p i : ℝ) : ℂ) := by
  rw [likelihoodFilter_diagonal p ℓ hℓ, Matrix.trace_diagonal]
  norm_cast

/-- The normalized branch is exactly the diagonal Bayesian posterior. -/
theorem likelihoodFilter_bayes {ι : Type} [Fintype ι] [DecidableEq ι]
    (p ℓ : ι → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i) :
    (((∑ i, ℓ i * p i : ℝ) : ℂ)⁻¹) •
        (likelihoodFilter ℓ * Matrix.diagonal (fun i => (p i : ℂ)) *
          (likelihoodFilter ℓ)ᴴ) =
      Matrix.diagonal (fun i => ((ℓ i * p i / ∑ j, ℓ j * p j : ℝ) : ℂ)) := by
  rw [likelihoodFilter_diagonal p ℓ hℓ]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [div_eq_mul_inv, mul_comm]
  · simp [hij]

/-- A positive-probability diagonal posterior is itself a density matrix. -/
theorem diagonal_bayes_density {ι : Type} [Fintype ι] [DecidableEq ι]
    (p ℓ : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hZ : 0 < ∑ i, ℓ i * p i) :
    PositiveSemidefinite
        (Matrix.diagonal (fun i => ((ℓ i * p i / ∑ j, ℓ j * p j : ℝ) : ℂ))) ∧
      Matrix.trace
        (Matrix.diagonal (fun i => ((ℓ i * p i / ∑ j, ℓ j * p j : ℝ) : ℂ))) = 1 := by
  constructor
  · rw [PositiveSemidefinite, Matrix.posSemidef_diagonal_iff]
    intro i
    exact Complex.zero_le_real.mpr (div_nonneg (mul_nonneg (hℓ i) (hp i)) hZ.le)
  · rw [Matrix.trace_diagonal]
    have hs : ∑ i, ℓ i * p i / ∑ j, ℓ j * p j = (1 : ℝ) := by
      rw [← Finset.sum_div, div_self (ne_of_gt hZ)]
    exact_mod_cast hs

/-- A likelihood in [0,1] and its complement form a complete binary instrument. -/
theorem likelihoodFilter_complete {ι : Type} [Fintype ι] [DecidableEq ι]
    (ℓ : ι → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) :
    (likelihoodFilter ℓ)ᴴ * likelihoodFilter ℓ +
      (likelihoodFilter (fun i => 1 - ℓ i))ᴴ *
        likelihoodFilter (fun i => 1 - ℓ i) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, likelihoodFilter, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    simp [Matrix.diagonal_apply]
    norm_cast
    rw [Real.mul_self_sqrt (hℓ0 i), Real.mul_self_sqrt (sub_nonneg.mpr (hℓ1 i))]
    ring
  · simp [likelihoodFilter, hij]

#check @likelihoodFilter
#print axioms likelihoodFilter
#check @likelihoodFilter_diagonal
#print axioms likelihoodFilter_diagonal
#check @likelihoodFilter_trace
#print axioms likelihoodFilter_trace
#check @likelihoodFilter_bayes
#print axioms likelihoodFilter_bayes
#check @diagonal_bayes_density
#print axioms diagonal_bayes_density
#check @likelihoodFilter_complete
#print axioms likelihoodFilter_complete

end OperatorKO7.Meta.UUET.Quantum
