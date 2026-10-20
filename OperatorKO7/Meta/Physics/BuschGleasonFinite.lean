import Mathlib
set_option autoImplicit false

/-!
# Finite-dimensional trace representation and probabilities

Every complex-linear functional on finite square complex matrices has a unique matrix trace representer. A density operator assigns each effect a value in `[0,1]` through the trace rule. The module proves representation, uniqueness, positivity, normalization, and a concrete two-dimensional example.

The representation theorem assumes complex-linearity. The probability bound assumes a density operator and an effect in finite dimension.

Trust status: PROVEN-IN-LEAN, Mathlib baseline.
-/

namespace OperatorKO7.Meta.Physics.BuschGleasonFinite

open Matrix BigOperators

variable {d : ℕ}

/-- The trace / Born functional induced by an operator `ρ` on an operator `E`. -/
noncomputable def bornMeasure (ρ E : Matrix (Fin d) (Fin d) ℂ) : ℂ := (ρ * E).trace

/-- Representer of a `ℂ`-linear functional on matrices: `ρ i j = μ (single j i 1)`. -/
noncomputable def traceDual (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => μ (Matrix.single j i (1 : ℂ))

/-- `single i j c = c • single i j 1`. -/
theorem single_eq_smul (i j : Fin d) (c : ℂ) :
    Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
  ext i' j'
  simp only [Matrix.single, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

/-- Entry extraction: `Tr (M * single j i 1) = M i j`. -/
theorem trace_mul_single (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (M * Matrix.single j i (1 : ℂ)).trace = M i j := by
  rw [Matrix.trace]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [Matrix.single]
    · intro b _ hb
      simp only [Matrix.single, Matrix.of_apply]
      rw [if_neg (by rintro ⟨h, _⟩; exact hb h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro x _ hx
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.single, Matrix.of_apply]
    rw [if_neg (by rintro ⟨_, h⟩; exact hx h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Representation: the trace rule against `traceDual μ` reproduces `μ`. -/
theorem traceDual_represents (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (traceDual μ * A).trace = μ A := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  have hrhs : ∀ p, μ (∑ q, Matrix.single p q (A p q))
      = ∑ q, A p q * μ (Matrix.single p q 1) := by
    intro p
    rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [single_eq_smul, map_smul, smul_eq_mul]
  simp_rw [hrhs]
  rw [Matrix.trace]
  have hlhs : ∀ i, (traceDual μ * A).diag i = ∑ q, A q i * μ (Matrix.single q i 1) := by
    intro i
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [traceDual, Matrix.of_apply, mul_comm]
  simp_rw [hlhs]
  rw [Finset.sum_comm]

/-- Two operators that induce the same trace functional on every matrix are equal. -/
theorem trace_rule_unique (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ A, (ρ * A).trace = (σ * A).trace) : ρ = σ := by
  ext i j
  have := h (Matrix.single j i (1 : ℂ))
  rwa [trace_mul_single, trace_mul_single] at this

/-- Every complex-linear functional on these finite matrices has a unique matrix representing it by trace. -/
theorem busch_gleason_representation (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) :
    ∃! ρ : Matrix (Fin d) (Fin d) ℂ, ∀ A, (ρ * A).trace = μ A := by
  refine ⟨traceDual μ, traceDual_represents μ, ?_⟩
  intro ρ hρ
  apply trace_rule_unique
  intro A
  rw [hρ A, traceDual_represents μ A]

/-- The trace functional is additive in its matrix argument. -/
theorem bornMeasure_add (ρ E F : Matrix (Fin d) (Fin d) ℂ) :
    bornMeasure ρ (E + F) = bornMeasure ρ E + bornMeasure ρ F := by
  simp [bornMeasure, mul_add, Matrix.trace_add]

/-- Forward direction (normalization): a unit-trace operator sends the identity effect to
one. -/
theorem bornMeasure_one (ρ : Matrix (Fin d) (Fin d) ℂ) (h : ρ.trace = 1) :
    bornMeasure ρ 1 = 1 := by
  simp [bornMeasure, h]

/-! ## Positivity layer: a density operator induces probabilities in `[0,1]` -/

open scoped ComplexOrder

/-- Diagonal entries of a positive-semidefinite matrix are nonnegative. -/
theorem diag_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (h : A.PosSemidef) (i : Fin d) :
    0 ≤ A i i := by
  have h2 := h.2 (Pi.single i 1)
  rw [show star (Pi.single i (1 : ℂ)) = (Pi.single i 1 : Fin d → ℂ) by
        ext k; simp [Pi.single_apply, Pi.star_apply, apply_ite]] at h2
  rw [Matrix.mulVec_single, MulOpposite.op_one, one_smul, single_one_dotProduct] at h2
  simpa using h2

/-- The trace of a positive-semidefinite matrix is nonnegative. -/
theorem psd_trace_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (h : A.PosSemidef) :
    0 ≤ A.trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intro i _
  rw [Matrix.diag_apply]
  exact diag_nonneg h i

/-- The trace of a product of two PSD matrices is nonnegative (`Tr(ρE) = Tr(√ρ E √ρ)`, and
`√ρ E √ρ` is positive-semidefinite by conjugation). -/
theorem psd_mul_trace_nonneg {ρ E : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) : 0 ≤ (ρ * E).trace := by
  have hHerm : (hρ.sqrt)ᴴ = hρ.sqrt := hρ.posSemidef_sqrt.1.eq
  have hcyc : (ρ * E).trace = (hρ.sqrt * E * hρ.sqrt).trace := by
    conv_lhs => rw [← hρ.sqrt_mul_self]
    rw [mul_assoc, Matrix.trace_mul_comm]
  have hpsd : (hρ.sqrt * E * hρ.sqrt).PosSemidef := by
    have := hE.mul_mul_conjTranspose_same hρ.sqrt
    rwa [hHerm] at this
  rw [hcyc]
  exact psd_trace_nonneg hpsd

/-- An effect: a positive-semidefinite operator dominated by the identity (`0 ≤ E ≤ 1`). -/
def IsEffect (E : Matrix (Fin d) (Fin d) ℂ) : Prop := E.PosSemidef ∧ (1 - E).PosSemidef

/-- A density operator: positive-semidefinite with unit trace. -/
def IsDensity (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- **Born values are probabilities.** For a density operator `ρ` and an effect `E`,
`0 ≤ Tr(ρE) ≤ 1`. -/
theorem bornMeasure_mem_unitInterval {ρ E : Matrix (Fin d) (Fin d) ℂ}
    (hρ : IsDensity ρ) (hE : IsEffect E) :
    0 ≤ bornMeasure ρ E ∧ bornMeasure ρ E ≤ 1 := by
  refine ⟨psd_mul_trace_nonneg hρ.1 hE.1, ?_⟩
  have hcompl : 0 ≤ (ρ * (1 - E)).trace := psd_mul_trace_nonneg hρ.1 hE.2
  have hsplit : (ρ * (1 - E)).trace = ρ.trace - bornMeasure ρ E := by
    rw [bornMeasure, mul_sub, mul_one, Matrix.trace_sub]
  rw [hsplit, hρ.2] at hcompl
  exact sub_nonneg.mp hcompl

/-! ## Concrete qubit example -/

/-- The maximally mixed qubit state `(1/2) I`. -/
noncomputable def mixedQubit : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem mixedQubit_trace : mixedQubit.trace = 1 := by
  simp only [mixedQubit, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

/-- A concrete effect: the diagonal projector onto `|0>`. -/
def proj0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]

/-- The Born value of the mixed qubit on the `|0>` projector is `1/2`, a concrete probability
in `[0,1]`. -/
theorem bornMeasure_mixed_proj0 : bornMeasure mixedQubit proj0 = 1 / 2 := by
  have hp : proj0.trace = 1 := by
    simp only [proj0, Matrix.trace_diagonal]
    simp [Fin.sum_univ_two]
  simp only [bornMeasure, mixedQubit, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul, hp]
  norm_num

end OperatorKO7.Meta.Physics.BuschGleasonFinite
