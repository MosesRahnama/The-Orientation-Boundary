import OperatorKO7.Meta.UUET.Quantum.BellState

set_option autoImplicit false

/-!
# Global and relative phase behavior

Relation: equality under global phase and averaging under a relative phase flip.
Closure: rank-one projectors and an explicit two-point qubit twirl.
Trust: kernel-checked finite complex matrix algebra.
Scope: exact finite phase fixtures; no uncontrolled ensemble interpretation.
-/

namespace OperatorKO7.Meta.UUET.Quantum

/-- Apply one global complex phase to a ket. -/
def globalPhase {ι : Type} (z : ℂ) (ψ : Ket ι) : Ket ι :=
  fun i => z * ψ i

/-- Global phase leaves a rank-one projector unchanged. -/
theorem globalPhase_projector_invariant {ι : Type} (z : ℂ) (ψ : Ket ι)
    (hz : z * star z = 1) :
    outer (globalPhase z ψ) = outer ψ := by
  ext i j
  rw [outer_apply, outer_apply]
  simp only [globalPhase, star_mul]
  calc
    z * ψ i * (star (ψ j) * star z) =
        (z * star z) * (ψ i * star (ψ j)) := by ring
    _ = ψ i * star (ψ j) := by rw [hz]; ring

/-- Qubit relative-phase flip `Z`. -/
noncomputable def phaseZ : Operator (Fin 2) :=
  Matrix.diagonal ![1, -1]

noncomputable def phaseFlip (ρ : Operator (Fin 2)) : Operator (Fin 2) :=
  phaseZ * ρ * Matrix.conjTranspose phaseZ

/-- Two-point relative-phase twirl. -/
noncomputable def relativePhaseTwirl (ρ : Operator (Fin 2)) : Operator (Fin 2) :=
  ((1 / 2 : ℝ) : ℂ) • (ρ + phaseFlip ρ)

/-- The relative-phase twirl removes exactly the qubit off-diagonal entries. -/
theorem relativePhaseTwirl_eq_diagonal (ρ : Operator (Fin 2)) :
    relativePhaseTwirl ρ = Matrix.diagonal (Matrix.diag ρ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relativePhaseTwirl, phaseFlip, phaseZ, Matrix.mul_apply] <;> ring

/-- Normalized `|+><+|` matrix. -/
noncomputable def plusProjector : Operator (Fin 2) :=
  !![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ);
     ((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)]

/-- Positive fixture: relative-phase twirling `|+>` yields the maximally mixed qubit. -/
theorem relative_phase_twirl_plus_is_mixed :
    relativePhaseTwirl plusProjector = maximallyMixedQubit.matrix := by
  rw [relativePhaseTwirl_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusProjector, maximallyMixedQubit,
      OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.rhoMix,
      Matrix.diagonal_apply]

/-- Negative fixture: global phase cannot turn `|+><+|` into a mixed state. -/
theorem global_phase_projector_not_maximally_mixed (z : ℂ)
    (hz : z * star z = 1) :
    ((1 / 2 : ℂ) • outer (globalPhase z (fun _ : Fin 2 => 1))) ≠
      maximallyMixedQubit.matrix := by
  rw [globalPhase_projector_invariant z (fun _ : Fin 2 => 1) hz]
  intro h
  have h01 := congrArg (fun A : Operator (Fin 2) => A 0 1) h
  norm_num [outer_apply, maximallyMixedQubit,
    OperatorKO7.Meta.QuantumBoundary.DensityMatrixPOVM.rhoMix] at h01

/-! Imported NameGate and TypeGate. -/
#check @star_mul
#check @Matrix.diag
#check @globalPhase_projector_invariant
#check @relativePhaseTwirl

#check @globalPhase_projector_invariant
#print axioms globalPhase_projector_invariant
#check @relativePhaseTwirl_eq_diagonal
#print axioms relativePhaseTwirl_eq_diagonal
#check @relative_phase_twirl_plus_is_mixed
#print axioms relative_phase_twirl_plus_is_mixed
#check @global_phase_projector_not_maximally_mixed
#print axioms global_phase_projector_not_maximally_mixed


/-! ## Arbitrary finite phase ensembles and exact compression -/

open Matrix
open scoped ComplexOrder

/-- The second phase moment multiplying entry (i,j). -/
noncomputable def phaseCorrelation {Ω ι : Type} [Fintype Ω]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (i j : ι) : ℂ :=
  ∑ a, (w a : ℂ) * z a i * star (z a j)

/-- The actual average of diagonal-unitary conjugations. -/
noncomputable def phaseEnsemble {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (ρ : Operator ι) : Operator ι :=
  ∑ a, (w a : ℂ) • (Matrix.diagonal (z a) * ρ * (Matrix.diagonal (z a))ᴴ)

theorem diagonal_conjugation_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (ρ : Operator ι) (i j : ι) :
    (Matrix.diagonal z * ρ * (Matrix.diagonal z)ᴴ) i j =
      z i * ρ i j * star (z j) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem phaseEnsemble_apply {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (ρ : Operator ι) (i j : ι) :
    phaseEnsemble w z ρ i j = phaseCorrelation w z i j * ρ i j := by
  simp only [phaseEnsemble, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    diagonal_conjugation_apply, phaseCorrelation, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem phaseCorrelation_diagonal {Ω ι : Type} [Fintype Ω]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (hw : ∑ a, w a = 1)
    (hz : ∀ a i, z a i * star (z a i) = 1) (i : ι) :
    phaseCorrelation w z i i = 1 := by
  unfold phaseCorrelation
  calc
    (∑ a, (w a : ℂ) * z a i * star (z a i)) = ∑ a, (w a : ℂ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, hz a i, mul_one]
    _ = 1 := by exact_mod_cast hw

/-- Complete dephasing is exactly off-diagonal moment cancellation. -/
theorem phaseEnsemble_eq_dephase_iff {Ω ι : Type}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (hw : ∑ a, w a = 1)
    (hz : ∀ a i, z a i * star (z a i) = 1) :
    (∀ ρ : Operator ι, phaseEnsemble w z ρ = Matrix.diagonal (Matrix.diag ρ)) ↔
      ∀ i j, i ≠ j → phaseCorrelation w z i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun A : Operator ι => A i j) (h (fun _ _ => 1))
    dsimp only at he
    rw [phaseEnsemble_apply] at he
    simpa [Matrix.diagonal_apply, hij] using he
  · intro h ρ
    ext i j
    rw [phaseEnsemble_apply]
    by_cases hij : i = j
    · subst j
      simp [phaseCorrelation_diagonal w z hw hz]
    · simp [h i j hij, hij]

theorem phaseEnsemble_trace {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (hw : ∑ a, w a = 1)
    (hz : ∀ a i, z a i * star (z a i) = 1) (ρ : Operator ι) :
    Matrix.trace (phaseEnsemble w z ρ) = Matrix.trace ρ := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change phaseEnsemble w z ρ i i = ρ i i
  rw [phaseEnsemble_apply, phaseCorrelation_diagonal w z hw hz, one_mul]

/-- Nonnegative phase weights preserve positivity on the actual matrix carrier. -/
theorem phaseEnsemble_positive {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (z : Ω → ι → ℂ) (hw : ∀ a, 0 ≤ w a)
    {ρ : Operator ι} (hρ : PositiveSemidefinite ρ) :
    PositiveSemidefinite (phaseEnsemble w z ρ) := by
  unfold phaseEnsemble
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h1 h2 => h1.add h2) ?_ ?_
  · exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩
  · intro a _
    exact real_smul_positiveSemidefinite
      (hρ.mul_mul_conjTranspose_same (Matrix.diagonal (z a))) (hw a)

/-- Exact multiplicativity criterion for compression by any idempotent in any ring. -/
theorem compression_multiplicative_iff {R : Type*} [Ring R]
    (p f g : R) (hp : p * p = p) :
    (p * f * g * p = (p * f * p) * (p * g * p)) ↔
      p * f * (1 - p) * g * p = 0 := by
  have hmid : (p * f * p) * (p * g * p) = p * f * p * g * p := by
    calc
      _ = p * f * (p * p) * g * p := by noncomm_ring
      _ = _ := by rw [hp]
  have hsplit : p * f * g * p - (p * f * p) * (p * g * p) =
      p * f * (1 - p) * g * p := by
    rw [hmid]
    noncomm_ring
  constructor
  · intro h
    rw [← hsplit, h, sub_self]
  · intro h
    exact sub_eq_zero.mp (by rw [hsplit, h])

/-- Dephasing as an actual complex-linear endomorphism of the matrix space. -/
noncomputable def dephaseEnd {ι : Type} [DecidableEq ι] :
    Module.End ℂ (Operator ι) where
  toFun ρ := Matrix.diagonal (Matrix.diag ρ)
  map_add' := by
    intro ρ σ
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' := by
    intro c ρ
    ext i j
    by_cases h : i = j <;> simp [h]

theorem dephaseEnd_idempotent {ι : Type} [DecidableEq ι] :
    (dephaseEnd : Module.End ℂ (Operator ι)) * dephaseEnd = dephaseEnd := by
  ext ρ i j
  simp [dephaseEnd]

theorem classical_shadow_composition_iff {ι : Type} [DecidableEq ι]
    (f g : Module.End ℂ (Operator ι)) :
    dephaseEnd * f * g * dephaseEnd =
        (dephaseEnd * f * dephaseEnd) * (dephaseEnd * g * dephaseEnd) ↔
      dephaseEnd * f * (1 - dephaseEnd) * g * dephaseEnd = 0 :=
  compression_multiplicative_iff dephaseEnd f g dephaseEnd_idempotent

/-- Conjugation by the normalized Hadamard, written without square-root factors. -/
noncomputable def hadamardConjugation (ρ : Operator (Fin 2)) : Operator (Fin 2) :=
  let H : Operator (Fin 2) := fun i j => if i = 1 ∧ j = 1 then -1 else 1
  (1 / 2 : ℂ) • (H * ρ * H)

theorem hadamardConjugation_involution (ρ : Operator (Fin 2)) :
    hadamardConjugation (hadamardConjugation ρ) = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardConjugation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Interposed dephasing destroys composition even for a two-dimensional unitary channel. -/
theorem hadamard_dephase_composition_failure :
    dephaseEnd (hadamardConjugation (hadamardConjugation (Matrix.diagonal ![1, 0]))) ≠
      dephaseEnd (hadamardConjugation
        (dephaseEnd (hadamardConjugation (Matrix.diagonal ![1, 0])))) := by
  intro h
  have h00 := congrArg (fun A : Operator (Fin 2) => A 0 0) h
  norm_num [dephaseEnd, hadamardConjugation, Matrix.mul_apply, Fin.sum_univ_two] at h00

#check @phaseCorrelation
#print axioms phaseCorrelation
#check @phaseEnsemble
#print axioms phaseEnsemble
#check @diagonal_conjugation_apply
#print axioms diagonal_conjugation_apply
#check @phaseEnsemble_apply
#print axioms phaseEnsemble_apply
#check @phaseCorrelation_diagonal
#print axioms phaseCorrelation_diagonal
#check @phaseEnsemble_eq_dephase_iff
#print axioms phaseEnsemble_eq_dephase_iff
#check @phaseEnsemble_trace
#print axioms phaseEnsemble_trace
#check @phaseEnsemble_positive
#print axioms phaseEnsemble_positive
#check @compression_multiplicative_iff
#print axioms compression_multiplicative_iff
#check @dephaseEnd
#print axioms dephaseEnd
#check @dephaseEnd_idempotent
#print axioms dephaseEnd_idempotent
#check @classical_shadow_composition_iff
#print axioms classical_shadow_composition_iff
#check @hadamardConjugation
#print axioms hadamardConjugation
#check @hadamardConjugation_involution
#print axioms hadamardConjugation_involution
#check @hadamard_dephase_composition_failure
#print axioms hadamard_dephase_composition_failure

end OperatorKO7.Meta.UUET.Quantum
