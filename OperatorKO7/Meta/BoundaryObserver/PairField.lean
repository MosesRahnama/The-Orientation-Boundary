import OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction
import OperatorKO7.Meta.BoundaryObserver.PairQubit
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Kronecker ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver.PairField

open QuantumReconstruction
noncomputable section

/-- M6.10(i), exact source-bound real interference statement. -/
def RealInterferenceGoal : Prop :=
  ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
    QuantumReconstruction.Hermitian A → QuantumReconstruction.Hermitian B →
    (∀ i j, (A i j).im = 0) → (∀ i j, (B i j).im = 0) →
    (∀ i, QuantumReconstruction.population A i = QuantumReconstruction.population B i) →
    QuantumReconstruction.plusReport A 0 1 = QuantumReconstruction.plusReport B 0 1 → A = B

/-- M6.10(ii), exact source-bound complex phase separation statement. -/
def ComplexNeedsSecondReportGoal : Prop :=
  ∃ A B : Matrix (Fin 2) (Fin 2) ℂ,
    QuantumReconstruction.Hermitian A ∧ QuantumReconstruction.Hermitian B ∧
    (∀ i, QuantumReconstruction.population A i = QuantumReconstruction.population B i) ∧
    QuantumReconstruction.plusReport A 0 1 = QuantumReconstruction.plusReport B 0 1 ∧
    QuantumReconstruction.phaseReport A 0 1 ≠ QuantumReconstruction.phaseReport B 0 1

/-- M6.10(iv), exact source-bound classical purification obstruction. -/
def ClassicalPurificationFailsGoal : Prop :=
  ¬ ∃ (Y : Type) (_ : Fintype Y) (m : Bool × Y → ℝ),
    (∀ z, 0 ≤ m z) ∧ (∃ z₀, m z₀ = 1 ∧ ∀ z, z ≠ z₀ → m z = 0) ∧
      ∀ b, ∑ y, m (b, y) = 1 / 2

/-- Equal populations and one plus report determine a real Hermitian qubit. -/
theorem realInterferenceGoal : RealInterferenceGoal := by
  intro A B hA hB hiA hiB hp hplus
  have h00 : A 0 0 = B 0 0 := by
    apply Complex.ext
    · simpa only [QuantumReconstruction.population_entry] using hp 0
    · exact (hiA 0 0).trans (hiB 0 0).symm
  have h11 : A 1 1 = B 1 1 := by
    apply Complex.ext
    · simpa only [QuantumReconstruction.population_entry] using hp 1
    · exact (hiA 1 1).trans (hiB 1 1).symm
  have h01Re : (A 0 1).re = (B 0 1).re := by
    have ha := QuantumReconstruction.plusReport_entry A hA 0 1
    have hb := QuantumReconstruction.plusReport_entry B hB 0 1
    rw [hplus, hp 0, hp 1] at ha
    linarith
  have h01 : A 0 1 = B 0 1 := by
    apply Complex.ext
    · exact h01Re
    · exact (hiA 0 1).trans (hiB 0 1).symm
  have h10 : A 1 0 = B 1 0 := by
    calc
      A 1 0 = star (A 0 1) := (hA 0 1).symm
      _ = star (B 0 1) := congrArg star h01
      _ = B 1 0 := hB 0 1
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

private def phasePlus : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 1 / 2
    else if i = 0 then Complex.I / 2 else -Complex.I / 2

private def phaseMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 1 / 2
    else if i = 0 then -Complex.I / 2 else Complex.I / 2

private theorem phasePlus_hermitian : QuantumReconstruction.Hermitian phasePlus := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phasePlus, Complex.star_def, Complex.conj_I]

private theorem phaseMinus_hermitian : QuantumReconstruction.Hermitian phaseMinus := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseMinus, Complex.star_def, Complex.conj_I]

/-- Opposite complex phases have equal populations and plus report,
but unequal phase report. -/
theorem complexNeedsSecondReportGoal : ComplexNeedsSecondReportGoal := by
  refine ⟨phasePlus, phaseMinus, phasePlus_hermitian, phaseMinus_hermitian, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [QuantumReconstruction.population_entry, phasePlus, phaseMinus]
  · have ha := QuantumReconstruction.plusReport_entry phasePlus phasePlus_hermitian 0 1
    have hb := QuantumReconstruction.plusReport_entry phaseMinus phaseMinus_hermitian 0 1
    norm_num [QuantumReconstruction.population_entry, phasePlus, phaseMinus] at ha hb
    linarith
  · intro heq
    have ha := QuantumReconstruction.phaseReport_entry phasePlus phasePlus_hermitian 0 1
    have hb := QuantumReconstruction.phaseReport_entry phaseMinus phaseMinus_hermitian 0 1
    rw [heq] at ha
    norm_num [QuantumReconstruction.population_entry, phasePlus, phaseMinus] at ha hb
    linarith

/-- A classical point mass cannot have a fair-bit marginal. -/
theorem classicalPurificationFailsGoal : ClassicalPurificationFailsGoal := by
  rintro ⟨Y, fint, m, _hmpos, ⟨z, hz, hzero⟩, hhalf⟩
  letI : Fintype Y := fint
  classical
  have hsum : (∑ y : Y, m (z.1, y)) = 1 := by
    calc
      (∑ y : Y, m (z.1, y)) = m (z.1, z.2) := by
        apply Finset.sum_eq_single z.2
        · intro y _ hy
          apply hzero
          intro heq
          exact hy (congrArg Prod.snd heq)
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ z.2))
      _ = m z := by simp only [Prod.mk.eta]
      _ = 1 := hz
  have hfix := hhalf z.1
  rw [hsum] at hfix
  norm_num at hfix


/-- M6.10(v): agreement on all Hermitian local product tests determines
the entire complex two-pair matrix, without positivity assumptions. -/
def ComplexLocalTomographyGoal : Prop :=
  ∀ ρ σ : Matrix (Bool × Bool) (Bool × Bool) ℂ,
    (∀ A B : Matrix Bool Bool ℂ, A.IsHermitian → B.IsHermitian →
      (ρ * (A ⊗ₖ B)).trace = (σ * (A ⊗ₖ B)).trace) → ρ = σ

private def hermPlus (M : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  M + M.conjTranspose

private def hermPhase (M : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  ((Complex.I : ℂ) • M) + (((Complex.I : ℂ) • M).conjTranspose)

private theorem hermPlus_selfAdjoint (M : Matrix Bool Bool ℂ) :
    (hermPlus M).IsHermitian :=
  Matrix.isHermitian_add_transpose_self M

private theorem hermPhase_selfAdjoint (M : Matrix Bool Bool ℂ) :
    (hermPhase M).IsHermitian :=
  Matrix.isHermitian_add_transpose_self ((Complex.I : ℂ) • M)

/-- An arbitrary complex local matrix is a complex linear combination
of two Hermitian matrices. -/
private theorem hermitian_decomposition (M : Matrix Bool Bool ℂ) :
    M = (1 / 2 : ℂ) • hermPlus M + (-Complex.I / 2 : ℂ) • hermPhase M := by
  ext i j
  change M i j =
    (1 / 2 : ℂ) * (M i j + star (M j i)) +
      (-Complex.I / 2 : ℂ) *
        ((Complex.I : ℂ) * M i j + star ((Complex.I : ℂ) * M j i))
  rw [star_mul']
  simp only [Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem trace_mul_matrix_single
    (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (a b : Bool × Bool) :
    (M * Matrix.single b a (1 : ℂ)).trace = M a b := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single,
      Fintype.sum_prod_type]

/-- Hermitian product tests span the complex dual, and matrix units
separate all sixteen entries of an arbitrary two-pair matrix. -/
theorem complexLocalTomographyGoal : ComplexLocalTomographyGoal := by
  intro ρ σ h
  let D : Matrix (Bool × Bool) (Bool × Bool) ℂ := ρ - σ
  let F : Matrix Bool Bool ℂ → Matrix Bool Bool ℂ → ℂ :=
    fun A B => (D * (A ⊗ₖ B)).trace
  have haddL (A A' B : Matrix Bool Bool ℂ) :
      F (A + A') B = F A B + F A' B := by
    simp only [F, Matrix.add_kronecker, mul_add, Matrix.trace_add]
  have haddR (A B B' : Matrix Bool Bool ℂ) :
      F A (B + B') = F A B + F A B' := by
    simp only [F, Matrix.kronecker_add, mul_add, Matrix.trace_add]
  have hsmulL (c : ℂ) (A B : Matrix Bool Bool ℂ) :
      F (c • A) B = c * F A B := by
    simp only [F, Matrix.smul_kronecker, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  have hsmulR (c : ℂ) (A B : Matrix Bool Bool ℂ) :
      F A (c • B) = c * F A B := by
    simp only [F, Matrix.kronecker_smul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  have hherm (A B : Matrix Bool Bool ℂ) (ha : A.IsHermitian)
      (hb : B.IsHermitian) : F A B = 0 := by
    dsimp [F, D]
    rw [sub_mul, Matrix.trace_sub]
    exact sub_eq_zero.mpr (h A B ha hb)
  have hright (A B : Matrix Bool Bool ℂ) (ha : A.IsHermitian) :
      F A B = 0 := by
    conv_lhs => rw [hermitian_decomposition B]
    rw [haddR, hsmulR, hsmulR,
      hherm A (hermPlus B) ha (hermPlus_selfAdjoint B),
      hherm A (hermPhase B) ha (hermPhase_selfAdjoint B)]
    simp
  have hall (A B : Matrix Bool Bool ℂ) : F A B = 0 := by
    conv_lhs => rw [hermitian_decomposition A]
    rw [haddL, hsmulL, hsmulL,
      hright (hermPlus A) B (hermPlus_selfAdjoint A),
      hright (hermPhase A) B (hermPhase_selfAdjoint A)]
    simp
  have hD : D = 0 := by
    ext i j
    rcases i with ⟨a, b⟩
    rcases j with ⟨c, d⟩
    have ht := hall (Matrix.single c a (1 : ℂ))
      (Matrix.single d b (1 : ℂ))
    change (D * (Matrix.single c a (1 : ℂ) ⊗ₖ
      Matrix.single d b (1 : ℂ))).trace = 0 at ht
    rw [Matrix.single_kronecker_single, one_mul,
      trace_mul_matrix_single] at ht
    exact ht
  exact sub_eq_zero.mp hD

/-- M6.10(vi): over the real numbers two different joint states of two pairs agree on every
product test. -/
def RealLocalTomographyFailsGoal : Prop :=
  ∃ ρ σ : Matrix (Bool × Bool) (Bool × Bool) ℝ, ρ ≠ σ ∧ ρ.PosSemidef ∧ σ.PosSemidef ∧
    ρ.trace = 1 ∧ σ.trace = 1 ∧
    ∀ A B : Matrix Bool Bool ℝ, A.transpose = A → B.transpose = B →
      (ρ * (A ⊗ₖ B)).trace = (σ * (A ⊗ₖ B)).trace

/-- The real rotation J = [[0, 1], [-1, 0]] on the two labels. -/
private def realJ (a b : Bool) : ℝ := if a = b then 0 else if a then -1 else 1

/-- The maximally mixed real joint state of two pairs. -/
private def realMixed : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun x y => if x = y then 1 / 4 else 0

/-- The maximally mixed state shifted by one eighth of J ⊗ J. -/
private def realShifted : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun x y => (if x = y then 1 / 4 else 0) + realJ x.1 y.1 * realJ x.2 y.2 / 8

private theorem realMixed_eq_diagonal :
    realMixed = Matrix.diagonal (fun _ : Bool × Bool => (1 / 4 : ℝ)) := by
  ext x y
  simp [realMixed, Matrix.diagonal_apply]

/-- G37. Over the real numbers two different joint states of two pairs agree on every product
of symmetric local tests: the difference J ⊗ J / 8 is invisible to them. -/
theorem realLocalTomographyFailsGoal : RealLocalTomographyFailsGoal := by
  refine ⟨realMixed, realShifted, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun (congrFun h (false, false)) (true, true)
    simp [realMixed, realShifted, realJ] at h1
  · rw [realMixed_eq_diagonal]
    exact Matrix.PosSemidef.diagonal (fun _ => by norm_num)
  · constructor
    · ext x y
      rcases x with ⟨a, b⟩
      rcases y with ⟨c, d⟩
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [realShifted, realJ, Matrix.conjTranspose_apply]
    · intro v
      simp only [star_trivial, dotProduct, Matrix.mulVec, realShifted, realJ,
        Fintype.sum_prod_type, Fintype.sum_bool]
      norm_num
      nlinarith [sq_nonneg (v (false, false) + v (true, true)),
        sq_nonneg (v (false, true) - v (true, false)),
        sq_nonneg (v (false, false)), sq_nonneg (v (true, true)),
        sq_nonneg (v (false, true)), sq_nonneg (v (true, false))]
  · simp [Matrix.trace, realMixed]
  · simp [Matrix.trace, realShifted, realJ]
  · intro A B hA hB
    have hA01 : A true false = A false true := by
      have := congrFun (congrFun hA false) true
      simpa [Matrix.transpose_apply] using this
    have hB01 : B true false = B false true := by
      have := congrFun (congrFun hB false) true
      simpa [Matrix.transpose_apply] using this
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
      realMixed, realShifted, realJ, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    rw [hA01, hB01]
    ring

open PairQubit in
/-- M6.10: the selection of the complex field at the pair. -/
def FieldSelectionGoal : Prop :=
  RealInterferenceGoal ∧ ComplexNeedsSecondReportGoal ∧ QuantumPurificationGoal ∧
    ClassicalPurificationFailsGoal ∧ ComplexLocalTomographyGoal ∧
    RealLocalTomographyFailsGoal ∧ FieldDimensionGoal

/-- G39. The seven parts of the field comparison at the pair hold together. -/
theorem fieldSelectionGoal : FieldSelectionGoal :=
  ⟨realInterferenceGoal, complexNeedsSecondReportGoal, PairQubit.quantum_purification,
    classicalPurificationFailsGoal, complexLocalTomographyGoal, realLocalTomographyFailsGoal,
    PairQubit.field_dimension⟩

end
end OperatorKO7.Meta.BoundaryObserver.PairField
