import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite state reconstruction from population and interference reports

The carrier is an explicitly given finite-dimensional complex vector space.
The measurement values are matrix quadratic forms, not independent asserted coordinates.
This reconstructs a Hermitian state in that carrier; it does not derive the carrier or the
Born evaluation rule from an arbitrary deterministic observer.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction

/-- Matrix sesquilinear form on a finite coordinate space. -/
noncomputable def form {D : Type*} [Fintype D] (A : Matrix D D ℂ)
    (v w : D → ℂ) : ℂ := ∑ i, ∑ j, star (v i) * A i j * w j

noncomputable def basis {D : Type*} [DecidableEq D] (i : D) (k : D) : ℂ :=
  if k = i then 1 else 0

/-- Entrywise Hermitian symmetry, with no positivity assumption hidden in it. -/
def Hermitian {D : Type*} (A : Matrix D D ℂ) : Prop := ∀ i j, star (A i j) = A j i

theorem form_basis {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (i j : D) : form A (basis i) (basis j) = A i j := by
  simp [form, basis, mul_ite, ite_mul]

theorem form_add_left {D : Type*} [Fintype D] (A : Matrix D D ℂ) (u v w : D → ℂ) :
    form A (u + v) w = form A u w + form A v w := by
  simp [form, add_mul, Finset.sum_add_distrib]

theorem form_add_right {D : Type*} [Fintype D] (A : Matrix D D ℂ) (u v w : D → ℂ) :
    form A u (v + w) = form A u v + form A u w := by
  simp [form, mul_add, Finset.sum_add_distrib]

theorem form_scale_left {D : Type*} [Fintype D] (A : Matrix D D ℂ)
    (c : ℂ) (v w : D → ℂ) : form A (fun i => c * v i) w = star c * form A v w := by
  simp [form, mul_assoc, Finset.mul_sum]

theorem form_scale_right {D : Type*} [Fintype D] (A : Matrix D D ℂ)
    (c : ℂ) (v w : D → ℂ) : form A v (fun i => c * w i) = c * form A v w := by
  simp only [form, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def population {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (i : D) : ℝ := (form A (basis i) (basis i)).re

/-- The outcome on the equal-phase pair ray; distinct indices give a unit ray after division by sqrt 2. -/
noncomputable def plusReport {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (i j : D) : ℝ :=
  (form A (basis i + basis j) (basis i + basis j)).re / 2

/-- The outcome on the pair ray with relative phase I. -/
noncomputable def phaseReport {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (i j : D) : ℝ :=
  let v := basis i + fun k => Complex.I * basis j k
  (form A v v).re / 2

theorem population_entry {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (i : D) : population A i = (A i i).re := by
  rw [population, form_basis]

theorem plusReport_entry {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (hA : Hermitian A) (i j : D) :
    2 * plusReport A i j = population A i + population A j + 2 * (A i j).re := by
  simp only [plusReport, form_add_left, form_add_right, form_basis, Complex.add_re,
    population_entry]
  rw [← hA i j]
  simp only [Complex.star_def, Complex.conj_re]
  ring

theorem phaseReport_entry {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (hA : Hermitian A) (i j : D) :
    2 * phaseReport A i j = population A i + population A j - 2 * (A i j).im := by
  simp only [phaseReport, form_add_left, form_add_right, form_scale_left,
    form_scale_right, form_basis, population_entry]
  rw [← hA i j]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re]
  ring

/-- The diagonal and both interference quadratures determine every complex matrix entry. -/
theorem reports_determine_state {D : Type*} [Fintype D] [DecidableEq D]
    (A B : Matrix D D ℂ) (hA : Hermitian A) (hB : Hermitian B)
    (hp : ∀ i, population A i = population B i)
    (hr : ∀ i j, i ≠ j → plusReport A i j = plusReport B i j)
    (hi : ∀ i j, i ≠ j → phaseReport A i j = phaseReport B i j) : A = B := by
  ext i j
  apply Complex.ext
  · by_cases hij : i = j
    · subst j
      simpa only [population_entry] using hp i
    · have ha := plusReport_entry A hA i j
      have hb := plusReport_entry B hB i j
      rw [hr i j hij, hp i, hp j] at ha
      linarith
  · by_cases hij : i = j
    · subst j
      have ha := congrArg Complex.im (hA i i)
      have hb := congrArg Complex.im (hB i i)
      simp only [Complex.star_def, Complex.conj_im] at ha hb
      linarith
    · have ha := phaseReport_entry A hA i j
      have hb := phaseReport_entry B hB i j
      rw [hi i j hij, hp i, hp j] at ha
      linarith

/-- A normalized positive state uses the same quadratic form as the report functions. -/
structure State (D : Type*) [Fintype D] [DecidableEq D] where
  matrix : Matrix D D ℂ
  hermitian : Hermitian matrix
  positive : ∀ v, 0 ≤ (form matrix v v).re
  trace_one : ∑ i, population matrix i = 1

theorem state_population_nonneg {D : Type*} [Fintype D] [DecidableEq D]
    (A : State D) (i : D) : 0 ≤ population A.matrix i := A.positive (basis i)

theorem state_plus_nonneg {D : Type*} [Fintype D] [DecidableEq D]
    (A : State D) (i j : D) : 0 ≤ plusReport A.matrix i j := by
  exact div_nonneg (A.positive (basis i + basis j)) (by norm_num)

theorem state_phase_nonneg {D : Type*} [Fintype D] [DecidableEq D]
    (A : State D) (i j : D) : 0 ≤ phaseReport A.matrix i j := by
  exact div_nonneg (A.positive _) (by norm_num)

/-- Agreement of the report family is equivalent to equality of the represented state matrix. -/
theorem state_equality_iff_reports {D : Type*} [Fintype D] [DecidableEq D]
    (A B : State D) : A.matrix = B.matrix ↔
      (∀ i, population A.matrix i = population B.matrix i) ∧
      (∀ i j, i ≠ j → plusReport A.matrix i j = plusReport B.matrix i j) ∧
      (∀ i j, i ≠ j → phaseReport A.matrix i j = phaseReport B.matrix i j) := by
  constructor
  · intro h
    rw [h]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · rintro ⟨hp, hr, hi⟩
    exact reports_determine_state A.matrix B.matrix A.hermitian B.hermitian hp hr hi

/-- Nonnegative populations do not by themselves determine off-diagonal phase information. -/
noncomputable def phaseMatrix (positivePhase : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 1 / 2 else if positivePhase then 1 / 2 else -(1 / 2)

theorem phaseMatrix_hermitian (b : Bool) : Hermitian (phaseMatrix b) := by
  intro i j
  fin_cases i <;> fin_cases j <;> cases b <;> norm_num [phaseMatrix]

/-- These are genuine positive trace-one matrices: their forms are squared absolute values. -/
theorem phaseMatrix_form (b : Bool) (v : Fin 2 → ℂ) :
    (form (phaseMatrix b) v v).re =
      ((v 0).re + (if b then (v 1).re else -(v 1).re)) ^ 2 / 2 +
      ((v 0).im + (if b then (v 1).im else -(v 1).im)) ^ 2 / 2 := by
  cases b <;>
    simp [form, Fin.sum_univ_two, phaseMatrix, Complex.mul_re, Complex.mul_im] <;> ring

noncomputable def phaseState (b : Bool) : State (Fin 2) where
  matrix := phaseMatrix b
  hermitian := phaseMatrix_hermitian b
  positive := by
    intro v
    rw [phaseMatrix_form]
    positivity
  trace_one := by
    simp [population_entry, phaseMatrix]

theorem populations_do_not_determine_state :
    (∀ i, population (phaseState true).matrix i = population (phaseState false).matrix i) ∧
    (phaseState true).matrix ≠ (phaseState false).matrix ∧
    plusReport (phaseState true).matrix 0 1 = 1 ∧
    plusReport (phaseState false).matrix 0 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [phaseState, population_entry, phaseMatrix]
  · intro h
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1).re) h
    norm_num [phaseState, phaseMatrix] at he
  · have h := plusReport_entry (phaseState true).matrix (phaseState true).hermitian 0 1
    norm_num [phaseState, population_entry, phaseMatrix] at h
    exact h
  · have h := plusReport_entry (phaseState false).matrix (phaseState false).hermitian 0 1
    norm_num [phaseState, population_entry, phaseMatrix] at h
    exact h

/-- Entry-by-entry reconstruction uses only the finite report data. -/
noncomputable def reconstruct {D : Type*} [DecidableEq D]
    (p : D → ℝ) (r s : D → D → ℝ) : Matrix D D ℂ := fun i j =>
  if i = j then (p i : ℂ) else
    ⟨r i j - (p i + p j) / 2, (p i + p j) / 2 - s i j⟩

/-- The report map has an explicit left inverse on all Hermitian matrices. -/
theorem reconstruct_reports {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (hA : Hermitian A) :
    reconstruct (population A) (plusReport A) (phaseReport A) = A := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext
    · simp [reconstruct, population_entry]
    · have h := congrArg Complex.im (hA i i)
      simp only [Complex.star_def, Complex.conj_im] at h
      have hz : (A i i).im = 0 := by linarith
      simp [reconstruct, hz]
  · apply Complex.ext
    · change (if i = j then (population A i : ℂ) else
        ⟨plusReport A i j - (population A i + population A j) / 2,
         (population A i + population A j) / 2 - phaseReport A i j⟩).re = (A i j).re
      rw [if_neg hij]
      change plusReport A i j - (population A i + population A j) / 2 = (A i j).re
      linarith [plusReport_entry A hA i j]
    · change (if i = j then (population A i : ℂ) else
        ⟨plusReport A i j - (population A i + population A j) / 2,
         (population A i + population A j) / 2 - phaseReport A i j⟩).im = (A i j).im
      rw [if_neg hij]
      change (population A i + population A j) / 2 - phaseReport A i j = (A i j).im
      linarith [phaseReport_entry A hA i j]

end OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction
