import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
The manuscript label cor:gibbs-record-heat states that entropy-preserving
unitary record formation in a finite Gibbs memory satisfies beta Q = I + D,
I <= beta Q, and equality precisely for an unchanged reservoir state.

The file uses spectral coordinates for finite complex density matrices.
The initial system and Hamiltonian are expressed in their eigenbases;
the final marginal eigenbases are arbitrary, so no commutativity assumption
is imposed. An evolution includes an actual joint unitary and matrix
partial-trace equations. Entropy and relative entropy use their spectral
formulas, with zero eigenvalues allowed in the final state.
The result is restricted to finite dimensions because the entropy proof
uses finite spectral sums.
The pure-state exclusion requires dimension at least two; dimension one
is an explicit counterexample. Finite index types retain product indices.
-/

noncomputable section
open scoped BigOperators

namespace GibbsRecordHeat

@[ext]
structure Probability (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

instance {ι : Type*} [Fintype ι] :
    CoeFun (Probability ι) (fun _ => ι → ℝ) := ⟨Probability.mass⟩

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def entropy (p : Probability ι) : ℝ := -∑ i, p i * Real.log (p i)

def tensor (p : Probability ι) (q : Probability κ) : Probability (ι × κ) where
  mass x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg x.1) (q.nonneg x.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

lemma xlog_mul (a b : ℝ) :
    a * b * Real.log (a * b) =
      (a * Real.log a) * b + a * (b * Real.log b) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

lemma entropy_tensor (p : Probability ι) (q : Probability κ) :
    entropy (tensor p q) = entropy p + entropy q := by
  change -(∑ x : ι × κ, p x.1 * q x.2 * Real.log (p x.1 * q x.2)) =
    -(∑ i, p i * Real.log (p i)) + -(∑ j, q j * Real.log (q j))
  rw [Fintype.sum_prod_type]
  simp_rw [xlog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, p.total, q.total, mul_one, one_mul]
  ring

def partition (β : ℝ) (E : ι → ℝ) : ℝ := ∑ i, Real.exp (-β * E i)

lemma partition_pos [Nonempty ι] (β : ℝ) (E : ι → ℝ) :
    0 < partition β E :=
  Finset.sum_pos (fun i _ => Real.exp_pos (-β * E i)) Finset.univ_nonempty

def gibbs [Nonempty ι] (β : ℝ) (E : ι → ℝ) : Probability ι where
  mass i := Real.exp (-β * E i) / partition β E
  nonneg i := (div_pos (Real.exp_pos _) (partition_pos β E)).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (partition_pos β E))

lemma gibbs_pos [Nonempty ι] (β : ℝ) (E : ι → ℝ) (i : ι) :
    0 < gibbs β E i :=
  div_pos (Real.exp_pos _) (partition_pos β E)

lemma log_gibbs [Nonempty ι] (β : ℝ) (E : ι → ℝ) (i : ι) :
    Real.log (gibbs β E i) = -β * E i - Real.log (partition β E) := by
  change Real.log (Real.exp (-β * E i) / partition β E) = _
  rw [Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (partition_pos β E)), Real.log_exp]

variable [DecidableEq ι] [DecidableEq κ]

abbrev Unitary (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Matrix.unitaryGroup ι ℂ

def density (U : Unitary ι) (p : Probability ι) : Matrix ι ι ℂ :=
  U.1 * Matrix.diagonal (fun i => (p i : ℂ)) * star U.1

def overlap (U : Unitary ι) (i j : ι) : ℝ := Complex.normSq (U.1 i j)

lemma overlap_nonneg (U : Unitary ι) (i j : ι) : 0 ≤ overlap U i j :=
  Complex.normSq_nonneg _

lemma overlap_row (U : Unitary ι) (i : ι) : ∑ j, overlap U i j = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) U.2.2
  simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re, overlap] using h

lemma overlap_col (U : Unitary ι) (j : ι) : ∑ i, overlap U i j = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => (A j j).re) U.2.1
  simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re, overlap] using h

lemma sum_rows (U : Unitary ι) (f : ι → ℝ) :
    (∑ i, ∑ j, overlap U i j * f i) = ∑ i, f i := by
  simp_rw [← Finset.sum_mul, overlap_row, one_mul]

lemma sum_columns (U : Unitary ι) (f : ι → ℝ) :
    (∑ i, ∑ j, overlap U i j * f j) = ∑ j, f j := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, overlap_col, one_mul]

def diagonalMass (p : Probability ι) (U : Unitary ι) (i : ι) : ℝ :=
  ∑ j, overlap U i j * p j

lemma diagonalMass_total (p : Probability ι) (U : Unitary ι) :
    ∑ i, diagonalMass p U i = 1 := by
  unfold diagonalMass
  rw [sum_columns, p.total]

lemma density_diagonal (p : Probability ι) (U : Unitary ι) (i : ι) :
    (density U p i i).re = diagonalMass p U i := by
  rw [density, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Complex.re_sum]
  unfold diagonalMass
  apply Finset.sum_congr rfl
  intro j _
  simp only [overlap, Complex.star_def, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma density_eq_diagonal_iff (p g : Probability ι) (U : Unitary ι) :
    density U p = Matrix.diagonal (fun i => (g i : ℂ)) ↔
      ∀ i j, U.1 i j ≠ 0 → p j = g i := by
  constructor
  · intro h i j hij
    have hm := congrArg (fun A : Matrix ι ι ℂ => A * U.1) h
    have hc : U.1 * Matrix.diagonal (fun k => (p k : ℂ)) =
        Matrix.diagonal (fun k => (g k : ℂ)) * U.1 := by
      simpa only [density, mul_assoc, U.2.1, mul_one] using hm
    have he := congrArg (fun A : Matrix ι ι ℂ => A i j) hc
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    apply Complex.ofReal_injective
    apply mul_left_cancel₀ hij
    simpa only [mul_comm] using he
  · intro h
    have hc : U.1 * Matrix.diagonal (fun k => (p k : ℂ)) =
        Matrix.diagonal (fun k => (g k : ℂ)) * U.1 := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : U.1 i j = 0
      · simp [hij]
      · rw [h i j hij]
        exact mul_comm _ _
    unfold density
    rw [hc, mul_assoc, U.2.2, mul_one]

def logGap (a b : ℝ) : ℝ := a * (Real.log a - Real.log b) - a + b

lemma logGap_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≠ b) :
    0 < logGap a b := by
  by_cases ha0 : a = 0
  · subst a
    simpa [logGap] using hb
  have ha' : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
  have hratio : b / a ≠ 1 := by
    intro h
    apply hab
    field_simp [ha0] at h
    linarith
  have h := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (div_pos hb ha') hratio) ha'
  rw [Real.log_div (ne_of_gt hb) ha0] at h
  have hc : a * (b / a - 1) = b - a := by
    field_simp [ha0]
  rw [hc] at h
  unfold logGap
  nlinarith

lemma logGap_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ logGap a b := by
  by_cases h : a = b
  · simp [logGap, h]
  · exact (logGap_pos ha hb h).le

lemma logGap_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    logGap a b = 0 ↔ a = b := by
  constructor
  · intro hz
    by_contra h
    have hp := logGap_pos ha hb h
    linarith
  · intro h
    simp [logGap, h]

/-- The spectral formula for quantum relative entropy against diagonal g. -/
def relativeEntropy (p : Probability ι) (U : Unitary ι) (g : Probability ι) : ℝ :=
  ∑ i, ∑ j, overlap U i j * (p j * (Real.log (p j) - Real.log (g i)))

lemma relativeEntropy_gap (p : Probability ι) (U : Unitary ι) (g : Probability ι) :
    relativeEntropy p U g = ∑ i, ∑ j, overlap U i j * logGap (p j) (g i) := by
  have h : (∑ i, ∑ j, overlap U i j * logGap (p j) (g i)) =
      relativeEntropy p U g - (∑ i, ∑ j, overlap U i j * p j) +
        (∑ i, ∑ j, overlap U i j * g i) := by
    simp only [logGap, relativeEntropy, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_columns, sum_rows, p.total, g.total] at h
  linarith

lemma relativeEntropy_nonneg (p : Probability ι) (U : Unitary ι)
    (g : Probability ι) (hg : ∀ i, 0 < g i) : 0 ≤ relativeEntropy p U g := by
  rw [relativeEntropy_gap]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (overlap_nonneg U i j) (logGap_nonneg (p.nonneg j) (hg i))))

omit [DecidableEq ι] [DecidableEq κ] in
lemma double_sum_zero (f : ι → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    (∑ i, ∑ j, f i j) = 0 ↔ ∀ i j, f i j = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => hf i j))]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro i
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset κ))
      (f := fun j : κ => f i j)
      (fun j _ => hf i j))

lemma relativeEntropy_zero (p : Probability ι) (U : Unitary ι)
    (g : Probability ι) (hg : ∀ i, 0 < g i) :
    relativeEntropy p U g = 0 ↔
      density U p = Matrix.diagonal (fun i => (g i : ℂ)) := by
  classical
  rw [density_eq_diagonal_iff, relativeEntropy_gap, double_sum_zero _
    (fun i j => mul_nonneg (overlap_nonneg U i j)
      (logGap_nonneg (p.nonneg j) (hg i)))]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  change Complex.normSq (U.1 i j) * logGap (p j) (g i) = 0 ↔ _
  rw [mul_eq_zero, Complex.normSq_eq_zero, logGap_eq_zero (p.nonneg j) (hg i)]
  tauto

lemma relativeEntropy_expand (p : Probability ι) (U : Unitary ι)
    (g : Probability ι) :
    relativeEntropy p U g =
      -entropy p - ∑ i, diagonalMass p U i * Real.log (g i) := by
  simp only [relativeEntropy, mul_sub, Finset.sum_sub_distrib]
  rw [sum_columns]
  unfold entropy
  rw [neg_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The energy is the real trace of the diagonal Hamiltonian times the state. -/
def energy (E : ι → ℝ) (p : Probability ι) (U : Unitary ι) : ℝ :=
  ∑ i, E i * (density U p i i).re

lemma energy_trace (E : ι → ℝ) (p : Probability ι) (U : Unitary ι) :
    energy E p U =
      (Matrix.trace (Matrix.diagonal (fun i => (E i : ℂ)) * density U p)).re := by
  simp only [energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma energy_eq (E : ι → ℝ) (p : Probability ι) (U : Unitary ι) :
    energy E p U = ∑ i, E i * diagonalMass p U i := by
  simp only [energy, density_diagonal]

def heat (E : ι → ℝ) (p : Probability ι) (U : Unitary ι)
    (g : Probability ι) : ℝ := energy E p U - energy E g 1

lemma relativeEntropy_gibbs [Nonempty ι] (p : Probability ι) (U : Unitary ι)
    (β : ℝ) (E : ι → ℝ) :
    relativeEntropy p U (gibbs β E) =
      -entropy p + β * energy E p U + Real.log (partition β E) := by
  rw [relativeEntropy_expand]
  have h : (∑ i, diagonalMass p U i * Real.log (gibbs β E i)) =
      -β * energy E p U - Real.log (partition β E) := by
    calc
      _ = ∑ i, ((-β) * (E i * diagonalMass p U i) -
          diagonalMass p U i * Real.log (partition β E)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [log_gibbs]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          diagonalMass_total, one_mul, energy_eq]
  rw [h]
  ring

lemma heat_identity [Nonempty ι] (p : Probability ι) (U : Unitary ι)
    (β : ℝ) (E : ι → ℝ) :
    β * heat E p U (gibbs β E) =
      entropy p - entropy (gibbs β E) + relativeEntropy p U (gibbs β E) := by
  have hp := relativeEntropy_gibbs p U β E
  have hg := relativeEntropy_gibbs (gibbs β E) (1 : Unitary ι) β E
  have hz : relativeEntropy (gibbs β E) (1 : Unitary ι) (gibbs β E) = 0 :=
    (relativeEntropy_zero _ _ _ (gibbs_pos β E)).2 (by simp [density])
  rw [hz] at hg
  unfold heat
  nlinarith

/-- The joint state is a unitary conjugate of the initial product spectrum. -/
structure Evolution (p : Probability ι) (g : Probability κ) where
  jointUnitary : Unitary (ι × κ)
  systemProb : Probability ι
  systemUnitary : Unitary ι
  reservoirProb : Probability κ
  reservoirUnitary : Unitary κ
  systemMarginal : density systemUnitary systemProb =
    fun i j => ∑ r, density jointUnitary (tensor p g) (i, r) (j, r)
  reservoirMarginal : density reservoirUnitary reservoirProb =
    fun r s => ∑ i, density jointUnitary (tensor p g) (i, r) (i, s)

def mutualInformation {p : Probability ι} {g : Probability κ}
    (e : Evolution p g) : ℝ :=
  entropy e.systemProb + entropy e.reservoirProb - entropy (tensor p g)

def IsPure (p : Probability ι) : Prop := ∃ i, p i = 1

omit [DecidableEq ι] in
lemma gibbs_not_pure [Nontrivial ι] (β : ℝ) (E : ι → ℝ) :
    ¬ IsPure (gibbs β E) := by
  rintro ⟨i, hi⟩
  obtain ⟨j, hji⟩ := exists_ne i
  have hle := Finset.add_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset ι)) => (gibbs β E).nonneg k)
    (Finset.mem_univ i) (Finset.mem_univ j) hji.symm
  rw [(gibbs β E).total, hi] at hle
  have hp := gibbs_pos β E j
  linarith

lemma gibbs_dimension_one_is_pure (β : ℝ) (E : Fin 1 → ℝ) :
    IsPure (gibbs β E) := by
  refine ⟨0, ?_⟩
  simpa [Fin.sum_univ_succ] using (gibbs β E).total

lemma zero_hamiltonian_heat (p g : Probability ι) (U : Unitary ι) :
    heat (fun _ => 0) p U g = 0 := by
  simp [heat, energy]

end GibbsRecordHeat

open GibbsRecordHeat

theorem gibbs_record_heat
    {n m : ℕ} [NeZero m]
    (β : ℝ) (hβ : 0 < β) (E : Fin m → ℝ) (p : Probability (Fin n))
    (e : Evolution p (gibbs β E)) (hS : entropy e.systemProb = entropy p) :
    β * heat E e.reservoirProb e.reservoirUnitary (gibbs β E) =
        mutualInformation e + relativeEntropy e.reservoirProb e.reservoirUnitary (gibbs β E) ∧
    mutualInformation e ≤ β * heat E e.reservoirProb e.reservoirUnitary (gibbs β E) ∧
    (β * heat E e.reservoirProb e.reservoirUnitary (gibbs β E) = mutualInformation e ↔
      density e.reservoirUnitary e.reservoirProb =
        Matrix.diagonal (fun i => (gibbs β E i : ℂ))) ∧
    mutualInformation e / β ≤ heat E e.reservoirProb e.reservoirUnitary (gibbs β E) := by
  have hI : mutualInformation e = entropy e.reservoirProb - entropy (gibbs β E) := by
    unfold mutualInformation
    rw [entropy_tensor, hS]
    ring
  have hid := heat_identity e.reservoirProb e.reservoirUnitary β E
  rw [← hI] at hid
  have hn := relativeEntropy_nonneg e.reservoirProb e.reservoirUnitary
    (gibbs β E) (gibbs_pos β E)
  have hz := relativeEntropy_zero e.reservoirProb e.reservoirUnitary
    (gibbs β E) (gibbs_pos β E)
  refine ⟨hid, by linarith, ?_, ?_⟩
  · rw [← hz, hid]
    constructor <;> intro h <;> linarith
  · apply (div_le_iff₀ hβ).2
    nlinarith

theorem gibbs_record_heat_bits
    {n m : ℕ} [NeZero m]
    (β kB T bits : ℝ) (hk : 0 < kB) (hT : 0 < T)
    (hβ : β = (kB * T)⁻¹) (E : Fin m → ℝ) (p : Probability (Fin n))
    (e : Evolution p (gibbs β E)) (hS : entropy e.systemProb = entropy p)
    (hbits : mutualInformation e = bits * Real.log 2) :
    kB * T * Real.log 2 * bits ≤
      heat E e.reservoirProb e.reservoirUnitary (gibbs β E) := by
  have hb : 0 < β := by rw [hβ]; exact inv_pos.mpr (mul_pos hk hT)
  have h := (gibbs_record_heat β hb E p e hS).2.2.2
  calc
    kB * T * Real.log 2 * bits = mutualInformation e / β := by
      rw [hbits, hβ, div_inv_eq_mul]
      ring
    _ ≤ _ := h

namespace GibbsRecordHeat

def fair : Probability (Fin 2) where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_succ]

def pureZero : Probability (Fin 2) where
  mass i := if i = 0 then 1 else 0
  nonneg i := by split <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

lemma fair_entropy : entropy fair = Real.log 2 := by
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  norm_num [entropy, fair, Fin.sum_univ_succ, hl] ; ring

lemma zero_hamiltonian_gibbs (β : ℝ) :
    gibbs β (fun _ : Fin 2 => 0) = fair := by
  ext i
  norm_num [gibbs, partition, fair, Fin.sum_univ_succ]

def cnotAction (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (x.1, x.1 + x.2)

def cnotMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x = cnotAction y then 1 else 0

def cnotUnitary : Unitary (Fin 2 × Fin 2) :=
  ⟨cnotMatrix, by
    have htwo : (1 : Fin 2) + 1 = 0 := by decide
    constructor <;> apply Matrix.ext <;> intro x y <;>
      rcases x with ⟨a, b⟩ <;> rcases y with ⟨c, d⟩ <;>
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [cnotMatrix, cnotAction, Matrix.mul_apply, Matrix.star_apply,
        Fintype.sum_prod_type, Fin.sum_univ_succ, htwo]⟩

lemma cnot_fair_joint :
    density cnotUnitary (tensor fair fair) =
      Matrix.diagonal (fun _ => (1 / 4 : ℂ)) := by
  have htwo : (1 : Fin 2) + 1 = 0 := by decide
  apply Matrix.ext
  intro x y
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [density, cnotUnitary, cnotMatrix, cnotAction, tensor, fair,
      Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, htwo]

def fairEvolution : Evolution fair fair where
  jointUnitary := cnotUnitary
  systemProb := fair
  systemUnitary := 1
  reservoirProb := fair
  reservoirUnitary := 1
  systemMarginal := by
    rw [cnot_fair_joint]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [density, fair, Fin.sum_univ_succ]
  reservoirMarginal := by
    rw [cnot_fair_joint]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [density, fair, Fin.sum_univ_succ]

lemma fair_cnot_information : mutualInformation fairEvolution = 0 := by
  change entropy fair + entropy fair - entropy (tensor fair fair) = 0
  rw [entropy_tensor]
  ring

lemma fair_cnot_unchanged_reservoir (β : ℝ) :
    density fairEvolution.reservoirUnitary fairEvolution.reservoirProb =
      Matrix.diagonal (fun i => (gibbs β (fun _ : Fin 2 => 0) i : ℂ)) := by
  rw [zero_hamiltonian_gibbs]
  simp [fairEvolution, density]

lemma fair_cnot_heat (β : ℝ) :
    heat (fun _ => 0) fairEvolution.reservoirProb fairEvolution.reservoirUnitary
      (gibbs β (fun _ : Fin 2 => 0)) = 0 :=
  zero_hamiltonian_heat _ _ _

/-- The final system retains the label in every branch; a pure target also copies it. -/
lemma cnot_branch_records (z r : Fin 2) :
    (cnotAction (z, r)).1 = z ∧ (cnotAction (z, 0)).2 = z := by
  constructor
  · rfl
  · fin_cases z <;> rfl

lemma pure_target_is_pure : IsPure pureZero :=
  ⟨0, by simp [pureZero]⟩

lemma pure_target_not_gibbs (β : ℝ) (E : Fin 2 → ℝ) : pureZero ≠ gibbs β E := by
  intro h
  apply gibbs_not_pure β E
  rw [← h]
  exact pure_target_is_pure

lemma pure_target_zero_heat (p : Probability (Fin 2)) (U : Unitary (Fin 2)) :
    heat (fun _ => 0) p U pureZero = 0 :=
  zero_hamiltonian_heat _ _ _

end GibbsRecordHeat

end

end OperatorKO7.Meta.LiteratureReview
