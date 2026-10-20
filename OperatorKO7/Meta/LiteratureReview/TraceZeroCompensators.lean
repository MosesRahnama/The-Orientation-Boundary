import Mathlib

open scoped ENNReal NNReal

namespace OperatorKO7.Meta.LiteratureReview

/-!
Remark rem:trace-zero-compensators states that finite commutators have trace zero,
with the compensating edge terms exhibited for the unilateral shift, the
truncated oscillator, and the collective ladder, whose normalized coefficients
and commutator eigenvalues converge at each fixed weight to the bosonic values.

The infinite shift is defined on Mathlib's complex lp space with exponent two,
and its backward shift is identified by the Hilbert adjoint pairing.
The collective ladder uses its explicit weight-basis matrices.
The collective limit is coefficientwise at fixed weights, without an assertion
of operator-norm convergence; the limit proofs use positive n.
The oscillator's top commutator eigenvalue is -k; its defect relative to the
identity is -(k+1) times the top-coordinate projection.
-/

namespace TraceZeroCompensators

open scoped BigOperators Topology
open Filter Matrix

noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def comm {n : ℕ} (A B : Mat n) : Mat n := A * B - B * A

def defect {n : ℕ} (A B : Mat n) (c : ℂ) : Mat n :=
  comm A B - c • (1 : Mat n)

lemma trace_comm {n : ℕ} (A B : Mat n) : Matrix.trace (comm A B) = 0 := by
  rw [comm, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

lemma trace_defect {n : ℕ} (A B : Mat n) (c : ℂ) :
    Matrix.trace (defect A B c) = -((n : ℂ) * c) := by
  rw [defect, Matrix.trace_sub, trace_comm]
  simp [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm]

lemma no_scalar_commutator {n : ℕ} (hn : 0 < n)
    (A B : Mat n) (c : ℂ) (hc : c ≠ 0) :
    comm A B ≠ c • (1 : Mat n) := by
  intro h
  have ht := trace_comm A B
  rw [h, Matrix.trace_smul, Matrix.trace_one] at ht
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply mul_ne_zero hc hn'
  simpa only [Fintype.card_fin, smul_eq_mul] using ht

abbrev H := lp (fun _ : ℕ => ℂ) 2

def forwardSeq (v : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => v m

def shift (v : H) : H :=
  ⟨forwardSeq v, by
    apply memℓp_gen
    apply (summable_nat_add_iff 1).1
    simpa only [forwardSeq] using
      (lp.memℓp v).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num)⟩

def backward (v : H) : H :=
  ⟨fun m => v (m + 1), by
    apply memℓp_gen
    exact (summable_nat_add_iff 1).2
      ((lp.memℓp v).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num))⟩

@[simp] lemma shift_zero (v : H) : shift v 0 = 0 := rfl
@[simp] lemma shift_succ (v : H) (m : ℕ) : shift v (m + 1) = v m := rfl
@[simp] lemma backward_apply (v : H) (m : ℕ) : backward v m = v (m + 1) := rfl

lemma shift_adjoint_pair (u v : H) :
    inner ℂ (shift u) v = inner ℂ u (backward v) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa only [shift_zero, shift_succ, inner_zero_left, zero_add, backward_apply]
    using (lp.summable_inner (𝕜 := ℂ) (shift u) v).tsum_eq_zero_add

lemma shift_basis (k : ℕ) :
    shift (lp.single 2 k (1 : ℂ)) = lp.single 2 (k + 1) (1 : ℂ) := by
  apply lp.ext
  funext m
  cases m with
  | zero => simp
  | succ m =>
    by_cases hm : m = k
    · subst m
      simp
    · have hs : m + 1 ≠ k + 1 := by omega
      simp [hm]

lemma unilateral_shift_commutator (v : H) :
    backward (shift v) - shift (backward v) = lp.single 2 0 (v 0) := by
  apply lp.ext
  funext m
  cases m with
  | zero => simp
  | succ m => simp

lemma vacuum_projection (v : H) :
    (lp.single 2 0 (v 0) : H) =
      inner ℂ (lp.single 2 0 (1 : ℂ) : H) v •
        (lp.single 2 0 (1 : ℂ) : H) := by
  apply lp.ext
  funext m
  by_cases hm : m = 0
  · subst m
    simp [lp.inner_single_left, RCLike.inner_apply, lp.coeFn_smul]
  · simp [lp.inner_single_left, RCLike.inner_apply, lp.coeFn_smul, hm]

lemma unilateral_shift_rank_one (v : H) :
    backward (shift v) - shift (backward v) =
      inner ℂ (lp.single 2 0 (1 : ℂ) : H) v •
        (lp.single 2 0 (1 : ℂ) : H) := by
  exact (unilateral_shift_commutator v).trans (vacuum_projection v)

def shiftTwo : Mat 2 := !![0, 0; 1, 0]

lemma shift_two_compression (i j : Fin 2) :
    shift (lp.single 2 j.val (1 : ℂ)) i.val = shiftTwo i j := by
  fin_cases i <;> fin_cases j <;> simp [shiftTwo]

lemma shift_two_commutator :
    comm shiftTwo.conjTranspose shiftTwo = !![1, 0; 0, -1] := by
  apply Matrix.ext
  intro i j
  change
    (∑ k : Fin 2, star (shiftTwo k i) * shiftTwo k j) -
        (∑ k : Fin 2, shiftTwo i k * star (shiftTwo j k)) =
      (!![1, 0; 0, -1] : Mat 2) i j
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [shiftTwo]

def lowering (n : ℕ) (a : ℕ → ℝ) : Mat (n + 1) :=
  fun i j => if j.val = i.val + 1 then (a j.val : ℂ) else 0

lemma lowering_adjoint_apply (n : ℕ) (a : ℕ → ℝ) (i j : Fin (n + 1)) :
    (lowering n a).conjTranspose i j =
      if i.val = j.val + 1 then (a i.val : ℂ) else 0 := by
  by_cases h : i.val = j.val + 1 <;>
    simp [lowering, Matrix.conjTranspose_apply, h]

lemma lowering_mul_adjoint (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0) :
    lowering n a * (lowering n a).conjTranspose =
      Matrix.diagonal (fun i => (a (i.val + 1) : ℂ) ^ 2) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i.val + 1 < n + 1
    · let t : Fin (n + 1) := ⟨i.val + 1, hi⟩
      rw [Finset.sum_eq_single t]
      · rw [lowering_adjoint_apply]
        simp [lowering, t, pow_two]
      · intro b _ hb
        have hb' : b.val ≠ i.val + 1 := by
          intro he
          apply hb
          apply Fin.ext
          exact he
        simp [lowering, hb']
      · simp
    · have hi' : i.val = n := by omega
      rw [hi', ha]
      simp only [Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro b _
      have hb : b.val ≠ n + 1 := by omega
      simp [lowering, hi', hb]
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b.val = i.val + 1
    · have hb' : b.val ≠ j.val + 1 := by
        intro he
        apply hij
        apply Fin.ext
        omega
      simp [lowering, hb']
    · simp [lowering, hb]

lemma adjoint_mul_lowering (n : ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) :
    (lowering n a).conjTranspose * lowering n a =
      Matrix.diagonal (fun i => (a i.val : ℂ) ^ 2) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i.val = 0
    · rw [hi, ha]
      simp only [Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro b _
      simp [lowering, hi]
    · let t : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      have ht : i.val = t.val + 1 := by dsimp [t]; omega
      rw [Finset.sum_eq_single t]
      · rw [lowering_adjoint_apply]
        simp only [lowering, if_pos ht, pow_two]
      · intro b _ hb
        have hb' : i.val ≠ b.val + 1 := by
          intro he
          apply hb
          apply Fin.ext
          dsimp [t]
          omega
        simp [lowering, hb']
      · simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : i.val = b.val + 1
    · have hb' : j.val ≠ b.val + 1 := by
        intro he
        apply hij
        apply Fin.ext
        omega
      simp [lowering, hb']
    · simp [lowering, hb]

lemma lowering_commutator (n : ℕ) (a : ℕ → ℝ)
    (hzero : a 0 = 0) (htop : a (n + 1) = 0) :
    comm (lowering n a) (lowering n a).conjTranspose =
      Matrix.diagonal (fun i =>
        (a (i.val + 1) : ℂ) ^ 2 - (a i.val : ℂ) ^ 2) := by
  rw [comm, lowering_mul_adjoint n a htop, adjoint_mul_lowering n a hzero,
    Matrix.diagonal_sub]

def oscillatorWeight (k m : ℕ) : ℝ :=
  if m ≤ k then Real.sqrt (m : ℝ) else 0

def oscillator (k : ℕ) : Mat (k + 1) := lowering k (oscillatorWeight k)

def topProjector (k : ℕ) : Mat (k + 1) :=
  Matrix.diagonal (fun i => if i.val = k then 1 else 0)

lemma oscillatorWeight_sq (k m : ℕ) :
    (oscillatorWeight k m : ℂ) ^ 2 = if m ≤ k then (m : ℂ) else 0 := by
  by_cases hm : m ≤ k
  · simp only [oscillatorWeight, if_pos hm]
    exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)))
  · simp [oscillatorWeight, hm]

lemma oscillator_lowering_entry (k : ℕ) (i j : Fin (k + 1)) :
    oscillator k i j =
      if j.val = i.val + 1 then (Real.sqrt (j.val : ℝ) : ℂ) else 0 := by
  have hj : j.val ≤ k := by omega
  simp [oscillator, lowering, oscillatorWeight, hj]

lemma oscillator_raising_entry (k : ℕ) (i j : Fin (k + 1)) :
    (oscillator k).conjTranspose i j =
      if i.val = j.val + 1 then (Real.sqrt (i.val : ℝ) : ℂ) else 0 := by
  unfold oscillator
  rw [lowering_adjoint_apply]
  have hi : i.val ≤ k := by omega
  simp [oscillatorWeight, hi]

lemma oscillator_raising_top_zero (k : ℕ) :
    (oscillator k).conjTranspose *ᵥ Pi.single (Fin.last k) 1 = 0 := by
  rw [Matrix.mulVec_single_one]
  funext i
  change (oscillator k).conjTranspose i (Fin.last k) = 0
  rw [oscillator_raising_entry]
  change
    (if i.val = k + 1 then (Real.sqrt (i.val : ℝ) : ℂ) else 0) = 0
  exact if_neg (ne_of_lt i.isLt)

lemma oscillator_commutator (k : ℕ) :
    comm (oscillator k) (oscillator k).conjTranspose =
      Matrix.diagonal (fun i => if i.val = k then -(k : ℂ) else 1) := by
  unfold oscillator
  rw [lowering_commutator k (oscillatorWeight k)
    (by simp [oscillatorWeight]) (by simp [oscillatorWeight])]
  apply congrArg (fun d : Fin (k + 1) → ℂ => Matrix.diagonal d)
  funext i
  rw [oscillatorWeight_sq, oscillatorWeight_sq]
  have hi : i.val ≤ k := by omega
  by_cases ht : i.val = k
  · simp [ht]
  · have hs : i.val + 1 ≤ k := by omega
    simp only [if_pos hi, if_pos hs, if_neg ht, Nat.cast_add, Nat.cast_one]
    ring

lemma oscillator_identity (k : ℕ) :
    comm (oscillator k) (oscillator k).conjTranspose =
      1 - ((k : ℂ) + 1) • topProjector k := by
  rw [oscillator_commutator]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases ht : i.val = k <;>
      simp [topProjector, ht, Matrix.smul_apply, smul_eq_mul]
  · simp [topProjector, hij, Matrix.smul_apply]

lemma oscillator_defect (k : ℕ) :
    defect (oscillator k) (oscillator k).conjTranspose 1 =
      -(((k : ℂ) + 1) • topProjector k) := by
  rw [defect, one_smul, oscillator_identity]
  abel

lemma oscillator_two_top :
    comm (oscillator 1) (oscillator 1).conjTranspose (Fin.last 1) (Fin.last 1) = -1 ∧
      defect (oscillator 1) (oscillator 1).conjTranspose 1
        (Fin.last 1) (Fin.last 1) = -2 := by
  constructor
  · rw [oscillator_commutator]
    norm_num
  · rw [oscillator_defect]
    norm_num [topProjector, Matrix.smul_apply, smul_eq_mul]

lemma oscillator_on_zero_top (k : ℕ) (v : Fin (k + 1) → ℂ)
    (hv : v (Fin.last k) = 0) :
    (comm (oscillator k) (oscillator k).conjTranspose) *ᵥ v = v := by
  rw [oscillator_commutator]
  funext i
  rw [Matrix.mulVec_diagonal]
  change (if i.val = k then -(k : ℂ) else 1) * v i = v i
  by_cases hi : i.val = k
  · have hi' : i = Fin.last k := Fin.ext hi
    subst i
    simp [hv]
  · simp [hi]

def lowerEmbed (k : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun v := Fin.snoc v 0
  map_add' := by
    intro v w
    funext i
    cases i using Fin.lastCases <;> simp
  map_smul' := by
    intro c v
    funext i
    cases i using Fin.lastCases <;> simp

lemma lowerEmbed_injective (k : ℕ) : Function.Injective (lowerEmbed k) := by
  intro v w h
  funext i
  simpa [lowerEmbed] using congrFun h i.castSucc

def lowSpace (k : ℕ) : Submodule ℂ (Fin (k + 1) → ℂ) :=
  LinearMap.range (lowerEmbed k)

lemma mem_lowSpace (k : ℕ) (v : Fin (k + 1) → ℂ) :
    v ∈ lowSpace k ↔ v (Fin.last k) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    simp [lowerEmbed]
  · intro hv
    refine' ⟨Fin.init v, _⟩
    change Fin.snoc (Fin.init v) 0 = v
    rw [← hv, Fin.snoc_init_self]

lemma lowSpace_finrank (k : ℕ) : Module.finrank ℂ (lowSpace k) = k := by
  rw [lowSpace, LinearMap.finrank_range_of_inj (lowerEmbed_injective k)]
  simp

lemma oscillator_on_lowSpace (k : ℕ) (v : Fin (k + 1) → ℂ)
    (hv : v ∈ lowSpace k) :
    (comm (oscillator k) (oscillator k).conjTranspose) *ᵥ v = v := by
  rcases hv with ⟨u, rfl⟩
  apply oscillator_on_zero_top
  simp [lowerEmbed]

lemma canonical_subspace_bound (k : ℕ) (A B : Mat (k + 1))
    (V : Submodule ℂ (Fin (k + 1) → ℂ))
    (hV : ∀ v ∈ V, (comm A B) *ᵥ v = v) :
    Module.finrank ℂ V ≤ k := by
  have hproper : V ≠ ⊤ := by
    intro htop
    have he : comm A B = 1 := by
      apply Matrix.ext_of_mulVec_single
      intro i
      simpa only [Matrix.one_mulVec] using hV (Pi.single i 1) (by simp [htop])
    apply no_scalar_commutator (Nat.succ_pos k) A B 1 one_ne_zero
    simpa using he
  have hlt : Module.finrank ℂ V <
      Module.finrank ℂ (⊤ : Submodule ℂ (Fin (k + 1) → ℂ)) :=
    Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hdim :
      Module.finrank ℂ (⊤ : Submodule ℂ (Fin (k + 1) → ℂ)) = k + 1 := by simp
  rw [hdim] at hlt
  omega

def collectiveWeight (n m : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * ((n : ℝ) + 1 - m))

def collective (n : ℕ) : Mat (n + 1) := lowering n (collectiveWeight n)

def numberOperator (n : ℕ) : Mat (n + 1) :=
  Matrix.diagonal (fun i => (i.val : ℂ))

lemma collectiveWeight_sq (n m : ℕ) (hm : m ≤ n + 1) :
    (collectiveWeight n m : ℂ) ^ 2 =
      (m : ℂ) * ((n : ℂ) + 1 - m) := by
  have hm' : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm
  have hp : 0 ≤ (m : ℝ) * ((n : ℝ) + 1 - m) :=
    mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hm')
  unfold collectiveWeight
  exact_mod_cast (Real.sq_sqrt hp)

lemma collective_commutator_diagonal (n : ℕ) :
    comm (collective n) (collective n).conjTranspose =
      Matrix.diagonal (fun i => (n : ℂ) - 2 * i.val) := by
  unfold collective
  rw [lowering_commutator n (collectiveWeight n)
    (by simp [collectiveWeight])
    (by simp [collectiveWeight, Nat.cast_add, Nat.cast_one])]
  apply congrArg (fun d : Fin (n + 1) → ℂ => Matrix.diagonal d)
  funext i
  rw [collectiveWeight_sq n (i.val + 1) (by omega),
    collectiveWeight_sq n i.val (by omega)]
  push_cast
  ring

lemma collective_commutator (n : ℕ) :
    comm (collective n) (collective n).conjTranspose =
      (n : ℂ) • (1 : Mat (n + 1)) - (2 : ℂ) • numberOperator n := by
  rw [collective_commutator_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [numberOperator, Matrix.smul_apply, smul_eq_mul]
  · simp [numberOperator, hij, Matrix.smul_apply]

lemma collective_low_weight_bound (n : ℕ) (w : Fin (n + 1)) (W : ℕ)
    (hw : w.val ≤ W) :
    |((n : ℝ) - 2 * w.val) - n| ≤ 2 * (W : ℝ) := by
  have he : ((n : ℝ) - 2 * w.val) - n = -(2 * (w.val : ℝ)) := by ring
  rw [he, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * w.val)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by norm_num)

def normalizedWeight (n m : ℕ) : ℝ :=
  collectiveWeight n m / Real.sqrt (n : ℝ)

def normalizedCollective (n : ℕ) : Mat (n + 1) :=
  lowering n (normalizedWeight n)

def normalizedCoefficient (n w : ℕ) : ℝ :=
  Real.sqrt (((w : ℝ) + 1) * ((n : ℝ) - w) / n)

def normalizedEigenvalue (n w : ℕ) : ℝ :=
  ((n : ℝ) - 2 * w) / n

lemma normalized_collective_eq (n : ℕ) :
    normalizedCollective n =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ • collective n := by
  ext i j
  by_cases h : j.val = i.val + 1 <;>
    simp [normalizedCollective, normalizedWeight, collective, lowering, h,
      Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma normalized_coefficient_eq (n w : ℕ) :
    normalizedCoefficient n w = normalizedWeight n (w + 1) := by
  unfold normalizedCoefficient normalizedWeight collectiveWeight
  rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
  congr 2 ; push_cast ; ring

lemma normalized_collective_commutator (n : ℕ) :
    comm (normalizedCollective n) (normalizedCollective n).conjTranspose =
      Matrix.diagonal (fun i => (normalizedEigenvalue n i.val : ℂ)) := by
  unfold normalizedCollective
  rw [lowering_commutator n (normalizedWeight n)
    (by simp [normalizedWeight, collectiveWeight])
    (by simp [normalizedWeight, collectiveWeight, Nat.cast_add, Nat.cast_one])]
  apply congrArg (fun d : Fin (n + 1) → ℂ => Matrix.diagonal d)
  funext i
  have hs : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)))
  simp only [normalizedWeight, Complex.ofReal_div, div_pow, hs]
  rw [collectiveWeight_sq n (i.val + 1) (by omega),
    collectiveWeight_sq n i.val (by omega)]
  unfold normalizedEigenvalue
  push_cast
  simp only [div_eq_mul_inv]
  ring

lemma collective_coefficient_limit (w : ℕ) :
    Tendsto (fun n : ℕ => normalizedCoefficient n w) atTop
      (𝓝 (Real.sqrt ((w : ℝ) + 1))) := by
  have hbase : Tendsto
      (fun n : ℕ => ((w : ℝ) + 1) * (1 - (w : ℝ) / n))
      atTop (𝓝 (((w : ℝ) + 1) * (1 - 0))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (w : ℝ)))
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt (((w : ℝ) + 1) * (1 - (w : ℝ) / n)))
      atTop (𝓝 (Real.sqrt ((w : ℝ) + 1))) := by
    simpa using hbase.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold normalizedCoefficient
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp [hn']

lemma collective_commutator_limit (w : ℕ) :
    Tendsto (fun n : ℕ => normalizedEigenvalue n w) atTop (𝓝 (1 : ℝ)) := by
  have hbase : Tendsto
      (fun n : ℕ => 1 - 2 * ((w : ℝ) / n))
      atTop (𝓝 ((1 : ℝ) - 2 * 0)) :=
    tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_const_div_atTop_nhds_zero_nat (w : ℝ)))
  have hlimit : Tendsto
      (fun n : ℕ => 1 - 2 * ((w : ℝ) / n)) atTop (𝓝 (1 : ℝ)) := by
    simpa using hbase
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold normalizedEigenvalue
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp [hn']

lemma normalized_collective_not_canonical (n : ℕ) :
    comm (normalizedCollective n) (normalizedCollective n).conjTranspose ≠ 1 := by
  simpa using no_scalar_commutator (Nat.succ_pos n)
    (normalizedCollective n) (normalizedCollective n).conjTranspose 1 one_ne_zero

end

end TraceZeroCompensators

open TraceZeroCompensators in
theorem trace_zero_compensators {n : ℕ} (A B : Mat n) (c : ℂ) :
    Matrix.trace (defect A B c) = -((n : ℂ) * c) ∧
      (0 < n → c ≠ 0 → comm A B ≠ c • (1 : Mat n)) :=
  ⟨trace_defect A B c, fun hn hc => no_scalar_commutator hn A B c hc⟩

end OperatorKO7.Meta.LiteratureReview
