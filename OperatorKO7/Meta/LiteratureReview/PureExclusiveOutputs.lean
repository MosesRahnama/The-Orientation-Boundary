import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Corollary cor:pure-exclusive-outputs states that complementary rank-one
projectors attain the maximal one-sided exclusive probability
1 - |inner ψ φ|² for two distinct pure states, and alternating the two
tests on independent fresh copies identifies either label without error
in at most 2 / (1 - |inner ψ φ|²) expected readings.
The Hilbert space is EuclideanSpace ℂ (Fin n).
An effect is a positive semidefinite matrix with positive semidefinite
complement, so its upper bound is in the Loewner order.
The stopping law explicitly uses products of independent reading
probabilities; successive measurements of one evolving copy are excluded.
-/

noncomputable section

open scoped BigOperators ComplexOrder Topology
open Matrix Filter

namespace PureExclusiveOutputs

abbrev Vec (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ}

def IsEffect (E : Mat n) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

def projector (φ : Vec n) : Mat n :=
  vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))

def exclusive (φ : Vec n) : Mat n := 1 - projector φ

def born (E : Mat n) (ψ : Vec n) : ℝ :=
  (star (WithLp.ofLp ψ) ⬝ᵥ E *ᵥ WithLp.ofLp ψ).re

def success (ψ φ : Vec n) : ℝ := 1 - ‖inner ℂ ψ φ‖ ^ 2

lemma inner_dot (ψ φ : Vec n) :
    inner ℂ ψ φ = star (WithLp.ofLp ψ) ⬝ᵥ WithLp.ofLp φ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma born_eq_inner (E : Mat n) (ψ : Vec n) :
    born E ψ =
      (inner ℂ ψ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) E ψ)).re := by
  rw [inner_dot, Matrix.ofLp_toEuclideanCLM]
  rfl

lemma inner_self_unit (φ : Vec n) (hφ : ‖φ‖ = 1) :
    inner ℂ φ φ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hφ]
  norm_num

lemma projector_hermitian (φ : Vec n) : (projector φ).IsHermitian := by
  change (projector φ)ᴴ = projector φ
  simp [projector]

lemma projector_sq (φ : Vec n) (hφ : ‖φ‖ = 1) :
    projector φ * projector φ = projector φ := by
  unfold projector
  rw [vecMulVec_mul_vecMulVec, ← inner_dot φ φ, inner_self_unit φ hφ,
    one_smul]

lemma exclusive_hermitian (φ : Vec n) : (exclusive φ).IsHermitian :=
  Matrix.isHermitian_one.sub (projector_hermitian φ)

lemma exclusive_sq (φ : Vec n) (hφ : ‖φ‖ = 1) :
    exclusive φ * exclusive φ = exclusive φ := by
  unfold exclusive
  rw [sub_mul, one_mul, mul_sub, mul_one, projector_sq φ hφ,
    sub_self, sub_zero]

lemma projection_posSemidef (A : Mat n) (hA : A.IsHermitian)
    (hsq : A * A = A) : A.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [hA.eq, hsq] at h

lemma projector_effect (φ : Vec n) (hφ : ‖φ‖ = 1) :
    IsEffect (projector φ) := by
  constructor
  · exact projection_posSemidef _ (projector_hermitian φ) (projector_sq φ hφ)
  · exact projection_posSemidef _ (exclusive_hermitian φ) (exclusive_sq φ hφ)

lemma exclusive_effect (φ : Vec n) (hφ : ‖φ‖ = 1) :
    IsEffect (exclusive φ) := by
  refine ⟨(projector_effect φ hφ).2, ?_⟩
  have h : (1 : Mat n) - exclusive φ = projector φ := by
    unfold exclusive
    abel
  rw [h]
  exact (projector_effect φ hφ).1

lemma effects_sum (φ : Vec n) : exclusive φ + projector φ = 1 := by
  unfold exclusive
  abel

lemma born_sub (A B : Mat n) (ψ : Vec n) :
    born (A - B) ψ = born A ψ - born B ψ := by
  simp only [born, sub_mulVec, dotProduct_sub, Complex.sub_re]

lemma born_one (ψ : Vec n) : born (1 : Mat n) ψ = ‖ψ‖ ^ 2 := by
  unfold born
  rw [one_mulVec, ← inner_dot ψ ψ]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) ψ).symm

lemma born_projector (ψ φ : Vec n) :
    born (projector φ) ψ = ‖inner ℂ ψ φ‖ ^ 2 := by
  unfold born projector
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct,
    smul_eq_mul, ← inner_dot ψ φ, ← inner_dot φ ψ]
  calc
    (inner ℂ ψ φ * inner ℂ φ ψ).re =
        ‖inner ℂ ψ φ * inner ℂ φ ψ‖ :=
      inner_mul_symm_re_eq_norm (𝕜 := ℂ) ψ φ
    _ = ‖inner ℂ ψ φ‖ ^ 2 := by
      rw [norm_mul, ← norm_inner_symm (𝕜 := ℂ) ψ φ, pow_two]

lemma born_exclusive (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) :
    born (exclusive φ) ψ = success ψ φ := by
  rw [exclusive, born_sub, born_one, hψ, born_projector]
  norm_num [success]

lemma born_exclusive_self (φ : Vec n) (hφ : ‖φ‖ = 1) :
    born (exclusive φ) φ = 0 := by
  rw [born_exclusive φ φ hφ]
  simp [success, inner_self_unit φ hφ]

lemma born_effect_bounds (E : Mat n) (hE : IsEffect E)
    (ψ : Vec n) (hψ : ‖ψ‖ = 1) :
    0 ≤ born E ψ ∧ born E ψ ≤ 1 := by
  constructor
  · exact hE.1.re_dotProduct_nonneg (WithLp.ofLp ψ)
  · have h := hE.2.re_dotProduct_nonneg (WithLp.ofLp ψ)
    change 0 ≤ born (1 - E) ψ at h
    rw [born_sub, born_one, hψ] at h
    norm_num at h
    linarith

/-- The two outputs are the Born probabilities of E and its complement. -/
def measuredRow (E : Mat n) (ψ : Vec n) (outcome : Bool) : ℝ :=
  if outcome then born E ψ else born (1 - E) ψ

lemma measuredRow_isLaw (E : Mat n) (hE : IsEffect E)
    (ψ : Vec n) (hψ : ‖ψ‖ = 1) :
    (∀ outcome, 0 ≤ measuredRow E ψ outcome) ∧
      (∑ outcome : Bool, measuredRow E ψ outcome) = 1 := by
  constructor
  · intro outcome
    cases outcome
    · exact hE.2.re_dotProduct_nonneg (WithLp.ofLp ψ)
    · exact hE.1.re_dotProduct_nonneg (WithLp.ofLp ψ)
  · rw [Fintype.sum_bool]
    norm_num [measuredRow, born_sub, born_one, hψ]

lemma annihilates_of_born_zero (E : Mat n) (hE : E.PosSemidef)
    (φ : Vec n) (hz : born E φ = 0) :
    E *ᵥ WithLp.ofLp φ = 0 := by
  apply (hE.dotProduct_mulVec_zero_iff (WithLp.ofLp φ)).mp
  apply Complex.ext
  · exact hz
  · exact (RCLike.nonneg_iff.mp (hE.2 (WithLp.ofLp φ))).2

lemma mul_projector (E : Mat n) (φ : Vec n) :
    E * projector φ =
      vecMulVec (E *ᵥ WithLp.ofLp φ) (star (WithLp.ofLp φ)) := by
  ext i j
  change (∑ k, E i k * (WithLp.ofLp φ k * star (WithLp.ofLp φ j))) =
    (∑ k, E i k * WithLp.ofLp φ k) * star (WithLp.ofLp φ j)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma effect_le_exclusive (E : Mat n) (hE : IsEffect E)
    (φ : Vec n) (hφ : ‖φ‖ = 1) (hz : born E φ = 0) :
    (exclusive φ - E).PosSemidef := by
  have hker := annihilates_of_born_zero E hE.1 φ hz
  have hEP : E * projector φ = 0 := by
    rw [mul_projector, hker, zero_vecMulVec]
  have hPE : projector φ * E = 0 := by
    have h := congrArg Matrix.conjTranspose hEP
    simpa only [conjTranspose_mul, hE.1.isHermitian.eq,
      (projector_hermitian φ).eq, conjTranspose_zero] using h
  have hQE : exclusive φ * E = E := by
    rw [exclusive, sub_mul, one_mul, hPE, sub_zero]
  have hEQ : E * exclusive φ = E := by
    rw [exclusive, mul_sub, mul_one, hEP, sub_zero]
  have hc :
      (exclusive φ)ᴴ * (1 - E) * exclusive φ = exclusive φ - E := by
    rw [(exclusive_hermitian φ).eq, mul_sub, mul_one, sub_mul,
      hQE, exclusive_sq φ hφ, hEQ]
  have hp := hE.2.conjTranspose_mul_mul_same (exclusive φ)
  rwa [hc] at hp

lemma exclusive_mass_optimal (ψ φ : Vec n) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) (E : Mat n) (hE : IsEffect E) (hz : born E φ = 0) :
    born E ψ ≤ success ψ φ := by
  have h := (effect_le_exclusive E hE φ hφ hz).re_dotProduct_nonneg
    (WithLp.ofLp ψ)
  change 0 ≤ born (exclusive φ - E) ψ at h
  rw [born_sub, born_exclusive ψ φ hψ] at h
  linarith

lemma success_symm (ψ φ : Vec n) : success ψ φ = success φ ψ := by
  unfold success
  rw [norm_inner_symm ψ φ]

lemma success_pos (ψ φ : Vec n) (hc : ‖inner ℂ ψ φ‖ < 1) :
    0 < success ψ φ := by
  have hn := norm_nonneg (inner ℂ ψ φ)
  have hprod : 0 < (1 - ‖inner ℂ ψ φ‖) * (1 + ‖inner ℂ ψ φ‖) :=
    mul_pos (by linarith) (by linarith)
  unfold success
  nlinarith

lemma success_le_one (ψ φ : Vec n) : success ψ φ ≤ 1 := by
  unfold success
  nlinarith [sq_nonneg ‖inner ℂ ψ φ‖]

lemma maximal_exclusive_mass (ψ φ : Vec n) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) :
    IsGreatest {r : ℝ | ∃ E : Mat n,
      IsEffect E ∧ born E φ = 0 ∧ born E ψ = r} (success ψ φ) := by
  constructor
  · exact ⟨exclusive φ, exclusive_effect φ hφ,
      born_exclusive_self φ hφ, born_exclusive ψ φ hψ⟩
  · rintro r ⟨E, hE, hz, rfl⟩
    exact exclusive_mass_optimal ψ φ hψ hφ E hE hz

/-- The label true denotes ψ; the label false denotes φ. -/
def inputState (ψ φ : Vec n) (label : Bool) : Vec n :=
  if label then ψ else φ

/-- The first test names ψ on a click; the second test names φ on a click. -/
def testEffect (ψ φ : Vec n) (test : Bool) : Mat n :=
  if test then exclusive φ else exclusive ψ

def click (ψ φ : Vec n) (test label : Bool) : ℝ :=
  born (testEffect ψ φ test) (inputState ψ φ label)

lemma test_isEffect (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (test : Bool) : IsEffect (testEffect ψ φ test) := by
  cases test
  · exact exclusive_effect ψ hψ
  · exact exclusive_effect φ hφ

lemma click_eq (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (test label : Bool) :
    click ψ φ test label = if test = label then success ψ φ else 0 := by
  cases test <;> cases label <;>
    simp [click, testEffect, inputState,
      born_exclusive ψ φ hψ, born_exclusive φ ψ hφ,
      born_exclusive_self ψ hψ, born_exclusive_self φ hφ,
      success_symm φ ψ]

/-- Independence of fresh copies gives this two-reading block probability. -/
def blockClick (ψ φ : Vec n) (label guess : Bool) : ℝ :=
  if guess then click ψ φ true label
  else (1 - click ψ φ true label) * click ψ φ false label

def blockFailure (ψ φ : Vec n) (label : Bool) : ℝ :=
  (1 - click ψ φ true label) * (1 - click ψ φ false label)

lemma blockClick_eq (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label guess : Bool) :
    blockClick ψ φ label guess =
      if guess = label then success ψ φ else 0 := by
  cases label <;> cases guess <;>
    simp [blockClick, click_eq ψ φ hψ hφ]

lemma blockFailure_eq (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label : Bool) :
    blockFailure ψ φ label = 1 - success ψ φ := by
  cases label <;> simp [blockFailure, click_eq ψ φ hψ hφ]

/-- The weight describes k failed blocks and the next block's first click. -/
def stopWeight (ψ φ : Vec n) (label : Bool) (k : ℕ) (guess : Bool) : ℝ :=
  blockFailure ψ φ label ^ k * blockClick ψ φ label guess

def readingCount (k : ℕ) (guess : Bool) : ℕ :=
  2 * k + if guess then 1 else 2

def expectedReadings (ψ φ : Vec n) (label : Bool) : ℝ :=
  ∑' k, ∑ guess : Bool, (readingCount k guess : ℝ) *
    stopWeight ψ φ label k guess

lemma stopWeight_eq (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label : Bool) (k : ℕ) (guess : Bool) :
    stopWeight ψ φ label k guess =
      if guess = label then
        ProbabilityTheory.geometricPMFReal (success ψ φ) k else 0 := by
  rw [stopWeight, blockFailure_eq ψ φ hψ hφ,
    blockClick_eq ψ φ hψ hφ]
  by_cases h : guess = label <;>
    simp [h, ProbabilityTheory.geometricPMFReal]

lemma stopWeight_nonneg (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) (k : ℕ) (guess : Bool) :
    0 ≤ stopWeight ψ φ label k guess := by
  rw [stopWeight_eq ψ φ hψ hφ]
  by_cases h : guess = label
  · rw [if_pos h]
    exact ProbabilityTheory.geometricPMFReal_nonneg
      (success_pos ψ φ hc) (success_le_one ψ φ)
  · simp [h]

lemma stopWeight_wrong (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label : Bool) (k : ℕ) (guess : Bool) (h : guess ≠ label) :
    stopWeight ψ φ label k guess = 0 := by
  rw [stopWeight_eq ψ φ hψ hφ, if_neg h]

lemma stopWeight_sum (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label : Bool) (k : ℕ) :
    (∑ guess : Bool, stopWeight ψ φ label k guess) =
      ProbabilityTheory.geometricPMFReal (success ψ φ) k := by
  cases label <;> simp [stopWeight_eq ψ φ hψ hφ]

lemma stopping_prefix (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (label : Bool) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ guess : Bool, stopWeight ψ φ label k guess) +
      blockFailure ψ φ label ^ N = 1 := by
  simp_rw [stopWeight_sum ψ φ hψ hφ, blockFailure_eq ψ φ hψ hφ]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      simp only [ProbabilityTheory.geometricPMFReal] at ih ⊢
      nlinarith

lemma stopping_hasSum_one (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) :
    HasSum (fun k => ∑ guess : Bool, stopWeight ψ φ label k guess) 1 := by
  simpa only [stopWeight_sum ψ φ hψ hφ] using
    ProbabilityTheory.geometricPMFRealSum
      (success_pos ψ φ hc) (success_le_one ψ φ)

lemma survival_tendsto_zero (ψ φ : Vec n) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) :
    Tendsto (fun k : ℕ => blockFailure ψ φ label ^ k) atTop (𝓝 0) := by
  have hd := success_pos ψ φ hc
  simpa only [blockFailure_eq ψ φ hψ hφ] using
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr (success_le_one ψ φ))
      (by linarith : 1 - success ψ φ < 1)

lemma geometric_blocks_mean {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasSum (fun k : ℕ =>
      ((k : ℝ) + 1) * ProbabilityTheory.geometricPMFReal δ k) (1 / δ) := by
  have hq : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hn : ‖1 - δ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    linarith
  have hb : HasSum (fun k : ℕ => ((k : ℝ) + 1) * (1 - δ) ^ k)
      (1 / δ ^ 2) := by
    simpa using
      (hasSum_choose_mul_geometric_of_norm_lt_one (r := 1 - δ) 1 hn)
  have hm := hb.mul_right δ
  convert hm using 1
  · ext k
    unfold ProbabilityTheory.geometricPMFReal
    ring
  · field_simp [ne_of_gt hδ] ; ring

lemma stopWeight_moment_term (ψ φ : Vec n) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) (label : Bool) (k : ℕ) :
    (∑ guess : Bool, (readingCount k guess : ℝ) *
        stopWeight ψ φ label k guess) =
      (readingCount k label : ℝ) *
        ProbabilityTheory.geometricPMFReal (success ψ φ) k := by
  cases label <;> simp [stopWeight_eq ψ φ hψ hφ]

lemma readings_hasSum (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) :
    HasSum
      (fun k => ∑ guess : Bool, (readingCount k guess : ℝ) *
        stopWeight ψ φ label k guess)
      (2 / success ψ φ - if label then 1 else 0) := by
  have hd := success_pos ψ φ hc
  have hmass := ProbabilityTheory.geometricPMFRealSum hd (success_le_one ψ φ)
  have hblocks := geometric_blocks_mean hd (success_le_one ψ φ)
  cases label
  · have h := hblocks.mul_left 2
    convert h using 1
    · ext k
      rw [stopWeight_moment_term ψ φ hψ hφ]
      norm_num [readingCount] ; ring
    · norm_num ; ring
  · have h := (hblocks.mul_left 2).sub hmass
    convert h using 1
    · ext k
      rw [stopWeight_moment_term ψ φ hψ hφ]
      norm_num [readingCount] ; ring
    · norm_num ; ring

lemma expectedReadings_eq (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) :
    expectedReadings ψ φ label =
      2 / success ψ φ - if label then 1 else 0 :=
  (readings_hasSum ψ φ hψ hφ hc label).tsum_eq

lemma expectedReadings_le (ψ φ : Vec n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hc : ‖inner ℂ ψ φ‖ < 1) (label : Bool) :
    expectedReadings ψ φ label ≤ 2 / success ψ φ := by
  rw [expectedReadings_eq ψ φ hψ hφ hc label]
  cases label <;> norm_num

end PureExclusiveOutputs

open PureExclusiveOutputs in
/-- The theorem includes optimal effects and the independent-copy stopping law. -/
theorem pure_exclusive_outputs {n : ℕ} (ψ φ : Vec n)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hc : ‖inner ℂ ψ φ‖ < 1) :
    let δ := success ψ φ
    IsEffect (exclusive φ) ∧
      IsEffect (projector φ) ∧
      exclusive φ + projector φ = 1 ∧
      born (exclusive φ) ψ = δ ∧
      born (exclusive φ) φ = 0 ∧
      IsEffect (exclusive ψ) ∧
      born (exclusive ψ) φ = δ ∧
      born (exclusive ψ) ψ = 0 ∧
      IsGreatest {r : ℝ | ∃ E : Mat n,
        IsEffect E ∧ born E φ = 0 ∧ born E ψ = r} δ ∧
      IsGreatest {r : ℝ | ∃ E : Mat n,
        IsEffect E ∧ born E ψ = 0 ∧ born E φ = r} δ ∧
      0 < δ ∧
      (∀ label : Bool,
        (∀ k guess, 0 ≤ stopWeight ψ φ label k guess) ∧
        HasSum (fun k => ∑ guess : Bool, stopWeight ψ φ label k guess) 1 ∧
        (∀ k guess, guess ≠ label → stopWeight ψ φ label k guess = 0) ∧
        Tendsto (fun k : ℕ => blockFailure ψ φ label ^ k) atTop (𝓝 0) ∧
        HasSum
          (fun k => ∑ guess : Bool, (readingCount k guess : ℝ) *
            stopWeight ψ φ label k guess)
          (2 / δ - if label then 1 else 0) ∧
        expectedReadings ψ φ label ≤ 2 / δ) := by
  dsimp only
  refine ⟨exclusive_effect φ hφ, projector_effect φ hφ, effects_sum φ,
    born_exclusive ψ φ hψ, born_exclusive_self φ hφ, exclusive_effect ψ hψ,
    ?_, born_exclusive_self ψ hψ, maximal_exclusive_mass ψ φ hψ hφ,
    ?_, success_pos ψ φ hc, ?_⟩
  · simpa only [success_symm φ ψ] using born_exclusive φ ψ hφ
  · simpa only [success_symm φ ψ] using maximal_exclusive_mass φ ψ hφ hψ
  · intro label
    exact ⟨stopWeight_nonneg ψ φ hψ hφ hc label,
      stopping_hasSum_one ψ φ hψ hφ hc label,
      stopWeight_wrong ψ φ hψ hφ label,
      survival_tendsto_zero ψ φ hψ hφ hc label,
      readings_hasSum ψ φ hψ hφ hc label,
      expectedReadings_le ψ φ hψ hφ hc label⟩

end

end OperatorKO7.Meta.LiteratureReview
