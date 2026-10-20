import OperatorKO7.Meta.BoundaryObserver.BitDivision

set_option autoImplicit false

/-!
# Finite exact recovery and reliable recovery

Completes the distinction after Proposition 5.2 of the Observation Principle manuscript.
Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, M11.
The input law is exactly `BitDivision.readingsJoint`, with a uniform hidden bit and independent
readings conditional on that bit. The decoder receives the whole finite transcript.
Relation: none. Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.NoisyResolution

open BitDivision

/-- The joint probability of a finite transcript is nonnegative in the stated range. -/
theorem readingsJoint_nonneg (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2)
    (b : Bool) (ys : Fin N → Bool) : 0 ≤ readingsJoint N ε b ys := by
  unfold readingsJoint
  refine mul_nonneg (by norm_num) (Finset.prod_nonneg fun i _ => ?_)
  split_ifs <;> linarith

/-- With nonzero noise every finite transcript has positive probability under either bit. -/
theorem readingsJoint_pos (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2)
    (b : Bool) (ys : Fin N → Bool) : 0 < readingsJoint N ε b ys := by
  unfold readingsJoint
  refine mul_pos (by norm_num) (Finset.prod_pos fun i _ => ?_)
  split_ifs <;> linarith

/-- The error probability of a deterministic decoder of all `N` reports. -/
noncomputable def decoderError (N : ℕ) (ε : ℝ) (decode : (Fin N → Bool) → Bool) : ℝ :=
  ∑ ys, readingsJoint N ε (!(decode ys)) ys

/-- The error also equals the sum over both hidden-bit values of the wrong-answer cells. -/
theorem decoderError_eq_sum (N : ℕ) (ε : ℝ) (decode : (Fin N → Bool) → Bool) :
    decoderError N ε decode =
      ∑ b, ∑ ys, if decode ys ≠ b then readingsJoint N ε b ys else 0 := by
  rw [Finset.sum_comm]
  unfold decoderError
  refine Finset.sum_congr rfl fun ys _ => ?_
  cases decode ys <;> simp

/-- Every transcript cell contains at least the probability of `N` incorrect reports. -/
theorem readingsJoint_lower (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2)
    (b : Bool) (ys : Fin N → Bool) :
    (1 / 2 : ℝ) * (1 / 2 - ε) ^ N ≤ readingsJoint N ε b ys := by
  have hq : (0 : ℝ) ≤ 1 / 2 - ε := by linarith
  have hp : (1 / 2 - ε) ^ N ≤ ∏ i : Fin N, if ys i = b then 1 / 2 + ε else 1 / 2 - ε := by
    calc (1 / 2 - ε) ^ N = ∏ _i : Fin N, (1 / 2 - ε) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hq) (fun i _ => by split_ifs <;> linarith)
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

/-- A uniform positive lower bound for the error of every finite-transcript decoder. -/
theorem decoderError_lower (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2)
    (decode : (Fin N → Bool) → Bool) :
    (1 - 2 * ε) ^ N / 2 ≤ decoderError N ε decode := by
  have heq : (1 - 2 * ε) ^ N / 2 =
      ∑ _ys : Fin N → Bool, (1 / 2 : ℝ) * (1 / 2 - ε) ^ N := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool,
      nsmul_eq_mul]
    push_cast
    rw [show 1 - 2 * ε = 2 * (1 / 2 - ε) by ring, mul_pow]
    ring
  rw [heq]
  exact Finset.sum_le_sum fun ys _ => readingsJoint_lower N ε h0 h1 _ ys

/-- No finite decoder has error zero when the noise is positive. -/
theorem decoderError_pos (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2)
    (decode : (Fin N → Bool) → Bool) : 0 < decoderError N ε decode := by
  have hbase : 0 < 1 - 2 * ε := by linarith
  exact lt_of_lt_of_le (div_pos (pow_pos hbase N) (by norm_num))
    (decoderError_lower N ε h0 h1.le decode)

/-- The full-support form rules out a decoder correct on every positive-probability input. -/
theorem no_finite_exact_decoder (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) :
    ¬ ∃ decode : (Fin N → Bool) → Bool,
      ∀ b ys, 0 < readingsJoint N ε b ys → decode ys = b := by
  rintro ⟨decode, h⟩
  let ys : Fin N → Bool := fun _ => false
  have he := h (!(decode ys)) ys (readingsJoint_pos N ε h0 h1 _ ys)
  cases hd : decode ys <;> simp [hd] at he

/-- At zero reliability margin every decoder has error exactly one half, for every horizon. -/
theorem decoderError_zero_signal (N : ℕ) (decode : (Fin N → Bool) → Bool) :
    decoderError N 0 decode = 1 / 2 := by
  have heq : ∀ ys, readingsJoint N 0 (!(decode ys)) ys = readingsJoint N 0 false ys := by
    intro ys
    simp [readingsJoint]
  unfold decoderError
  rw [Finset.sum_congr rfl fun ys _ => heq ys, readingsJoint_marginal_label]

/-- The majority decoder returns true exactly when more than half of the reports are true. -/
def majorityDecoder (N : ℕ) (ys : Fin N → Bool) : Bool :=
  decide (N < 2 * (Finset.univ.filter (fun i => ys i = true)).card)

/-- On odd horizons a wrong majority is exactly a strict minority of correct reports. -/
theorem majority_wrong_iff (N : ℕ) (hN : Odd N) (ys : Fin N → Bool) (b : Bool) :
    majorityDecoder N ys ≠ b ↔
      2 * (Finset.univ.filter (fun i => ys i = b)).card < N := by
  obtain ⟨k, hk⟩ := hN
  have hfilters : Finset.univ.filter (fun i : Fin N => ¬ ys i = true) =
      Finset.univ.filter (fun i => ys i = false) := by
    ext i
    cases ys i <;> simp
  have htotal := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => ys i = true)
  rw [hfilters, Finset.card_univ, Fintype.card_fin] at htotal
  cases b <;> simp [majorityDecoder] <;> omega

/-- The implemented majority decoder has the manuscript's exponential error bound. -/
theorem majority_decoder_error_le (N : ℕ) (hN : Odd N) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    decoderError N ε (majorityDecoder N) ≤ Real.exp (-2 * N * ε ^ 2) := by
  have hrow : ∀ b : Bool,
      (∑ ys, if majorityDecoder N ys ≠ b then readingsJoint N ε b ys else 0) =
        (1 / 2 : ℝ) *
          (∑ ys : Fin N → Bool,
            if 2 * (Finset.univ.filter (fun i => ys i = b)).card < N then
              ∏ i, (if ys i = b then 1 / 2 + ε else 1 / 2 - ε) else 0) := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ys _ => ?_
    simp only [majority_wrong_iff N hN ys b, readingsJoint, mul_ite, mul_zero]
  rw [decoderError_eq_sum, Fintype.sum_bool, hrow, hrow]
  linarith [majority_error_le N ε h0 h1 true, majority_error_le N ε h0 h1 false]

/-- Every positive error tolerance is achieved by a finite odd horizon at positive signal. -/
theorem arbitrarily_reliable_majority (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, Odd N ∧ decoderError N ε (majorityDecoder N) < δ := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((-Real.log δ) / (4 * ε ^ 2))
  have hs : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hkn : -Real.log δ < (k : ℝ) * (4 * ε ^ 2) :=
    (div_lt_iff₀ (by positivity)).mp hk
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  refine ⟨2 * k + 1, hodd,
    lt_of_le_of_lt (majority_decoder_error_le _ hodd ε h0.le h1) ?_⟩
  have he : -2 * ((2 * k + 1 : ℕ) : ℝ) * ε ^ 2 < Real.log δ := by
    push_cast
    nlinarith
  calc Real.exp (-2 * ((2 * k + 1 : ℕ) : ℝ) * ε ^ 2)
      < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr he
    _ = δ := Real.exp_log hδ

/-- Exact finite recovery fails while approximate recovery attains every positive tolerance. -/
theorem finite_exact_vs_reliable (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    (∀ N decode, 0 < decoderError N ε decode) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, Odd N ∧ decoderError N ε (majorityDecoder N) < δ) :=
  ⟨fun N decode => decoderError_pos N ε h0.le h1 decode,
    fun δ hδ => arbitrarily_reliable_majority ε h0 h1.le δ hδ⟩

end OperatorKO7.Meta.BoundaryObserver.NoisyResolution
