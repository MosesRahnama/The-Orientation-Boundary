import OperatorKO7.Meta.SchemaCanonicalTrace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
This module proves arithmetic identities, inequalities, and limits for stipulated burden and
entropy functions. Those functions form an abstract numeric model. A bridge to observations on
canonical trace terms requires separate declarations.



























-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

namespace BaseDuplicatingSystem

open scoped Real

/-- Definition with formal content given by the displayed type and body.
-/
def residualProofWork (k : Nat) : Nat := k

/-- Definition with formal content given by the displayed type and body.
-/
def confessedBurdenDoubled (k p : Nat) : Nat := (k + 1) * (k + 2) * p

/-- Definition with formal content given by the displayed type and body. -/
def totalConfessedBurdenDoubled (k w : Nat) : Nat := (k + 1) * (k + 2) * w

@[simp] theorem residualProofWork_eq (k : Nat) : residualProofWork k = k := rfl

@[simp] theorem confessedBurdenDoubled_eq (k p : Nat) :
    confessedBurdenDoubled k p = (k + 1) * (k + 2) * p := rfl

@[simp] theorem totalConfessedBurdenDoubled_eq (k w : Nat) :
    totalConfessedBurdenDoubled k w = (k + 1) * (k + 2) * w := rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem sum_payloads_doubled (k p : Nat) :
    2 * ((Finset.range (k + 1)).sum (fun i => (i + 1) * p))
      = confessedBurdenDoubled k p := by
  induction k with
  | zero => simp [confessedBurdenDoubled]
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      unfold confessedBurdenDoubled
      ring

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem total_confessed_burden_doubled (k w : Nat) :
    2 * ((Finset.range (k + 1)).sum (fun i => (i + 1) * w))
      = totalConfessedBurdenDoubled k w :=
  sum_payloads_doubled k w

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body.

-/
noncomputable def confessionQuadraticInvariant (k p : Nat) : ℝ :=
  (confessedBurdenDoubled k p : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Definition with formal content given by the displayed type and body.


-/
noncomputable def confessionLinearNormalizer (k p : Nat) : ℝ :=
  (confessedBurdenDoubled (k + 1) p : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Definition with formal content given by the displayed type and body.
-/
noncomputable def totalConfessionLinearNormalizer (k w : Nat) : ℝ :=
  (totalConfessedBurdenDoubled (k + 1) w : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Definition with formal content given by the displayed type and body.

-/
def proofEntropyTotalSize
    (k i payloadSize wrapSize cStar : Nat) : Nat :=
  i * (wrapSize + payloadSize) + (k - i) + cStar

/-- Definition with formal content given by the displayed type and body.

-/
noncomputable def proofEntropyValue
    (k i payloadSize wrapSize cStar : Nat) : ℝ :=
  (i * payloadSize : ℝ) /
    (proofEntropyTotalSize k i payloadSize wrapSize cStar : ℝ)

@[simp] theorem confessionQuadraticInvariant_eq (k p : Nat) :
    confessionQuadraticInvariant k p
      = ((1 : ℝ) + 1 / ((k : ℝ) + 1)) * ((p : ℝ) / 2) := by
  unfold confessionQuadraticInvariant confessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

@[simp] theorem confessionLinearNormalizer_eq (k p : Nat) :
    confessionLinearNormalizer k p
      = (((1 : ℝ) + 2 / ((k : ℝ) + 1))
          * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((p : ℝ) / 2) := by
  unfold confessionLinearNormalizer confessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

@[simp] theorem totalConfessionLinearNormalizer_eq (k w : Nat) :
    totalConfessionLinearNormalizer k w
      = (((1 : ℝ) + 2 / ((k : ℝ) + 1))
          * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((w : ℝ) / 2) := by
  unfold totalConfessionLinearNormalizer totalConfessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem confession_quadratic_invariant_tendsto (p : Nat) :
    Filter.Tendsto (fun k : Nat => confessionQuadraticInvariant k p)
      Filter.atTop (nhds ((p : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          ((1 : ℝ) + 1 / ((k : ℝ) + 1)) * ((p : ℝ) / 2))
        Filter.atTop (nhds ((p : ℝ) / 2)) := by
    simpa using hone.mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (confessionQuadraticInvariant_eq k p).symm

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem confession_linear_asymptotic_tendsto (p : Nat) :
    Filter.Tendsto (fun k : Nat => confessionLinearNormalizer k p)
      Filter.atTop (nhds ((p : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htwozero :
      Filter.Tendsto (fun k : Nat => (2 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := (2 : ℝ))).mul hzero
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have htwo :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 2 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add htwozero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          (((1 : ℝ) + 2 / ((k : ℝ) + 1))
            * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((p : ℝ) / 2))
        Filter.atTop (nhds ((p : ℝ) / 2)) := by
    simpa [one_mul] using (htwo.mul hone).mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (confessionLinearNormalizer_eq k p).symm

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem confession_ratio_eventually_dominates
    (p N : Nat) (hp : 1 ≤ p) :
    ∃ K : Nat, ∀ k ≥ K,
      (N : ℝ) ≤ (confessedBurdenDoubled (k + 1) p : ℝ) / (2 * (k + 1 : ℝ)) := by
  refine ⟨2 * N, ?_⟩
  intro k hk
  have hk1 : 0 < (2 * (k + 1 : ℝ)) := by positivity
  apply (le_div_iff₀ hk1).2
  have hnat : 2 * (k + 1) * N ≤ confessedBurdenDoubled (k + 1) p := by
    unfold confessedBurdenDoubled
    have hpk : 2 * N ≤ p * (k + 2) := by
      nlinarith [hk, hp]
    have hkk : k + 1 ≤ k + 3 := by omega
    nlinarith
  simpa [mul_assoc, mul_left_comm, mul_comm] using (show (2 * (k + 1) * N : ℝ) ≤
      (confessedBurdenDoubled (k + 1) p : ℝ) by exact_mod_cast hnat)

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem total_confession_linear_asymptotic_tendsto (w : Nat) :
    Filter.Tendsto (fun k : Nat => totalConfessionLinearNormalizer k w)
      Filter.atTop (nhds ((w : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htwozero :
      Filter.Tendsto (fun k : Nat => (2 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := (2 : ℝ))).mul hzero
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have htwo :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 2 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add htwozero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          (((1 : ℝ) + 2 / ((k : ℝ) + 1))
            * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((w : ℝ) / 2))
        Filter.atTop (nhds ((w : ℝ) / 2)) := by
    simpa [one_mul] using (htwo.mul hone).mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (totalConfessionLinearNormalizer_eq k w).symm

@[simp] theorem proofEntropyValue_zero
    (k payloadSize wrapSize cStar : Nat) :
    proofEntropyValue k 0 payloadSize wrapSize cStar = 0 := by
  simp [proofEntropyValue]

/-- Definition with formal content given by the displayed type and body.
-/
def proofEntropyOverhead (k i wrapSize cStar : Nat) : Nat :=
  i * wrapSize + (k - i) + cStar

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem proof_entropy_tendsto_one
    (k i wrapSize cStar : Nat) (hi : 1 ≤ i) :
    Filter.Tendsto (fun payloadSize : Nat =>
      proofEntropyValue k i (payloadSize + 1) wrapSize cStar)
      Filter.atTop (nhds 1) := by
  let Cnat : Nat := proofEntropyOverhead k i wrapSize cStar
  let C : ℝ := Cnat
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, Cnat, proofEntropyOverhead]
    positivity
  have hzero :
      Filter.Tendsto (fun payloadSize : Nat => C / ((payloadSize : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    have hone :
        Filter.Tendsto (fun payloadSize : Nat => (1 : ℝ) / ((payloadSize : ℝ) + 1))
          Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [C, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := C)).mul hone
  have hgap :
      Filter.Tendsto
        (fun payloadSize : Nat =>
          C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun payloadSize => div_nonneg hC_nonneg (by positivity)) ?_ hzero
    intro payloadSize
    have hden_ge :
        ((payloadSize : ℝ) + 1)
          ≤ (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
      exact_mod_cast (show payloadSize + 1 ≤ proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar by
        unfold proofEntropyTotalSize
        nlinarith [hi, Nat.zero_le wrapSize, Nat.zero_le cStar, Nat.zero_le (k - i)])
    have hden_pos :
        0 < (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
      have hden_pos_nat :
          0 < proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar := by
        unfold proofEntropyTotalSize
        have : 1 ≤ i * (wrapSize + (payloadSize + 1)) := by
          nlinarith [hi, Nat.succ_le_succ (Nat.zero_le payloadSize)]
        omega
      exact_mod_cast hden_pos_nat
    have hrecip :
        (1 : ℝ) / (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ)
          ≤ (1 : ℝ) / (((payloadSize : ℝ) + 1) : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden_ge
    have hmul :=
      mul_le_mul_of_nonneg_left hrecip hC_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrewrite :
      (fun payloadSize : Nat =>
        proofEntropyValue k i (payloadSize + 1) wrapSize cStar)
        =ᶠ[Filter.atTop]
          (fun payloadSize : Nat =>
            1 - C /
              (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro payloadSize
    dsimp [C, Cnat, proofEntropyValue, proofEntropyOverhead]
    have hden_pos :
        (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) ≠ 0 := by
      have hden_pos_nat :
          0 < proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar := by
        unfold proofEntropyTotalSize
        have : 1 ≤ i * (wrapSize + (payloadSize + 1)) := by
          nlinarith [hi, Nat.succ_le_succ (Nat.zero_le payloadSize)]
        omega
      exact_mod_cast hden_pos_nat.ne'
    have hsplit_nat :
        proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar
          = i * (payloadSize + 1) + proofEntropyOverhead k i wrapSize cStar := by
      unfold proofEntropyTotalSize proofEntropyOverhead
      calc
        i * (wrapSize + (payloadSize + 1)) + (k - i) + cStar
          = i * wrapSize + i * (payloadSize + 1) + (k - i) + cStar := by ring_nf
        _ = i * (payloadSize + 1) + (i * wrapSize + (k - i) + cStar) := by ac_rfl
    have hnum_eq :
        (i * (payloadSize + 1) : ℝ)
          = (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) - C := by
      have hsplit_real :
          (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ)
            = (i * (payloadSize + 1) : ℝ) + (proofEntropyOverhead k i wrapSize cStar : ℝ) := by
        exact_mod_cast hsplit_nat
      dsimp [C, Cnat]
      nlinarith
    calc
      proofEntropyValue k i (payloadSize + 1) wrapSize cStar
          = ((proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) - C) /
              (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
              simp [proofEntropyValue, hnum_eq]
      _ = 1 - C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
            field_simp [hden_pos]
  have hsub :
      Filter.Tendsto
        (fun payloadSize : Nat =>
          1 - C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hgap
  simpa using hsub.congr' hrewrite.symm

/-- The displayed proposition follows from the stated hypotheses.




-/
theorem confession_dominance_product (k p : Nat) :
    confessedBurdenDoubled k p
      = (k + 1) * (k + 2) * p := rfl

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem confession_doubled_eq_product (k p : Nat) :
    confessedBurdenDoubled k p = (k + 1) * (k + 2) * p := rfl

/-- Definition with formal content given by the displayed type and body.
-/
def proofEntropyDenominator (k i wrapperCellWeight cStar : Nat) : Nat :=
  i * wrapperCellWeight + (k - i) + cStar

/-- Proof-entropy numerator at step `i`: `i · payloadSize`. -/
def proofEntropyNumerator (i payloadSize : Nat) : Nat := i * payloadSize

/-- Definition with formal content given by the displayed type and body.
-/
def ProofEntropyNonDecreasing
    (k payloadSize wrapperCellWeight cStar : Nat) : Prop :=
  ∀ i,
    proofEntropyNumerator i payloadSize
      * proofEntropyDenominator k (i + 1) wrapperCellWeight cStar
    ≤ proofEntropyNumerator (i + 1) payloadSize
      * proofEntropyDenominator k i wrapperCellWeight cStar

/-- The displayed proposition follows from the stated hypotheses.





-/
theorem proof_entropy_nondecreasing
    (k payloadSize wrapperCellWeight cStar : Nat) :
    ProofEntropyNonDecreasing k payloadSize wrapperCellWeight cStar := by
  intro i
  unfold proofEntropyNumerator proofEntropyDenominator
  by_cases hik : i + 1 ≤ k
  · -- Nontrivial regime: i + 1 ≤ k, so k - (i+1) = (k - i) - 1 and k - i ≥ 1.
    have hkI : k - i = (k - (i + 1)) + 1 := by omega
    set m := k - (i + 1) with hm
    rw [hkI]
    nlinarith [Nat.zero_le m, Nat.zero_le wrapperCellWeight,
               Nat.zero_le payloadSize, Nat.zero_le i, Nat.zero_le cStar]
  · --
    have h1 : k - i = 0 := by omega
    have h2 : k - (i + 1) = 0 := by omega
    rw [h1, h2]
    nlinarith [Nat.zero_le wrapperCellWeight, Nat.zero_le payloadSize,
               Nat.zero_le i, Nat.zero_le cStar]

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
