import OperatorKO7.Meta.SafeStepCtx_Complexity_LowerBound
import OperatorKO7.Meta.SafeStep_Complexity

/-!
# Exponential lower family for unguarded `StepCtxFull`

The guarded family in `SafeStepCtx_Complexity_LowerBound` is a sub-relation of
full contextual `Step`. This module lifts that family, solves its exact length
recurrence, and bounds every full-context derivation by an exponential in the
structural source size.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.PolyInterpretation

namespace MetaSN_KO7

/-- Guarded root steps are kernel steps. -/
theorem safeStep_to_step {a b : Trace} (h : SafeStep a b) : Step a b := by
  cases h with
  | R_int_delta _ => exact Step.R_int_delta _
  | R_merge_void_left _ _ => exact Step.R_merge_void_left _
  | R_merge_void_right _ _ => exact Step.R_merge_void_right _
  | R_merge_cancel _ _ _ => exact Step.R_merge_cancel _
  | R_rec_zero _ _ _ => exact Step.R_rec_zero _ _
  | R_rec_succ _ _ _ => exact Step.R_rec_succ _ _ _
  | R_eq_refl _ _ => exact Step.R_eq_refl _
  | R_eq_diff _ _ _ => exact Step.R_eq_diff _ _

/-- Guarded contextual steps are full contextual steps. -/
theorem safeStepCtx_to_stepCtxFull {a b : Trace} (h : SafeStepCtx a b) :
    StepCtxFull a b := by
  induction h with
  | root hs => exact StepCtxFull.root (safeStep_to_step hs)
  | integrate _ ih => exact StepCtxFull.integrate ih
  | mergeL _ ih => exact StepCtxFull.mergeL ih
  | mergeR _ ih => exact StepCtxFull.mergeR ih
  | appL _ ih => exact StepCtxFull.appL ih
  | appR _ ih => exact StepCtxFull.appR ih
  | recB _ ih => exact StepCtxFull.recB ih
  | recS _ ih => exact StepCtxFull.recS ih
  | recN _ ih => exact StepCtxFull.recN ih

/-- Counted guarded chains lift to counted full-context chains of the same length. -/
theorem safeStepCtxPow_to_stepCtxFullPow :
    ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u → StepCtxFullPow t n u
  | 0, t, u, h => by
      cases h
      exact StepCtxFullPow.refl t
  | n + 1, t, u, ⟨v, htv, hvu⟩ =>
      StepCtxFullPow.tail (safeStepCtx_to_stepCtxFull htv)
        (safeStepCtxPow_to_stepCtxFullPow hvu)

/-- Nested recursor family: linear source size, `StepCtxFull` length at least `2^n`. -/
theorem stepCtxFull_has_singleExponential_lower_family (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      StepCtxFullPow t m u ∧
      2 ^ n ≤ m := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_, ?_⟩
  · exact termSize_ctxLowerFamily n
  · exact safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n)
  · exact two_pow_le_ctxLowerLen n

/-- Closed form of the exact lower-family derivation length. -/
@[simp] theorem ctxLowerLen_eq_two_pow_sub_three (n : Nat) :
    ctxLowerLen n = 2 ^ (n + 2) - 3 := by
  induction n with
  | zero => simp [ctxLowerLen]
  | succ n ih =>
      have hpow : 4 ≤ 2 ^ (n + 2) := by
        calc
          4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [ctxLowerLen, ih]
      calc
        2 * (2 ^ (n + 2) - 3) + 3 = 2 * 2 ^ (n + 2) - 3 := by omega
        _ = 2 ^ (n + 3) - 3 := by
          simp [pow_succ, Nat.mul_comm]

/-- The polynomial witness is bounded by a fixed-base exponential in structural
term size. -/
theorem W_le_eight_pow_termSize : ∀ t : Trace, W t ≤ 8 ^ termSize t
  | void => by decide
  | delta t => by
      have ih := W_le_eight_pow_termSize t
      have hp : 1 ≤ 8 ^ termSize t := Nat.one_le_pow _ _ (by decide)
      have h : W t + 1 ≤ 8 * (8 ^ termSize t) := by omega
      simpa [W, termSize, pow_add, Nat.mul_comm] using h
  | integrate t => by
      have ih := W_le_eight_pow_termSize t
      have hp : 1 ≤ 8 ^ termSize t := Nat.one_le_pow _ _ (by decide)
      have h : W t + 1 ≤ 8 * (8 ^ termSize t) := by omega
      simpa [W, termSize, pow_add, Nat.mul_comm] using h
  | merge a b => by
      have iha := W_le_eight_pow_termSize a
      have ihb := W_le_eight_pow_termSize b
      let A := 8 ^ termSize a
      let B := 8 ^ termSize b
      have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
      have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
      have hsmall : W a + W b + 1 ≤ A + B + 1 := by omega
      have hbig : A + B + 1 ≤ 8 * A * B := by nlinarith
      have h := le_trans hsmall hbig
      simpa [A, B, W, termSize, pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using h
  | app a b => by
      have iha := W_le_eight_pow_termSize a
      have ihb := W_le_eight_pow_termSize b
      let A := 8 ^ termSize a
      let B := 8 ^ termSize b
      have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
      have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
      have hsmall : W a + W b + 1 ≤ A + B + 1 := by omega
      have hbig : A + B + 1 ≤ 8 * A * B := by nlinarith
      have h := le_trans hsmall hbig
      simpa [A, B, W, termSize, pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using h
  | recΔ b s n => by
      have ihb := W_le_eight_pow_termSize b
      have ihs := W_le_eight_pow_termSize s
      have ihn := W_le_eight_pow_termSize n
      let B := 8 ^ termSize b
      let S' := 8 ^ termSize s
      let N := 8 ^ termSize n
      have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
      have hS : 1 ≤ S' := Nat.one_le_pow _ _ (by decide)
      have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
      have hleft : W n + 1 ≤ N + 1 := by omega
      have hright : W s + W b + 1 ≤ S' + B + 1 := by omega
      have hsmall : (W n + 1) * (W s + W b + 1) ≤ (N + 1) * (S' + B + 1) :=
        Nat.mul_le_mul hleft hright
      have hbig : (N + 1) * (S' + B + 1) ≤ 8 * B * S' * N := by
        have hN2 : N + 1 ≤ 2 * N := by omega
        have hSle : S' ≤ S' * B := by
          simpa using Nat.mul_le_mul_left S' hB
        have hBle : B ≤ S' * B := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right B hS
        have hOne : 1 ≤ S' * B := le_trans hS hSle
        have hSB : S' + B + 1 ≤ 3 * (S' * B) := by omega
        have hmul := Nat.mul_le_mul hN2 hSB
        have hscale : 6 * (B * S' * N) ≤ 8 * (B * S' * N) :=
          Nat.mul_le_mul_right (B * S' * N) (by decide)
        calc
          (N + 1) * (S' + B + 1) ≤ (2 * N) * (3 * (S' * B)) := hmul
          _ = 6 * (B * S' * N) := by ac_rfl
          _ ≤ 8 * (B * S' * N) := hscale
          _ = 8 * B * S' * N := by ac_rfl
      have h := le_trans hsmall hbig
      have hpow : 8 ^ termSize (recΔ b s n) = 8 * B * S' * N := by
        simp [B, S', N, termSize, pow_add, Nat.mul_assoc]
      change (W n + 1) * (W s + W b + 1) ≤ 8 ^ termSize (recΔ b s n)
      rw [hpow]
      exact h
  | eqW a b => by
      have iha := W_le_eight_pow_termSize a
      have ihb := W_le_eight_pow_termSize b
      let A := 8 ^ termSize a
      let B := 8 ^ termSize b
      have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
      have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
      have hsmall : W a + W b + 3 ≤ A + B + 3 := by omega
      have hbig : A + B + 3 ≤ 8 * A * B := by nlinarith
      have h := le_trans hsmall hbig
      simpa [A, B, W, termSize, pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using h

/-- Every full-context derivation has single-exponential length in the source
term size. -/
theorem stepCtxFullPow_length_lt_eight_pow_termSize
    {t u : Trace} {m : Nat} (h : StepCtxFullPow t m u) :
    m < 8 ^ termSize t :=
  lt_of_lt_of_le (stepCtxFullPow_length_lt_W h) (W_le_eight_pow_termSize t)

/-- Compatibility statement pairing the lower family with the polynomial
weight bound.  The global size-exponential upper bound is stated below. -/
theorem step_derivation_length_singleExponential_tight (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      StepCtxFullPow t m u ∧
      2 ^ n ≤ m ∧
      m < W t := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_, ?_, ?_⟩
  · exact termSize_ctxLowerFamily n
  · exact safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n)
  · exact two_pow_le_ctxLowerLen n
  · exact stepCtxFullPow_length_lt_W
      (safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n))

/-- Exact exponential sandwich: a linear-size source realizes the closed-form
lower-family length, and that length lies below the universal exponential
upper bound. -/
theorem step_derivational_complexity_singleExponential_sandwich (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      m = 2 ^ (n + 2) - 3 ∧
      StepCtxFullPow t m u ∧
      2 ^ n ≤ m ∧
      m < 8 ^ termSize t := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n,
    termSize_ctxLowerFamily n, ctxLowerLen_eq_two_pow_sub_three n, ?_,
    two_pow_le_ctxLowerLen n, ?_⟩
  · exact safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n)
  · exact stepCtxFullPow_length_lt_eight_pow_termSize
      (safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n))

private theorem add8_gap (C : Nat) : 10 * C + 48 < 2 ^ (C + 8) := by
  induction C with
  | zero => decide
  | succ C ih =>
      have hL : 10 * (C + 1) + 48 = 10 * C + 58 := by omega
      have hstep : 10 * C + 58 < 2 * (10 * C + 48) := by omega
      have hmul : 2 * (10 * C + 48) < 2 * 2 ^ (C + 8) :=
        Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 2)
      have hpow : 2 * 2 ^ (C + 8) = 2 ^ (C + 9) := by
        rw [Nat.mul_comm, ← pow_succ]
      have hidx : C + 1 + 8 = C + 9 := by omega
      rw [hL, hidx, ← hpow]
      exact lt_trans hstep hmul

private theorem linear_lt_two_pow (C : Nat) :
    C * (5 * (C + 8) + 3) < 2 ^ (C + 8) := by
  induction C with
  | zero => decide
  | succ C ih =>
      have hcoeff1 : 5 * (C + 9) + 3 = 5 * C + 48 := by omega
      have hcoeff0 : 5 * (C + 8) + 3 = 5 * C + 43 := by omega
      have hshift : C + 1 + 8 = C + 9 := by
        rw [Nat.add_assoc]
      have hL :
          (C + 1) * (5 * (C + 1 + 8) + 3)
            = C * (5 * (C + 8) + 3) + (10 * C + 48) := by
        have hmul :
            C * (5 * C + 48) = C * (5 * C + 43) + 5 * C := by
          have h48 : (48 : Nat) = 43 + 5 := rfl
          calc
            C * (5 * C + 48)
                = C * (5 * C) + C * 48 := Nat.mul_add _ _ _
            _ = C * (5 * C) + C * (43 + 5) := by rw [h48]
            _ = C * (5 * C) + (C * 43 + C * 5) := by rw [Nat.mul_add]
            _ = C * (5 * C) + C * 43 + C * 5 := by rw [← Nat.add_assoc]
            _ = C * (5 * C + 43) + C * 5 := by rw [← Nat.mul_add]
            _ = C * (5 * C + 43) + 5 * C := by rw [Nat.mul_comm C 5]
        calc
          (C + 1) * (5 * (C + 1 + 8) + 3)
              = (C + 1) * (5 * (C + 9) + 3) := by rw [hshift]
          _ = (C + 1) * (5 * C + 48) := by rw [hcoeff1]
          _ = C * (5 * C + 48) + (5 * C + 48) := Nat.succ_mul _ _
          _ = C * (5 * C + 43) + 5 * C + (5 * C + 48) := by
                rw [hmul, Nat.add_assoc]
          _ = C * (5 * (C + 8) + 3) + (10 * C + 48) := by
                rw [hcoeff0]
                omega
      have hsum :
          C * (5 * (C + 8) + 3) + (10 * C + 48)
            < 2 ^ (C + 8) + 2 ^ (C + 8) :=
        Nat.add_lt_add ih (add8_gap C)
      have htwo : 2 ^ (C + 8) + 2 ^ (C + 8) = 2 ^ (C + 9) := by
        have : 2 ^ (C + 8) + 2 ^ (C + 8) = 2 * 2 ^ (C + 8) :=
          (Nat.two_mul _).symm
        rw [this, Nat.mul_comm, ← pow_succ]
      have hidx : C + 1 + 8 = C + 9 := by omega
      rw [hidx]
      calc
        (C + 1) * (5 * (C + 1 + 8) + 3)
            = C * (5 * (C + 8) + 3) + (10 * C + 48) := hL
        _ < 2 ^ (C + 9) := by
            rw [← htwo]
            exact hsum

/-- No linear-in-size bound covers every `StepCtxFull` derivation length. -/
theorem step_not_linear_derivational_complexity (C : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      StepCtxFullPow t m u ∧ C * termSize t < m := by
  let n := C + 8
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_⟩
  · exact safeStepCtxPow_to_stepCtxFullPow (ctxLowerFamily_pow_nf n)
  · have hsz : termSize (ctxLowerFamily n) = 5 * n + 3 := termSize_ctxLowerFamily n
    have hlow : 2 ^ n ≤ ctxLowerLen n := two_pow_le_ctxLowerLen n
    have hlin : C * (5 * n + 3) < 2 ^ n := by
      simpa [n] using linear_lt_two_pow C
    calc
      C * termSize (ctxLowerFamily n) = C * (5 * n + 3) := by rw [hsz]
      _ < 2 ^ n := hlin
      _ ≤ ctxLowerLen n := hlow

end MetaSN_KO7
