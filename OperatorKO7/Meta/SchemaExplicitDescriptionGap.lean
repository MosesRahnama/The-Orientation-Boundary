import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

/-!
# The explicit-description gap, with the threshold that makes it positive

The upstream identity
`M i - L_exp i = i * (β + γ) - size₂ (i + 1) - c₀`
is a rearrangement of the two definitions and says nothing about the sign of the
difference. The manuscript reads it as "the repeated-carrier representation exceeds the
explicit description by a linear term", which fails at small indices: at `i = 0` the
repeated-carrier envelope is `β + γ` while the explicit description is
`β + γ + size₂ 1 + c₀`, which is strictly larger.

This module supplies the threshold. `explicitDescription_gap_positive` gives an explicit
sufficient condition, `explicitDescription_gap_fails_at_zero` shows the unqualified reading
is false, and `explicitDescription_gap_threshold_is_attained` witnesses the hypothesis.

Relation: arithmetic on the carrier envelope and the explicit description length.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.SchemaExplicitDescriptionGap

/-- The binary-length code for the step index: `size₂ n` bits encode `n`. -/
def size2 (n : Nat) : Nat := Nat.log 2 n + 1

/-- The repeated-carrier envelope at stage `i`: `i + 1` cells of weight `β + γ`. -/
def carrierEnvelope (beta gamma i : Nat) : Nat := (i + 1) * (beta + gamma)

/-- The explicit description length: one seed, one wrapper symbol, a binary index code,
and fixed glue overhead. -/
def explicitDescription (beta gamma c0 i : Nat) : Nat :=
  beta + gamma + size2 (i + 1) + c0

/-! ### The identity, restated -/

/--
Proves: the upstream rearrangement, with both sides in additive form so that the identity
holds in `Nat` without truncated subtraction.
-/
theorem carrierEnvelope_explicitDescription_identity
    (beta gamma c0 i : Nat) :
    i * (beta + gamma) + explicitDescription beta gamma c0 i
      = carrierEnvelope beta gamma i + size2 (i + 1) + c0 := by
  simp only [carrierEnvelope, explicitDescription]
  ring

/-! ### The unqualified reading is false -/

/--
Proves: at stage zero the explicit description is strictly longer than the repeated-carrier
envelope, so the gap statement needs a threshold rather than holding for every index.
-/
theorem explicitDescription_gap_fails_at_zero (beta gamma c0 : Nat) :
    carrierEnvelope beta gamma 0 < explicitDescription beta gamma c0 0 := by
  simp only [carrierEnvelope, explicitDescription, size2]
  omega

/-! ### The threshold -/

/-- Helper: `k + 2 ≤ 2 ^ k` for `2 ≤ k`. -/
private theorem add_two_le_two_pow (k : Nat) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 2 with h | h
      · have hn1 : n = 1 := by omega
        subst hn1
        norm_num
      · have hn := ih h
        have hsplit : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
          rw [pow_succ]; omega
        omega

/--
Proves: the binary index code costs at most `i` bits once `2 ≤ i`.
-/
theorem size2_succ_le (i : Nat) (hi : 2 ≤ i) : size2 (i + 1) ≤ i := by
  rcases Nat.lt_or_ge (Nat.log 2 (i + 1)) 2 with h | h
  · simp only [size2]; omega
  · have hpow : 2 ^ Nat.log 2 (i + 1) ≤ i + 1 :=
      Nat.pow_log_le_self 2 (by omega)
    have hbig := add_two_le_two_pow (Nat.log 2 (i + 1)) h
    simp only [size2]
    omega

/--
Intent: **the gap theorem with its threshold**. Once the cell weight is at least two, the
index is at least two, and the glue overhead is below the index, the repeated-carrier
envelope strictly exceeds the explicit description.

Relation: arithmetic.
Trust: kernel-only.
Non-vacuity witness: `explicitDescription_gap_threshold_is_attained`.
-/
theorem explicitDescription_gap_positive
    (beta gamma c0 i : Nat)
    (hweight : 2 ≤ beta + gamma)
    (hindex : 2 ≤ i)
    (hglue : c0 < i) :
    explicitDescription beta gamma c0 i < carrierEnvelope beta gamma i := by
  have hcode : size2 (i + 1) ≤ i := size2_succ_le i hindex
  have hmul : 2 * i ≤ i * (beta + gamma) := by
    calc 2 * i = i * 2 := by ring
    _ ≤ i * (beta + gamma) := Nat.mul_le_mul_left i hweight
  simp only [carrierEnvelope, explicitDescription]
  have hexpand : (i + 1) * (beta + gamma) = i * (beta + gamma) + (beta + gamma) := by
    ring
  omega

/--
Proves: the hypotheses of `explicitDescription_gap_positive` are satisfiable, so the
threshold statement is non-vacuous (Gate R5).
-/
theorem explicitDescription_gap_threshold_is_attained :
    explicitDescription 1 1 0 4 < carrierEnvelope 1 1 4 :=
  explicitDescription_gap_positive 1 1 0 4 (by norm_num) (by norm_num) (by norm_num)

/--
Proves: the gap grows without bound above the threshold, which is the linear-growth reading
the manuscript wants, now stated where it is true.
-/
theorem explicitDescription_gap_grows
    (beta gamma c0 i : Nat)
    (hweight : 2 ≤ beta + gamma)
    (hindex : 2 ≤ i)
    (hglue : c0 < i) :
    explicitDescription beta gamma c0 i + (i - c0) ≤ carrierEnvelope beta gamma i := by
  have hcode : size2 (i + 1) ≤ i := size2_succ_le i hindex
  have hmul : 2 * i ≤ i * (beta + gamma) := by
    calc 2 * i = i * 2 := by ring
    _ ≤ i * (beta + gamma) := Nat.mul_le_mul_left i hweight
  simp only [carrierEnvelope, explicitDescription]
  have hexpand : (i + 1) * (beta + gamma) = i * (beta + gamma) + (beta + gamma) := by
    ring
  omega

end OperatorKO7.Meta.SchemaExplicitDescriptionGap
