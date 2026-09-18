import OperatorKO7.Meta.SafeStep.BranchEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# General real-valued branch-entropy functional

This module is the general companion to `BranchEntropy`. The paper defines branch
entropy as `log2` of the number of distinct terminal verdicts a source admits;
`BranchEntropy.verdictBits` only mechanizes the *binary* specialization (one
verdict gives `0`, two or more give `1`). Here we mechanize the general
real-valued functional, the Shannon entropy of `n` equiprobable terminal
verdicts, and tie it back to the binary `verdictBits` at the values that occur at
a non-left-linear critical pair.

## Honesty / trust surface

This file is part of the checked surface. It contains no `sorry`, no `admit`, no
new `axiom`/`constant`, no `native_decide`/`bv_decide`, no `@[csimp]`/`extern`/
`implemented_by`, no `unsafe`/`partial`/`opaque`. `set_option autoImplicit false`
is active. Every headline theorem carries a trailing `#print axioms`, and each
reduces to a subset of `{propext, Classical.choice, Quot.sound}` (the `Real`
development is classical and noncomputable; that is the *only* trust expansion,
and it is the standard Mathlib analysis base, not a project axiom).

## What it adds (and what it does not)

`branchEntropy n := Real.logb 2 n` is a genuine real-valued functional, not a
two-point table. The headline facts are real `Real.logb` theorems:

* `branchEntropy_one : branchEntropy 1 = 0` (logb of `1`);
* `branchEntropy_two : branchEntropy 2 = 1` (logb base `2` of `2`);
* `branchEntropy_mono` : monotone in the verdict count (logb monotonicity for
  base `> 1`, with the positivity side conditions discharged);
* `branchEntropy_collapse_one_bit_real : branchEntropy 2 - branchEntropy 1 = 1`,
  the one-bit collapse in the general functional.

It does *not* re-prove the eqW confluence breaker; that lives in
`EqWVoidAnomaly` and is re-exported through `BranchEntropy`. The corollary
`eqW_void_void_branchEntropyGeneral_collapse` connects the concrete breaker to
this functional: the breaker's two unjoinable verdicts realize the `n = 2`
instance (`branchEntropy 2 = 1` bit) and the licensed single verdict realizes
the `n = 1` instance (`branchEntropy 1 = 0` bits). Non-vacuity therefore comes
from the breaker, not from an empty hypothesis.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.SafeStep.BranchEntropyGeneral

open OperatorKO7.Meta.SafeStep.BranchEntropy

/-- General branch entropy in bits: the Shannon entropy of `n` equiprobable
terminal verdicts, `log₂ n`. This is the full real-valued functional the paper
states; `BranchEntropy.verdictBits` is its `{0,1}`-valued binary specialization.
`noncomputable` because `Real.logb` is. -/
def branchEntropy (n : Nat) : Real := Real.logb 2 (n : Real)

/-- One verdict carries zero branch entropy: `log₂ 1 = 0`. A genuine `Real.logb`
evaluation, not a definitional rewrite. -/
theorem branchEntropy_one : branchEntropy 1 = 0 := by
  unfold branchEntropy
  rw [Nat.cast_one, Real.logb_one]

/-- Two verdicts carry exactly one bit of branch entropy: `log₂ 2 = 1`. Uses
`Real.logb_self_eq_one` for base `2 > 1`. -/
theorem branchEntropy_two : branchEntropy 2 = 1 := by
  unfold branchEntropy
  have h2 : ((2 : Nat) : Real) = (2 : Real) := by norm_num
  rw [h2, Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]

/-- Monotonicity of the general functional in the number of verdicts: for
`1 ≤ n ≤ m`, `branchEntropy n ≤ branchEntropy m`. This is `Real.logb`
monotonicity for base `2 > 1`; the positivity side condition `0 < (n : Real)`
is discharged from `1 ≤ n`, and the cast inequality from `n ≤ m`. -/
theorem branchEntropy_mono {n m : Nat} (hn : 1 ≤ n) (hnm : n ≤ m) :
    branchEntropy n ≤ branchEntropy m := by
  unfold branchEntropy
  have hxpos : (0 : Real) < (n : Real) := by
    have : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    linarith
  have hxy : (n : Real) ≤ (m : Real) := by exact_mod_cast hnm
  exact Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hxpos hxy

/-- The one-bit collapse in the *general* real-valued functional: going from two
admissible verdicts to one licensed verdict drops branch entropy by exactly one
bit. `branchEntropy 2 - branchEntropy 1 = 1`. This is the real-analytic analogue
of `BranchEntropy.branchEntropy_collapse_one_bit` (which is the integer
`verdictBits 2 - verdictBits 1 = 1`). -/
theorem branchEntropy_collapse_one_bit_real :
    branchEntropy 2 - branchEntropy 1 = 1 := by
  rw [branchEntropy_two, branchEntropy_one]
  norm_num

/-- Bridge: the general real functional agrees with the integer binary
specialization `verdictBits` at the two values that occur at a non-left-linear
critical pair, `n ∈ {1, 2}`. The left-hand sides are `Real.logb` values; the
right-hand sides are the `Nat`-valued `verdictBits` cast into `Real`. -/
theorem branchEntropy_agrees_verdictBits :
    (branchEntropy 1 = (verdictBits 1 : Real)) ∧
    (branchEntropy 2 = (verdictBits 2 : Real)) := by
  refine ⟨?_, ?_⟩
  · rw [branchEntropy_one, verdictBits_one, Nat.cast_zero]
  · rw [branchEntropy_two, verdictBits_two, Nat.cast_one]

/-- The general-functional collapse measured at the concrete confluence breaker.

The eqW(void,void) breaker (re-exported from `EqWVoidAnomaly` through
`BranchEntropy`) is a genuine two-verdict source: it carries the critical pair
`CriticalPairAt (eqW void void) void (integrate (merge void void))`. Those two
unjoinable verdicts realize the `n = 2` instance of the general functional, so
`branchEntropy 2 = 1` bit; the licensed layer collapses to the single verdict,
the `n = 1` instance, so `branchEntropy 1 = 0` bits. The net cost of the
confluence-preserving move is `branchEntropy 2 - branchEntropy 1 = 1` bit.

This packages the non-vacuity of the collapse: the witness is the breaker, not an
empty or contradictory hypothesis. The breaker itself is *not* re-proved here. -/
theorem eqW_void_void_branchEntropyGeneral_collapse :
    CriticalPairAt (eqW void void) void (integrate (merge void void)) ∧
    branchEntropy 2 = 1 ∧
    branchEntropy 1 = 0 ∧
    branchEntropy 2 - branchEntropy 1 = 1 :=
  ⟨local_confluence_fails_at_eqW_void_void,
   branchEntropy_two,
   branchEntropy_one,
   branchEntropy_collapse_one_bit_real⟩

-- Headline axiom inventories. Each must be a subset of
-- {propext, Classical.choice, Quot.sound}.
#print axioms branchEntropy_one
#print axioms branchEntropy_two
#print axioms branchEntropy_mono
#print axioms branchEntropy_collapse_one_bit_real
#print axioms branchEntropy_agrees_verdictBits
#print axioms eqW_void_void_branchEntropyGeneral_collapse

-- Headline types, for the audit record.
#check @branchEntropy_one
#check @branchEntropy_two
#check @branchEntropy_mono
#check @branchEntropy_collapse_one_bit_real
#check @branchEntropy_agrees_verdictBits
#check @eqW_void_void_branchEntropyGeneral_collapse

end OperatorKO7.Meta.SafeStep.BranchEntropyGeneral

end
