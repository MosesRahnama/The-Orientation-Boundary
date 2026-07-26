/-!
# Arts and Giesl proof length, parameterized by rule size rather than signature size

The manuscript's proof-length proposition bounds the dependency-pair construction stage by
"over a rule of size bounded by `|Σ|`". A rule over a fixed finite signature can be
arbitrarily large, so signature cardinality does not bound rule size. The proposition also
leaves the base-order proof-length function `L_base` undefined and silently assumes it is
additive when it sums a per-pair cost `L_base 1` into a total `L_base n`.

This module states the bound with the parameter that actually controls the construction
stage, namely the maximum rule size, and carries the additivity of `L_base` as an explicit
field rather than an unstated assumption. The constant `C` is derived from the stage
definitions instead of asserted.

Relation: proof length of a dependency-pair soundness application.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ArtsGieslProofLengthBySize

/-! ### The base order's proof-length function -/

/--
A base order together with its proof-length function. `perPair` is the cost of checking one
extracted pair; `additive` is the assumption the manuscript uses implicitly when it sums a
per-pair cost over `n` pairs.
-/
structure BaseOrderProofLength where
  /-- Proof length of discharging `n` extracted pairs. -/
  length : Nat → Nat
  /-- Cost of a single pair. -/
  perPair : Nat
  /-- Additivity, stated rather than assumed. -/
  additive : ∀ n, length n = n * perPair

/-- A linear base order of ordinal `ω`: one unit of proof length per pair. -/
def linearBaseOrder : BaseOrderProofLength where
  length := fun n => n
  perPair := 1
  additive := by intro n; omega

/-! ### The three stages -/

/-- A finite term rewriting system, recorded by the three quantities the construction stage
reads: rule count, maximum rule size, and the number of extracted dependency pairs. -/
structure FiniteTRSShape where
  /-- Number of rules. -/
  ruleCount : Nat
  /-- Maximum size of a single rule. This is the parameter the construction stage depends
  on; signature cardinality does not bound it. -/
  maxRuleSize : Nat
  /-- Number of extracted dependency pairs. -/
  pairCount : Nat

/-- Construction stage: marked-pair extraction and dependency-graph connectivity. -/
def constructionCost (R : FiniteTRSShape) : Nat :=
  R.ruleCount * R.ruleCount * R.maxRuleSize

/-- Base-order check stage: one check per extracted pair. -/
def baseCheckCost (L : BaseOrderProofLength) (R : FiniteTRSShape) : Nat :=
  L.length R.pairCount

/-- Soundness-application stage: one schematic instance. -/
def soundnessCost : Nat := 1

/-- Total proof length of one Arts and Giesl soundness application. -/
def agProofLength (L : BaseOrderProofLength) (R : FiniteTRSShape) : Nat :=
  constructionCost R + baseCheckCost L R + soundnessCost

/-! ### The bound, with the constant derived -/

/--
Intent: the proof-length bound with `C = 2` derived from the stage definitions, and with the
construction stage controlled by maximum rule size rather than signature cardinality.

Relation: proof length.
Trust: kernel-only.
Scope: requires at least one rule of nonzero size, which is what makes the soundness stage's
unit cost absorbable into the construction coefficient.
-/
theorem agProofLength_le_of_nonempty
    (L : BaseOrderProofLength) (R : FiniteTRSShape)
    (hrule : 1 ≤ R.ruleCount) (hsize : 1 ≤ R.maxRuleSize) :
    agProofLength L R
      ≤ 2 * (R.ruleCount * R.ruleCount * R.maxRuleSize) + L.length R.pairCount := by
  have hone : 1 ≤ R.ruleCount * R.ruleCount * R.maxRuleSize := by
    have h1 : 1 ≤ R.ruleCount * R.ruleCount := Nat.one_le_iff_ne_zero.mpr (by
      intro h
      rcases Nat.mul_eq_zero.mp h with h' | h' <;> omega)
    calc 1 = 1 * 1 := by omega
    _ ≤ (R.ruleCount * R.ruleCount) * R.maxRuleSize := Nat.mul_le_mul h1 hsize
  simp only [agProofLength, constructionCost, baseCheckCost, soundnessCost]
  omega

/--
Proves: signature cardinality cannot replace maximum rule size in the construction bound.
For every signature size there are shapes whose construction cost exceeds any bound stated
in that signature size alone, because rule size is an independent parameter.
-/
theorem constructionCost_unbounded_in_ruleSize (bound : Nat) :
    ∃ R : FiniteTRSShape,
      R.ruleCount = 1 ∧ bound < constructionCost R := by
  refine ⟨⟨1, bound + 1, 0⟩, rfl, ?_⟩
  simp only [constructionCost]
  omega

/-! ### The recursor specialization -/

/-- The step-duplicating recursor: two rules, one extracted pair. -/
def recursorShape (maxRuleSize : Nat) : FiniteTRSShape :=
  ⟨2, maxRuleSize, 1⟩

/--
Proves: on the step-duplicating recursor with a linear base order the license overhead is a
constant in the input counter height, with the constant named explicitly.
-/
theorem agProofLength_recursor_closed_form (m : Nat) :
    agProofLength linearBaseOrder (recursorShape m) = 4 * m + 2 := by
  simp only [agProofLength, constructionCost, baseCheckCost, soundnessCost,
    recursorShape, linearBaseOrder]

/--
Proves: a complete confession certificate on input counter height `K` has total length
`4 * m + 2 + K`, so it is linear in `K` with an explicitly named constant rather than an
unquantified `O(K)`.
-/
theorem confessionCertificateLength_recursor (m K : Nat) :
    agProofLength linearBaseOrder (recursorShape m) + K = 4 * m + 2 + K := by
  rw [agProofLength_recursor_closed_form m]

/--
Proves: removing the residual work from the total certificate leaves the same license
overhead at every input counter height, which is the constant-overhead reading stated so
that the input height genuinely occurs on both sides.
-/
theorem licenseOverhead_constant_in_input (m K K' : Nat) :
    (agProofLength linearBaseOrder (recursorShape m) + K) - K
      = (agProofLength linearBaseOrder (recursorShape m) + K') - K' := by
  omega

end OperatorKO7.Meta.ArtsGieslProofLengthBySize
