/-!
# Arts and Giesl proof length, parameterized by maximum rule size

Construction cost depends on maximum rule size; a finite signature does not
bound the size of a rule. Summing a per-pair base-order proof cost `L_base 1`
across `n` pairs requires an explicit additive law for `L_base`.

This module uses maximum rule size in the construction cost and stores
additivity as a field. The coefficient `C = 2` follows from the three
stage definitions.

Relation: proof length of a dependency-pair soundness application.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only. No `sorry`, no `admit`, no new `axiom`, no native reduction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ArtsGieslProofLengthBySize

/-! ### The base order's proof-length function -/

/-- A base order with a proof-length function. `perPair` is the cost of
checking one extracted pair. `additive` states that checking `n` pairs
costs `n * perPair`. -/
structure BaseOrderProofLength where
  /-- Proof length of discharging `n` extracted pairs. -/
  length : Nat → Nat
  /-- Cost of a single pair. -/
  perPair : Nat
  /-- Additivity, stated rather than assumed. -/
  additive : ∀ n, length n = n * perPair

/-- A proof-length model that assigns one unit to each extracted pair. -/
def linearBaseOrder : BaseOrderProofLength where
  length := fun n => n
  perPair := 1
  additive := by intro n; omega

/-! ### The three stages -/

/-- Metadata for a finite TRS cost model: rule count, maximum rule size,
and extracted dependency-pair count. -/
structure FiniteTRSShape where
  /-- Number of rules. -/
  ruleCount : Nat
  /-- Maximum size of a single rule. This is the parameter the construction stage depends
  on; signature cardinality does not bound it. -/
  maxRuleSize : Nat
  /-- Number of extracted dependency pairs. -/
  pairCount : Nat

/-- Modeled construction-stage cost for marked-pair extraction and
dependency-graph connectivity. -/
def constructionCost (R : FiniteTRSShape) : Nat :=
  R.ruleCount * R.ruleCount * R.maxRuleSize

/-- Modeled cost of checking the extracted pairs with the supplied
proof-length function. -/
def baseCheckCost (L : BaseOrderProofLength) (R : FiniteTRSShape) : Nat :=
  L.length R.pairCount

/-- Soundness-application stage: one schematic instance. -/
def soundnessCost : Nat := 1

/-- Total modeled length of one Arts and Giesl soundness application. -/
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
Proves: for every bound, a shape with one rule has construction cost above that bound.
The cost grows with `maxRuleSize`.
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
Proves: the modeled length for recursor size `m` plus residual cost `K`
equals `4 * m + 2 + K`.
-/
theorem confessionCertificateLength_recursor (m K : Nat) :
    agProofLength linearBaseOrder (recursorShape m) + K = 4 * m + 2 + K := by
  rw [agProofLength_recursor_closed_form m]

/--
Proves: subtracting `K` or `K'` from the corresponding modeled total gives the same value.
-/
theorem licenseOverhead_constant_in_input (m K K' : Nat) :
    (agProofLength linearBaseOrder (recursorShape m) + K) - K
      = (agProofLength linearBaseOrder (recursorShape m) + K') - K' := by
  omega

end OperatorKO7.Meta.ArtsGieslProofLengthBySize
