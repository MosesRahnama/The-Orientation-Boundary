import OperatorKO7.Meta.UUET.DualBoundaryUncertaintyFunctional
import OperatorKO7.Meta.UUET.BornBranchLedger

set_option autoImplicit false

/-!
# UUET finite entanglement-magnitude carrier (U-57)

This module closes the U-50 next-quant backlog item: it gives the dual-boundary
picture a finite *scalar* entanglement-magnitude proxy and links it to the
uncertainty deficits, to the terminal-record commit, and to the legal Born weight.

The magnitude is the product of the two unresolved boundary residuals
(`residualDescent d * residualDistinction b`): a concurrence-like nonnegative
scalar that is strictly positive exactly in the premeasurement (fully unlicensed)
regime and collapses to zero as soon as either boundary axis is licensed. This is
the finite structural shadow of the "pre-commit entangled, post-commit
classical-separable, one boundary event apart" picture.

Scope and honesty: this is a FINITE STRUCTURAL carrier over the U-03 collapse
deficits. It is NOT a physical entanglement measure (no Hilbert space, no
concurrence/negativity theorem) and makes no physics theorem-status claim. The
Born content is the nonnegative gauge-invariant accepted-shot ratio of U-05; the
reading of these scalars as physical entanglement or collapse probabilities is a
structural model, not a Lean theorem.

No `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
`unsafe`, `partial`, or `opaque`. Headline declarations are `#print axioms`-checked
against the baseline whitelist `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.Meta.UUET

open OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio

noncomputable section

/-- Finite structural entanglement-magnitude proxy: the product of the two
unresolved boundary residuals. Strictly positive in the premeasurement regime,
zero once either axis is licensed. Not a physical entanglement measure. -/
def entanglementMagnitude (descentLicensed distinctionLicensed : Bool) : ℝ :=
  residualDescent descentLicensed * residualDistinction distinctionLicensed

/-- The entanglement magnitude is nonnegative. -/
theorem entanglementMagnitude_nonneg (d b : Bool) :
    0 ≤ entanglementMagnitude d b :=
  mul_nonneg (residualDescent_nonneg d) (residualDistinction_nonneg b)

/-- **Link to the uncertainty deficits.** The premeasurement (fully unlicensed)
entanglement magnitude equals the product of the two pre-license collapse
deficits of U-03. -/
theorem entanglementMagnitude_premeasurement_eq :
    entanglementMagnitude false false = descentDeficit * distinctionDeficit := by
  unfold entanglementMagnitude
  simp

/-- **Nonzero witness.** The premeasurement entanglement magnitude is strictly
positive (both U-03 deficits are strictly positive). -/
theorem entanglementMagnitude_premeasurement_pos :
    0 < entanglementMagnitude false false := by
  rw [entanglementMagnitude_premeasurement_eq]
  exact mul_pos uuet_uncertainty_two_positive.1 uuet_uncertainty_two_positive.2

/-- **Collapse characterization.** The entanglement magnitude is zero iff at least
one boundary axis is licensed: committing either boundary event collapses the
premeasurement structure to a separable record. -/
theorem entanglementMagnitude_zero_iff_some_licensed (d b : Bool) :
    entanglementMagnitude d b = 0 ↔ d = true ∨ b = true := by
  unfold entanglementMagnitude
  rw [mul_eq_zero, residualDescent_eq_zero_iff, residualDistinction_eq_zero_iff]

/-- **Terminal-record collapse.** An admissible boundary event (both transactions
resolved, U-27) has zero entanglement magnitude: the committed terminal record is
a separable classical record. -/
theorem entanglementMagnitude_collapses_on_terminal_record
    (s : OperationalCompletenessState)
    (h : terminalRecordLicensed s) :
    entanglementMagnitude (descentLicensedOf s) (distinctionLicensedOf s) = 0 := by
  obtain ⟨hp, _⟩ := h
  rw [entanglementMagnitude_zero_iff_some_licensed]
  exact Or.inl ((descentLicensedOf_iff s).2 hp)

/-- **Born / terminal-record legality bridge.** Once an outcome is committed as a
licensed terminal record, the premeasurement entanglement magnitude is zero and
the accompanying legal Born weight is the nonnegative accepted-shot ratio of U-05.
The committed Born outcome is a separable classical record carrying a legal weight. -/
theorem entanglementMagnitude_born_terminal_legality
    (s : OperationalCompletenessState)
    (h : terminalRecordLicensed s)
    (g e k : ℝ) (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    entanglementMagnitude (descentLicensedOf s) (distinctionLicensedOf s) = 0
      ∧ 0 ≤ bornRatio g e k :=
  ⟨entanglementMagnitude_collapses_on_terminal_record s h,
    (uuet_born_weight_over_legal_branches g e k hg he hk).1⟩

/-- Non-vacuity: positive premeasurement magnitude equal to the deficit product,
zero on each single-licensed state, and zero on the canonical committed record. -/
theorem entanglementMagnitude_nonvacuous :
    0 < entanglementMagnitude false false
      ∧ entanglementMagnitude false false = descentDeficit * distinctionDeficit
      ∧ entanglementMagnitude true false = 0
      ∧ entanglementMagnitude false true = 0
      ∧ entanglementMagnitude (descentLicensedOf canonicalOperationallyComplete)
          (distinctionLicensedOf canonicalOperationallyComplete) = 0 := by
  refine ⟨entanglementMagnitude_premeasurement_pos,
    entanglementMagnitude_premeasurement_eq, ?_, ?_, ?_⟩
  · rw [entanglementMagnitude_zero_iff_some_licensed]; exact Or.inl rfl
  · rw [entanglementMagnitude_zero_iff_some_licensed]; exact Or.inr rfl
  · exact entanglementMagnitude_collapses_on_terminal_record _
      (operationallyComplete_terminal_record_licensed canonicalOperationallyComplete_complete)

#print axioms entanglementMagnitude_nonneg
#print axioms entanglementMagnitude_premeasurement_eq
#print axioms entanglementMagnitude_premeasurement_pos
#print axioms entanglementMagnitude_zero_iff_some_licensed
#print axioms entanglementMagnitude_collapses_on_terminal_record
#print axioms entanglementMagnitude_born_terminal_legality
#print axioms entanglementMagnitude_nonvacuous

end

end OperatorKO7.Meta.UUET
