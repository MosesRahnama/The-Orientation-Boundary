import Mathlib

/-!
# The categorical Landauer price of deletion (Blueprint §7)

The blueprint argues that Landauer's thermodynamic price `τ ≥ k_B T ln 2` is the categorical
consequence of forcing a non-natural deletion across the quantum-to-classical boundary: in a classical
(Markov / copy-discard) category the discard map is natural and free, while erasing genuine
information must be paid for. The copy-discard categorical substrate is already mechanized in
`Meta/UniversalBoundary/MarkovCategory.lean` (`channel_discards_to_unit`).

This module mechanizes the **cost side** the section relies on: the Landauer erasure cost is
nonnegative, additive over composed erasures, has a strictly positive per-bit floor at positive
temperature, and is zero exactly when nothing is erased (deletion is free iff it discards no
information). The thermal energy `kT = k_B T` is carried as a parameter, so the module depends on no
particular spelling of the physical constants.

## Audit slots
- Relation: a thermodynamic cost functional (not a rewriting relation).
- Closure: `propext`, `Classical.choice`, `Quot.sound`.
- Trust: no `sorry`/`axiom`/`native_decide`.
- Scope: the erasure-cost algebra (floor, additivity, free-iff-trivial); the categorical naturalness
  of classical discard is in `MarkovCategory.lean`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer

/-- The Landauer cost of erasing `bits` bits at thermal energy `kT = k_B T`: `bits · kT · ln 2`. -/
noncomputable def erasureCost (kT : ℝ) (bits : ℕ) : ℝ :=
  (bits : ℝ) * (kT * Real.log 2)

/-- Erasure cost is nonnegative at nonnegative temperature. -/
theorem erasureCost_nonneg (kT : ℝ) (hkT : 0 ≤ kT) (bits : ℕ) :
    0 ≤ erasureCost kT bits := by
  unfold erasureCost
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- Erasure cost is additive: erasing `m + n` bits costs the sum of erasing `m` then `n`. This is the
compositional Landauer accounting across a pipeline of deletions. -/
theorem erasureCost_additive (kT : ℝ) (m n : ℕ) :
    erasureCost kT (m + n) = erasureCost kT m + erasureCost kT n := by
  unfold erasureCost
  push_cast
  ring

/-- **The Landauer floor:** erasing a single bit costs `kT · ln 2 > 0` at positive temperature. This is
the strictly positive price that a non-natural (information-erasing) deletion must pay. -/
theorem erasureCost_floor (kT : ℝ) (hkT : 0 < kT) :
    0 < erasureCost kT 1 := by
  unfold erasureCost
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Nat.cast_one, one_mul]
  exact mul_pos hkT hlog

/-- **Deletion is free iff it erases nothing.** At positive temperature the cost vanishes exactly when
no bits are discarded; any genuine information erasure is strictly priced. -/
theorem free_iff_no_erasure (kT : ℝ) (hkT : 0 < kT) (bits : ℕ) :
    erasureCost kT bits = 0 ↔ bits = 0 := by
  unfold erasureCost
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < kT * Real.log 2 := mul_pos hkT hlog
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hb | hc
    · exact_mod_cast hb
    · exact absurd hc (ne_of_gt hpos)
  · intro h; subst h; simp

/-! ## Non-vacuity -/

/-- Concrete positive erasure cost (one bit at unit thermal energy is `ln 2 > 0`). -/
theorem erasureCost_one_unit_pos : 0 < erasureCost 1 1 :=
  erasureCost_floor 1 (by norm_num)

#print axioms erasureCost_nonneg
#print axioms erasureCost_additive
#print axioms erasureCost_floor
#print axioms free_iff_no_erasure

end OperatorKO7.Meta.QuantumBoundary.CategoricalLandauer
