import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7ExactSchema
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness

/-!
# KO7 closed witness minimality and unique root obstruction

This file keeps two notions separate:
* universal state-cardinality minimality lives in `Cardinality.lean`;
* this file proves a *closed KO7 syntax-size* minimum for reflexive `eqW` terms.

Relation claims reuse the already mechanized full-root critical-pair completeness
result and do not upgrade root rewriting to context rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7
open OperatorKO7.Trace

/-- Structural constructor count on KO7 `Trace`. -/
def ko7TraceSize : Trace → Nat
  | .void => 1
  | .delta t => ko7TraceSize t + 1
  | .integrate t => ko7TraceSize t + 1
  | .merge a b => ko7TraceSize a + ko7TraceSize b + 1
  | .app a b => ko7TraceSize a + ko7TraceSize b + 1
  | .recΔ b s n => ko7TraceSize b + ko7TraceSize s + ko7TraceSize n + 1
  | .eqW a b => ko7TraceSize a + ko7TraceSize b + 1

/-- Every KO7 term has positive structural size. -/
theorem ko7TraceSize_pos (t : Trace) : 1 ≤ ko7TraceSize t := by
  induction t <;> simp [ko7TraceSize] <;> omega

/-- The canonical closed diagonal witness has size three. -/
theorem ko7_eqW_void_void_size : ko7TraceSize (eqW void void) = 3 := rfl

/-- Every closed reflexive equality witness has size at least three. -/
theorem ko7_eqW_diagonal_size_ge_three (a : Trace) :
    3 ≤ ko7TraceSize (eqW a a) := by
  simp only [ko7TraceSize]
  have h := ko7TraceSize_pos a
  omega

/-- Closed-witness minimality in the declared KO7 grammar. -/
theorem ko7_closed_witness_minimal_in_declared_grammar :
    ko7TraceSize (eqW void void) = 3 ∧
      ∀ a : Trace, 3 ≤ ko7TraceSize (eqW a a) :=
  ⟨ko7_eqW_void_void_size, ko7_eqW_diagonal_size_ge_three⟩

/-- Exact local-cone relation isomorphism for the closed witness. -/
noncomputable def ko7_localCone_equiv_fork3 :
    RelIso Fork3Step
      (LocalConeStep ko7ExactDiagonalForkSchema void ko7TerminalDiagonal) :=
  determined_terminal_diagonal_localCone_equiv_fork3
    ko7ExactDiagonalForkSchema void ko7TerminalDiagonal ko7DiagonalDetermined

/-- Re-export of the independent full-kernel root completeness theorem: root
local nonjoinability occurs exactly on reflexive `eqW` diagonals. -/
theorem ko7_unique_root_obstruction_reexport (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep a ↔ OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a :=
  OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction a

/-- Canonical closed witness plus completeness of the obstruction class. -/
theorem ko7_closed_canonical_obstruction :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void) ∧
      ∀ a, ¬ MetaSN_KO7.LocalJoinStep a → OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.IsEqWDiagonal a :=
  OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork

