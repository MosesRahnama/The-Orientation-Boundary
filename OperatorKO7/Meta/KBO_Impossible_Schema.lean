import OperatorKO7.Meta.SymbolicComparatorBarrier_Schema

/-!
# KBO-style variable-condition obstruction

This schema-facing layer aliases the symbolic comparator's variable-condition
interface. Its two corollaries therefore cover that interface; the concrete
KO7 trace specialization is stated in `Meta/KBO_Impossible.lean`.
-/

namespace OperatorKO7.KBOImpossible

open OperatorKO7.SymbolicComparatorBarrier

/-- Minimal KBO-facing abstraction used by the KO7 impossibility corollary.
It is just a symbolic comparator with the standard variable condition. -/
abbrev KBOStyleOrder := VariableConditionOrder

/-- A variable-condition comparator orienting the duplicating schema step yields
a contradiction. -/
theorem no_kbo_orients_dup_step (K : KBOStyleOrder) :
    ¬ K.gt dupSrc dupTgt :=
  not_orients_dup_rule K

/-- Existence of a variable-condition comparator orienting the duplicating
schema step yields a contradiction. Full KBO consequences require the
trace-level adapter in `Meta/KBO_Impossible.lean`. -/
theorem no_kbo_orients_ko7_rec_succ :
    ¬ ∃ K : KBOStyleOrder, K.gt dupSrc dupTgt :=
  no_symbolic_variable_condition_orients_dup_step

end OperatorKO7.KBOImpossible
