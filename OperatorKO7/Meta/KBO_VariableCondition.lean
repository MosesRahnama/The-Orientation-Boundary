import OperatorKO7.Meta.KBO_Impossible

/-!
# KBO Variable-Condition Compatibility Layer

Historical archive rows S118 and S134 point at `Meta/KBO_VariableCondition.lean`.
The actual obstruction now lives in `Meta/KBO_Impossible.lean` and
`Meta/SymbolicComparatorBarrier.lean`.

This module restores the missing file surface without inventing new mathematics:

1. `KBOAttempt` re-exports the minimal KBO-facing hypothesis layer.
2. `variable_condition_fails_rec_succ` records the schema-level payload-variable
   count increase that blocks the duplicating rule.
3. The KBO impossibility theorems forward the already-proved schema and
   trace-level corollaries under the archive-facing module path.
-/

namespace OperatorKO7.KBOVariableCondition

open OperatorKO7.SymbolicComparatorBarrier

/-- Archive-facing alias for the minimal KBO-style comparator abstraction. -/
abbrev KBOAttempt := OperatorKO7.KBOImpossible.KBOStyleOrder

/-- The schema payload variable `s` occurs once on the source side and twice on
the target side of the duplicating `rec_succ` pattern. -/
theorem variable_condition_fails_rec_succ :
    countVar SchemaVar.s dupTgt > countVar SchemaVar.s dupSrc := by
  simp [countVar_dupSrc_s, countVar_dupTgt_s]

/-- No KBO-style order can orient the duplicating schema step. -/
theorem no_kbo_orients_dup_step (K : KBOAttempt) :
    ¬ K.gt dupSrc dupTgt :=
  OperatorKO7.KBOImpossible.no_kbo_orients_dup_step K

/-- No KBO-style order exists that orients the duplicating schema step. -/
theorem no_kbo_orients_rec_succ :
    ¬ ∃ K : KBOAttempt, K.gt dupSrc dupTgt :=
  OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ

/-- Archive-facing alias of the schema-level KO7 impossibility corollary. -/
theorem no_kbo_orients_ko7_rec_succ :
    ¬ ∃ K : KBOAttempt, K.gt dupSrc dupTgt :=
  no_kbo_orients_rec_succ

/-- No trace-level comparator satisfying the standard variable condition can
orient the concrete KO7 `rec_succ` rule instance. -/
theorem no_kbo_orients_ko7_rec_succ_trace
    (gtT : Trace → Trace → Prop) (bT sT nT : Trace)
    (hvar : ∀ {x y : STerm} {v : SchemaVar},
      gtT (instantiate bT sT nT x) (instantiate bT sT nT y) →
        countVar v y ≤ countVar v x) :
    ¬ gtT (Trace.recΔ bT sT (Trace.delta nT)) (Trace.app sT (Trace.recΔ bT sT nT)) :=
  OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace gtT bT sT nT hvar

end OperatorKO7.KBOVariableCondition
