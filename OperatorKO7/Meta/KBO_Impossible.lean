import OperatorKO7.Meta.KBO_Impossible_Schema
import OperatorKO7.Meta.SymbolicComparatorBarrier

/-!
# Explicit KBO-Style Impossibility Corollary

## Formal Scope

The local result is a conditional variable-count obstruction forwarded from imports. It does not formalize all KBO instances or derive the variable condition from a KBO implementation.
-/

namespace OperatorKO7.KBOImpossible

open OperatorKO7.SymbolicComparatorBarrier

/-- Trace-level bridge for the KO7 `rec_succ` rule: if a concrete comparator on
instantiated schema terms satisfies the standard variable condition there, it
cannot orient the concrete rule instance. -/
theorem no_kbo_orients_ko7_rec_succ_trace
    (gtT : Trace → Trace → Prop) (bT sT nT : Trace)
    (hvar : ∀ {x y : STerm} {v : SchemaVar},
      gtT (instantiate bT sT nT x) (instantiate bT sT nT y) →
        countVar v y ≤ countVar v x) :
    ¬ gtT (Trace.recΔ bT sT (Trace.delta nT)) (Trace.app sT (Trace.recΔ bT sT nT)) := by
  intro hgt
  have hs : countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc := by
    apply hvar (x := dupSrc) (y := dupTgt) (v := SchemaVar.s)
    simpa [instantiate_dupSrc, instantiate_dupTgt] using hgt
  simp [countVar_dupSrc_s, countVar_dupTgt_s] at hs

end OperatorKO7.KBOImpossible
