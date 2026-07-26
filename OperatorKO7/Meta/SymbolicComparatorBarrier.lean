import OperatorKO7.Meta.SymbolicComparatorBarrier_Schema
import OperatorKO7.Kernel

/-!
This module instantiates the imported symbolic duplicating terms in `Trace` and
proves the two displayed definitional equalities. The comparator interface and
its variable-condition obstruction are proved in the imported schema module;
this module adds only the concrete term interpretation.

-/

namespace OperatorKO7.SymbolicComparatorBarrier

def instantiate (bT sT nT : Trace) : STerm → Trace
  | STerm.var SchemaVar.b => bT
  | STerm.var SchemaVar.s => sT
  | STerm.var SchemaVar.n => nT
  | STerm.base => Trace.void
  | STerm.succ t => Trace.delta (instantiate bT sT nT t)
  | STerm.wrap x y => Trace.app (instantiate bT sT nT x) (instantiate bT sT nT y)
  | STerm.recur bU sU nU =>
      Trace.recΔ (instantiate bT sT nT bU) (instantiate bT sT nT sU) (instantiate bT sT nT nU)

theorem instantiate_dupSrc (bT sT nT : Trace) :
    instantiate bT sT nT dupSrc = Trace.recΔ bT sT (Trace.delta nT) := by
  simp [dupSrc, instantiate]

theorem instantiate_dupTgt (bT sT nT : Trace) :
    instantiate bT sT nT dupTgt = Trace.app sT (Trace.recΔ bT sT nT) := by
  simp [dupTgt, instantiate]

end OperatorKO7.SymbolicComparatorBarrier
