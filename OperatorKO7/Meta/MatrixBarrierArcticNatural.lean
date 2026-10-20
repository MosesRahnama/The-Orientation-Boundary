import OperatorKO7.Meta.MatrixBarrierArcticNatural_Schema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax
import OperatorKO7.Meta.ContextClosedBarrier

/-!
# Arctic matrix barrier: system, KO7, and context layers

`Meta/MatrixBarrierArcticNatural_Schema.lean` proves the certificate-free arctic barrier at the
root of an abstract step-duplicating schema. This module carries it up the three layers the
natural-matrix barrier already occupies: an arbitrary step-duplicating system, the KO7 rewrite
relation `Step`, and the full one-hole context closure `StepCtxFull`.

The strict form needs no positivity. `no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree`
supplies its own pump from the strictly oriented recursor chain, so the barrier holds for every
arctic interpretation whose two wrapper diagonal entries are finite, `fin 0` included. What is
load-bearing is finiteness: `arcticBotRightMeasure` is a compiled arctic interpretation of the
free syntax whose right wrapper diagonal entry is `bot` and which strictly orients the duplicating
step at its only coordinate. The `fin 0` case is therefore proved, and the `bot` case is killed.

Relation: `Step`, `StepCtxFull`, and the schema duplicating step. Closure: root and full context.
External trust: none. Mathlib only.
Named method: arctic (max-plus) matrix interpretations; the order is a parameter.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## System layer -/

/-- System-level arctic barrier, nonincreasing form. -/
theorem no_global_orients_arcticMatrix_of_tracked_nonincreasing
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : ArcticNatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLe (u i) (v i))
    (hfin : ∃ (t : Sys.T) (a : Nat), M.eval t i = ArcticNat.fin a) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_arcticMatrix_orients_dup_step_of_tracked_nonincreasing
    (S := Sys.toStepDuplicatingSchema) M hi hR hfin (fun b s n => h (Sys.dup_step b s n))

/-- System-level arctic barrier, strict form, with the positivity premise. -/
theorem no_global_orients_arcticMatrix_of_tracked_strict
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : ArcticNatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_arcticMatrix_orients_dup_step_of_tracked_strict
    (S := Sys.toStepDuplicatingSchema) M hi hR (fun b s n => h (Sys.dup_step b s n))

/-- **System-level arctic barrier, strict form, pump free.** Finiteness of the two wrapper
diagonal entries is the whole premise. -/
theorem no_global_orients_arcticMatrix_of_tracked_strict_pumpFree
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : ArcticNatMatrixMeasure Sys.toStepDuplicatingSchema d) {i : Fin d}
    (hi : ArcticWrapDiagFinite M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree
    (S := Sys.toStepDuplicatingSchema) M hi hR (fun b s n => h (Sys.dup_step b s n))

/-! ## The `bot` case is a real escape

The free syntax carries an arctic interpretation whose right wrapper diagonal entry is `bot`.
Because `bot` absorbs under arctic multiplication, the wrapper loses every lower bound on its
right argument, and the interpretation orients the duplicating step strictly. Finiteness in
`ArcticWrapDiagFinite` is therefore load-bearing. -/

/-- The measure realized by `arcticBotRightMeasure`: the wrapper reads only its left argument,
the successor and the recursor each add one. -/
def botRightWeight : FreeTerm → Nat
  | FreeTerm.base => 0
  | FreeTerm.succ t => 1 + botRightWeight t
  | FreeTerm.wrap x _ => botRightWeight x
  | FreeTerm.recur b s n =>
      max (botRightWeight b) (1 + max (botRightWeight s) (botRightWeight n))

/-- A one-dimensional arctic interpretation of the free syntax whose right wrapper diagonal entry
is `bot`. -/
def arcticBotRightMeasure : ArcticNatMatrixMeasure freeSchema 1 where
  eval := fun t _ => ArcticNat.fin (botRightWeight t)
  base_vec := fun _ => ArcticNat.fin 0
  succ_bias := fun _ => ArcticNat.fin 0
  succ_mat := ⟨fun _ _ => ArcticNat.fin 1⟩
  wrap_bias := fun _ => ArcticNat.fin 0
  wrap_left := ⟨fun _ _ => ArcticNat.fin 0⟩
  wrap_right := ⟨fun _ _ => ArcticNat.bot⟩
  recur_bias := fun _ => ArcticNat.fin 0
  recur_base := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_step := ⟨fun _ _ => ArcticNat.fin 1⟩
  recur_counter := ⟨fun _ _ => ArcticNat.fin 1⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [freeSchema, botRightWeight, arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus,
      List.finRange]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [freeSchema, botRightWeight, arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus,
      List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [freeSchema, botRightWeight, arcticVecMax, arcticMax, ArcticMatrix.act, arcticPlus,
      List.finRange]

/-- Its right wrapper diagonal entry is `bot`, so `ArcticWrapDiagFinite` fails. -/
theorem arcticBotRightMeasure_not_wrapDiagFinite :
    ¬ ArcticWrapDiagFinite arcticBotRightMeasure 0 := by
  rintro ⟨-, ⟨k, hk⟩⟩
  simp only [arcticBotRightMeasure] at hk
  exact ArcticNat.noConfusion hk

/-- **The `bot` case is a genuine escape.** With a `bot` right wrapper diagonal entry the
duplicating step is oriented strictly at coordinate `0`, uniformly in the three arguments. -/
theorem arcticBotRightMeasure_strictly_orients :
    ∀ (b s n : FreeTerm),
      ArcticLt (arcticBotRightMeasure.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
        (arcticBotRightMeasure.eval (freeSchema.recur b s (freeSchema.succ n)) 0) := by
  intro b s n
  simp only [arcticBotRightMeasure, freeSchema, ArcticLt, botRightWeight]
  omega

/-- The escape is not an artefact of an empty comparison: the same interpretation is finite at
every term. -/
theorem arcticBotRightMeasure_coord_finite (t : FreeTerm) :
    arcticBotRightMeasure.eval t 0 = ArcticNat.fin (botRightWeight t) := rfl

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierArcticNatural

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-! ## KO7 layer -/

/-- KO7 arctic barrier, nonincreasing form. -/
theorem no_global_step_orientation_arcticMatrix_of_tracked_nonincreasing
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLe (u i) (v i))
    (hfin : ∃ (t : Trace) (a : Nat), M.eval t i = ArcticNat.fin a) :
    ¬ GlobalOrients ko7System M.eval R :=
  no_global_orients_arcticMatrix_of_tracked_nonincreasing (Sys := ko7System) M hi hR hfin

/-- KO7 arctic barrier, strict form, with the positivity premise. -/
theorem no_global_step_orientation_arcticMatrix_of_tracked_strict
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ GlobalOrients ko7System M.eval R :=
  no_global_orients_arcticMatrix_of_tracked_strict (Sys := ko7System) M hi hR

/-- **KO7 arctic barrier, strict form, pump free.** -/
theorem no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagFinite M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ GlobalOrients ko7System M.eval R :=
  no_global_orients_arcticMatrix_of_tracked_strict_pumpFree (Sys := ko7System) M hi hR

/-! ## Context layer

An orienter of the full one-hole context closure orients the root relation, so every barrier
above lifts to `StepCtxFull` with no further hypothesis. -/

/-- Context-closed arctic barrier, nonincreasing form. -/
theorem no_ctx_orientation_arcticMatrix_of_tracked_nonincreasing
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLe (u i) (v i))
    (hfin : ∃ (t : Trace) (a : Nat), M.eval t i = ArcticNat.fin a) :
    ¬ OperatorKO7.ContextClosedBarrier.GlobalOrientsStepCtxFull M.eval R := fun h =>
  no_global_step_orientation_arcticMatrix_of_tracked_nonincreasing M hi hR hfin
    (OperatorKO7.ContextClosedBarrier.stepCtxFull_orientation_implies_root h)

/-- Context-closed arctic barrier, strict form, with the positivity premise. -/
theorem no_ctx_orientation_arcticMatrix_of_tracked_strict
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagPositive M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ OperatorKO7.ContextClosedBarrier.GlobalOrientsStepCtxFull M.eval R := fun h =>
  no_global_step_orientation_arcticMatrix_of_tracked_strict M hi hR
    (OperatorKO7.ContextClosedBarrier.stepCtxFull_orientation_implies_root h)

/-- **Context-closed arctic barrier, strict form, pump free.** The whole premise is that both
wrapper diagonal entries are finite. -/
theorem no_ctx_orientation_arcticMatrix_of_tracked_strict_pumpFree
    {d : Nat} (M : ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : ArcticWrapDiagFinite M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ OperatorKO7.ContextClosedBarrier.GlobalOrientsStepCtxFull M.eval R := fun h =>
  no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree M hi hR
    (OperatorKO7.ContextClosedBarrier.stepCtxFull_orientation_implies_root h)

/-! ## The KO7 instance with a positive wrapper diagonal -/

/-- Node count on `Trace`, in the max-plus reading the four schema constructors need. -/
def traceArcticWeight : Trace → Nat
  | Trace.void => 0
  | Trace.delta t => max 0 (1 + traceArcticWeight t)
  | Trace.integrate t => 1 + traceArcticWeight t
  | Trace.merge x y => 1 + traceArcticWeight x + traceArcticWeight y
  | Trace.app x y => max 0 (max (1 + traceArcticWeight x) (1 + traceArcticWeight y))
  | Trace.recΔ b s n =>
      max 0 (max (1 + traceArcticWeight b)
        (max (1 + traceArcticWeight s) (1 + traceArcticWeight n)))
  | Trace.eqW x y => 1 + traceArcticWeight x + traceArcticWeight y

/-- Trace weight as a one-dimensional arctic interpretation of KO7. -/
def sizeArcticMeasure : ArcticNatMatrixMeasure ko7Schema 1 where
  eval := fun t _ => ArcticNat.fin (traceArcticWeight t)
  base_vec := fun _ => ArcticNat.fin 0
  succ_bias := fun _ => ArcticNat.fin 0
  succ_mat := ⟨fun _ _ => ArcticNat.fin 1⟩
  wrap_bias := fun _ => ArcticNat.fin 0
  wrap_left := ⟨fun _ _ => ArcticNat.fin 1⟩
  wrap_right := ⟨fun _ _ => ArcticNat.fin 1⟩
  recur_bias := fun _ => ArcticNat.fin 0
  recur_base := ⟨fun _ _ => ArcticNat.fin 1⟩
  recur_step := ⟨fun _ _ => ArcticNat.fin 1⟩
  recur_counter := ⟨fun _ _ => ArcticNat.fin 1⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [traceArcticWeight, ko7Schema, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [traceArcticWeight, ko7Schema, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [traceArcticWeight, ko7Schema, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]

theorem sizeArcticMeasure_wrapDiagPositive :
    ArcticWrapDiagPositive sizeArcticMeasure 0 :=
  ⟨⟨1, rfl, le_refl 1⟩, ⟨1, rfl, le_refl 1⟩⟩

/-- The KO7 size interpretation is blocked at both layers. -/
theorem sizeArcticMeasure_no_ctx_orientation :
    ¬ OperatorKO7.ContextClosedBarrier.GlobalOrientsStepCtxFull sizeArcticMeasure.eval
        (fun u v => ArcticLt (u 0) (v 0)) :=
  no_ctx_orientation_arcticMatrix_of_tracked_strict sizeArcticMeasure
    sizeArcticMeasure_wrapDiagPositive (fun h => h)

end OperatorKO7.MatrixBarrierArcticNatural
