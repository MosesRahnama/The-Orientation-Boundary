import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierNatural_EWZ
import OperatorKO7.Meta.MatrixBarrierNatural

/-!
# Context closure for the arctic and Endrullis-Waldmann-Zantema families

The root-level and context-closed barrier inventories are kept equal as sets: every root family
`no_global_step_orientation_X` has a context-closed counterpart `no_stepCtxFull_orientation_X`.
Six families were added at the root without their counterparts, three arctic and three
Endrullis-Waldmann-Zantema, and this module supplies them.

Each lift is the same one-line argument the rest of the closure uses: every root contraction is a
one-hole context step at the identity context, so an orienter of `StepCtxFull` is in particular an
orienter of the root relation, and the root barrier applies unchanged. No hypothesis is added and
none is dropped.

Relation: `StepCtxFull`. Closure: full one-hole context.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.ContextClosedBarrierFullClosure

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ContextClosedBarrier
open MetaSN_KO7

/-! ## Arctic -/

theorem no_stepCtxFull_orientation_arcticMatrix_of_tracked_nonincreasing
    {d : Nat} (M : StepDuplicatingSchema.ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.ArcticWrapDiagPositive M i)
    {R : StepDuplicatingSchema.ArcticVec d → StepDuplicatingSchema.ArcticVec d → Prop}
    (hR : ∀ {u v : StepDuplicatingSchema.ArcticVec d},
      R u v → StepDuplicatingSchema.ArcticLe (u i) (v i))
    (hfin : ∃ (t : Trace) (a : Nat), M.eval t i = StepDuplicatingSchema.ArcticNat.fin a) :
    ¬ GlobalOrientsStepCtxFull M.eval R := fun h =>
  OperatorKO7.MatrixBarrierArcticNatural.no_global_step_orientation_arcticMatrix_of_tracked_nonincreasing
    M hi hR hfin (stepCtxFull_orientation_implies_root h)

theorem no_stepCtxFull_orientation_arcticMatrix_of_tracked_strict
    {d : Nat} (M : StepDuplicatingSchema.ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.ArcticWrapDiagPositive M i)
    {R : StepDuplicatingSchema.ArcticVec d → StepDuplicatingSchema.ArcticVec d → Prop}
    (hR : ∀ {u v : StepDuplicatingSchema.ArcticVec d},
      R u v → StepDuplicatingSchema.ArcticLt (u i) (v i)) :
    ¬ GlobalOrientsStepCtxFull M.eval R := fun h =>
  OperatorKO7.MatrixBarrierArcticNatural.no_global_step_orientation_arcticMatrix_of_tracked_strict
    M hi hR (stepCtxFull_orientation_implies_root h)

theorem no_stepCtxFull_orientation_arcticMatrix_of_tracked_strict_pumpFree
    {d : Nat} (M : StepDuplicatingSchema.ArcticNatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.ArcticWrapDiagFinite M i)
    {R : StepDuplicatingSchema.ArcticVec d → StepDuplicatingSchema.ArcticVec d → Prop}
    (hR : ∀ {u v : StepDuplicatingSchema.ArcticVec d},
      R u v → StepDuplicatingSchema.ArcticLt (u i) (v i)) :
    ¬ GlobalOrientsStepCtxFull M.eval R := fun h =>
  OperatorKO7.MatrixBarrierArcticNatural.no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree
    M hi hR (stepCtxFull_orientation_implies_root h)

/-! ## Endrullis-Waldmann-Zantema -/

theorem no_stepCtxFull_orientation_ewzMonotone
    {d : Nat} [NeZero d] (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d)
    (hewz : StepDuplicatingSchema.EWZMonotoneInterpretation M) :
    ¬ GlobalOrientsStepCtxFull M.eval (StepDuplicatingSchema.VecLeLt 0) := fun h =>
  OperatorKO7.MatrixBarrierNaturalEWZ.no_global_step_orientation_ewzMonotone M hewz
    (stepCtxFull_orientation_implies_root h)

theorem no_stepCtxFull_orientation_ewzMonotone_componentwise
    {d : Nat} [NeZero d] (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d)
    (hewz : StepDuplicatingSchema.EWZMonotoneInterpretation M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := fun h =>
  OperatorKO7.MatrixBarrierNaturalEWZ.no_global_step_orientation_ewzMonotone_componentwise M hewz
    (stepCtxFull_orientation_implies_root h)

theorem no_stepCtxFull_orientation_ewzMonotone_lexD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema (d + 1))
    (hewz : StepDuplicatingSchema.EWZMonotoneInterpretation M)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLexLt := fun h =>
  OperatorKO7.MatrixBarrierNaturalEWZ.no_global_step_orientation_ewzMonotone_lexD_of_primary_pos
    M hewz hpos (stepCtxFull_orientation_implies_root h)

end OperatorKO7.ContextClosedBarrierFullClosure
