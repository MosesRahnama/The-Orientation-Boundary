import OperatorKO7.Meta.MutualDuplication_Schema
import OperatorKO7.Meta.MutualDuplication_General
import OperatorKO7.Meta.MutualDuplication_Case

/-!
# Barriers for the First-Class Mutual Step-Duplicating Schema

This module lands the additive and affine barriers for the theorem-native mutual schema,
then bridges the existing alternating two-node development into that schema.
-/

namespace OperatorKO7.MutualDuplicationSchema

open OperatorKO7.StepDuplicating

namespace Schema

/-- Additive direct orienters fail on the first-class mutual one-cycle composite. -/
theorem no_additive_orients_cycle
    {S : Schema} (M : Schema.AdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (Schema.cycleTarget S b s n) <
        M.eval (Schema.cycleSource S b s n)) := by
  simpa using
    (OperatorKO7.MutualDuplicationCycleFlow.no_additive_orients_cycle_composite
      (S := Schema.toPrimarySchema S) (M := M.toPrimaryMeasure)
      (copies := 2) (hcopies := by decide))

/-- Affine direct orienters fail on the first-class mutual one-cycle composite
under the usual derived-schema unbounded-pump hypothesis. -/
theorem no_affine_orients_cycle_of_unbounded
    {S : Schema} (M : Schema.AffineMeasure S)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      M.toCompositeMeasure) :
    ¬ (∀ (b s n : S.T),
      M.eval (Schema.cycleTarget S b s n) <
        M.eval (Schema.cycleSource S b s n)) := by
  have hunbounded' :
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          M.toPrimaryMeasure 2 (by decide)) := by
    simpa [Schema.AffineMeasure.toCompositeMeasure] using hunbounded
  simpa using
    (OperatorKO7.MutualDuplicationCycleFlow.no_affine_orients_cycle_composite_of_unbounded
      (S := Schema.toPrimarySchema S) (M := M.toPrimaryMeasure)
      (copies := 2) (hcopies := by decide) (hunbounded := hunbounded'))

end Schema

namespace System

/-- The theorem-native mutual context relation inherits the additive barrier. -/
theorem no_global_orients_ctx_additive
    {Sys : System} (M : Schema.AdditiveMeasure Sys.toSchema) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
      (W := Sys.toCycleWitness) (M := M.toPrimaryMeasure) (hcopies := by decide)

/-- The theorem-native mutual context relation inherits the affine barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {Sys : System} (M : Schema.AffineMeasure Sys.toSchema)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      M.toCompositeMeasure) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  have hunbounded' :
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          M.toPrimaryMeasure 2 (by decide)) := by
    simpa [Schema.AffineMeasure.toCompositeMeasure] using hunbounded
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_affine_of_unbounded
      (W := Sys.toCycleWitness) (M := M.toPrimaryMeasure)
      (hcopies := by decide) (hunbounded := hunbounded')

end System

end OperatorKO7.MutualDuplicationSchema

namespace OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema

/-- The existing alternating two-node schema as an instance of the first-class mutual schema. -/
def toMutualSchema (S : AlternatingDupSchema) : OperatorKO7.MutualDuplicationSchema.Schema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recurA := S.recurA
  recurB := S.recurB

/-- Transport the old additive alternating measures to the first-class mutual schema. -/
def AdditiveMeasure.toMutualMeasure {S : AlternatingDupSchema}
    (M : AdditiveMeasure S) :
    OperatorKO7.MutualDuplicationSchema.Schema.AdditiveMeasure S.toMutualSchema where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recurA := M.eval_recurA
  eval_recurB := M.eval_recurB
  h_wrap_pos := M.h_wrap_pos

/-- Transport the old affine alternating measures to the first-class mutual schema. -/
def AffineMeasure.toMutualMeasure {S : AlternatingDupSchema}
    (M : AffineMeasure S) :
    OperatorKO7.MutualDuplicationSchema.Schema.AffineMeasure S.toMutualSchema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recurA := M.eval_recurA
  eval_recurB := M.eval_recurB
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- The old alternating additive theorem is an instance of the first-class mutual barrier. -/
theorem no_additive_orients_via_mutualSchema
    {S : AlternatingDupSchema} (M : AdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.wrap s (S.recurA b s n))) <
        M.eval (S.recurA b s (S.succ (S.succ n)))) := by
  simpa [toMutualSchema] using
    (OperatorKO7.MutualDuplicationSchema.Schema.no_additive_orients_cycle
      (S := S.toMutualSchema) (M := M.toMutualMeasure))

/-- The old alternating affine theorem is also an instance of the first-class mutual barrier. -/
theorem no_affine_orients_of_unbounded_via_mutualSchema
    {S : AlternatingDupSchema} (M : AffineMeasure S)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      M.toMutualMeasure.toCompositeMeasure) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.wrap s (S.recurA b s n))) <
        M.eval (S.recurA b s (S.succ (S.succ n)))) := by
  simpa [toMutualSchema] using
    (OperatorKO7.MutualDuplicationSchema.Schema.no_affine_orients_cycle_of_unbounded
      (S := S.toMutualSchema) (M := M.toMutualMeasure) (hunbounded := hunbounded))

end OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema

namespace OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema.AlternatingDupSystem

/-- The existing alternating two-node system as an instance of the first-class mutual system. -/
def toMutualSystem (Sys : AlternatingDupSystem) : OperatorKO7.MutualDuplicationSchema.System where
  T := Sys.T
  base := Sys.base
  succ := Sys.succ
  wrap := Sys.wrap
  recurA := Sys.recurA
  recurB := Sys.recurB
  Step := Sys.Step
  stepA_succ := Sys.stepA_succ
  stepB_succ := Sys.stepB_succ

/-- The old alternating system realizes the first-class mutual one-cycle path. -/
theorem cycle_realized_via_mutualSchema (Sys : AlternatingDupSystem) (b s n : Sys.T) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationSchema.System.StepCtx Sys.toMutualSystem)
      (OperatorKO7.MutualDuplicationSchema.Schema.cycleSource Sys.toMutualSystem.toSchema b s n)
      (OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget Sys.toMutualSystem.toSchema b s n) := by
  simpa using OperatorKO7.MutualDuplicationSchema.System.cyclePath Sys.toMutualSystem b s n

end OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema.AlternatingDupSystem

namespace OperatorKO7.MutualDuplicationCase

/-- Concrete nonvacuity witness system for the first-class mutual schema. -/
def mutualWitnessSystem : OperatorKO7.MutualDuplicationSchema.System where
  T := AltTerm
  base := AltTerm.base
  succ := AltTerm.succ
  wrap := AltTerm.wrap
  recurA := AltTerm.recurA
  recurB := AltTerm.recurB
  Step := AltStep
  stepA_succ := by
    intro b s n
    exact AltStep.R_A_succ b s n
  stepB_succ := by
    intro b s n
    exact AltStep.R_B_succ b s n

/-- The concrete alternating witness system realizes the mutual one-cycle composite. -/
theorem mutualWitnessSystem_nonvacuous (b s n : AltTerm) :
    ∃ u,
      OperatorKO7.MutualDuplicationSchema.System.StepCtx mutualWitnessSystem
        (OperatorKO7.MutualDuplicationSchema.Schema.cycleSource mutualWitnessSystem.toSchema b s n) u ∧
      OperatorKO7.MutualDuplicationSchema.System.StepCtx mutualWitnessSystem u
        (OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget mutualWitnessSystem.toSchema b s n) := by
  refine ⟨OperatorKO7.MutualDuplicationSchema.Schema.cycleMid mutualWitnessSystem.toSchema b s n, ?_, ?_⟩
  · simpa [OperatorKO7.MutualDuplicationSchema.Schema.cycleSource,
      OperatorKO7.MutualDuplicationSchema.Schema.cycleMid] using
      (OperatorKO7.MutualDuplicationSchema.System.StepCtx.root
        (mutualWitnessSystem.stepA_succ b s (AltTerm.succ n)))
  · simpa [OperatorKO7.MutualDuplicationSchema.Schema.cycleMid,
      OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget] using
      (OperatorKO7.MutualDuplicationSchema.System.StepCtx.wrap_right s
        (OperatorKO7.MutualDuplicationSchema.System.StepCtx.root
          (mutualWitnessSystem.stepB_succ b s n)))

end OperatorKO7.MutualDuplicationCase
