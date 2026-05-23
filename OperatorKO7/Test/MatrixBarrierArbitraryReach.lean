import OperatorKO7.Meta.MatrixBarrierArbitrary

namespace MatrixBarrierArbitraryReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

namespace Support

@[simp] def scalarVec (n : Nat) : OperatorKO7.StepDuplicating.StepDuplicatingSchema.MatrixVec 1 :=
  fun _ => n

@[simp] def oneMatrix : OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix 1 where
  coeff _ _ := 1

def simpleSizeMatrixMeasure :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema 1 where
  eval := fun t _ => simpleSize_ACM.eval t
  weight := scalarVec 1
  base_vec := scalarVec 0
  succ_bias := scalarVec 1
  succ_mat := oneMatrix
  wrap_bias := scalarVec 1
  wrap_left := oneMatrix
  wrap_right := oneMatrix
  recur_bias := scalarVec 1
  recur_base := oneMatrix
  recur_step := oneMatrix
  recur_counter := oneMatrix
  succ_scale := 1
  wrap_left_scale := 1
  wrap_right_scale := 1
  recur_base_scale := 1
  recur_step_scale := 1
  recur_counter_scale := 1
  eval_base := by
    funext i
    fin_cases i
    simp [scalarVec, ko7Schema, simpleSize_ACM]
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.vecAdd,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.vecAdd,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM, Nat.add_assoc]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.vecAdd,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM, Nat.add_assoc]
  h_succ_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_wrap_left_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_wrap_right_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_recur_base_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_recur_step_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_recur_counter_respects := by
    intro j
    fin_cases j
    simp [scalarVec, oneMatrix,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.MixedMatrix.weightedColumn]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

def scalarOrder
    (u v : OperatorKO7.StepDuplicating.StepDuplicatingSchema.MatrixVec 1) : Prop :=
  OperatorKO7.StepDuplicating.StepDuplicatingSchema.matrixScalarize simpleSizeMatrixMeasure.weight u <
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.matrixScalarize simpleSizeMatrixMeasure.weight v

def scalarDominance :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.MatrixScalarDominance
      simpleSizeMatrixMeasure.weight scalarOrder where
  nonstrict := by
    intro u v h
    exact Nat.le_of_lt h

lemma simpleSizeMatrixMeasure_unbounded :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedScalarizedRange
      simpleSizeMatrixMeasure := by
  intro k
  refine ⟨appIter k, ?_⟩
  simpa [simpleSizeMatrixMeasure, scalarVec,
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.matrixScalarize] using
    eval_appIter_ge simpleSize_ACM k

end Support

example :
    ¬ (∀ (b s n : Trace),
      Support.scalarOrder
        (Support.simpleSizeMatrixMeasure.eval (app s (recΔ b s n)))
        (Support.simpleSizeMatrixMeasure.eval (recΔ b s (delta n)))) := by
  exact
    StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump
      (S := ko7Schema)
      Support.simpleSizeMatrixMeasure
      Support.scalarDominance
      Support.simpleSizeMatrixMeasure_unbounded

example :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System
        Support.simpleSizeMatrixMeasure.eval
        Support.scalarOrder := by
  exact
    OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump
      Support.simpleSizeMatrixMeasure
      Support.scalarDominance
      Support.simpleSizeMatrixMeasure_unbounded

end MatrixBarrierArbitraryReach
