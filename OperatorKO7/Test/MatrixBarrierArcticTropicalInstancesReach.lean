import OperatorKO7.Meta.MatrixBarrierArcticTropical_Instances

namespace MatrixBarrierArcticTropicalInstancesReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

#check StepDuplicatingSchema.ArcticMatrixUnitLt
#check StepDuplicatingSchema.ArcticMatrixRowSumLt
#check StepDuplicatingSchema.TropicalMatrixUnitLt
#check StepDuplicatingSchema.TropicalMatrixRowSumLt
#check StepDuplicatingSchema.ArcticMatrixCertificate.of_unitScalarDominance
#check StepDuplicatingSchema.ArcticMatrixCertificate.of_rowSumScalarDominance
#check StepDuplicatingSchema.TropicalMatrixCertificate.of_unitScalarDominance
#check StepDuplicatingSchema.TropicalMatrixCertificate.of_rowSumScalarDominance
#check StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_unit_scalar_dominance_pump
#check StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
#check StepDuplicatingSchema.no_tropicalMatrix_orients_dup_step_of_unit_scalar_dominance_pump
#check StepDuplicatingSchema.no_tropicalMatrix_orients_dup_step_of_rowSum_scalar_dominance_pump
#check OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_unit_of_scalar_dominance_pump
#check OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_rowSum_of_scalar_dominance_pump
#check OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_unit_of_scalar_dominance_pump
#check OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_rowSum_of_scalar_dominance_pump

namespace Support

@[simp] def scalarVec1 (n : Nat) : StepDuplicatingSchema.MatrixVec 1 :=
  fun _ => n

@[simp] def scalarVec2 (n : Nat) : StepDuplicatingSchema.MatrixVec 2 :=
  fun _ => n

@[simp] def oneMatrix1 : StepDuplicatingSchema.MixedMatrix 1 where
  coeff _ _ := 1

@[simp] def diagonalMatrix2 : StepDuplicatingSchema.MixedMatrix 2 where
  coeff i j := if i = j then 1 else 0

def arcticUnitMatrixMeasure1 : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema 1 where
  eval := fun t _ => simpleSize_ACM.eval t
  weight := StepDuplicatingSchema.unitWeight 0
  base_vec := scalarVec1 0
  succ_bias := scalarVec1 1
  succ_mat := oneMatrix1
  wrap_bias := scalarVec1 1
  wrap_left := oneMatrix1
  wrap_right := oneMatrix1
  recur_bias := scalarVec1 1
  recur_base := oneMatrix1
  recur_step := oneMatrix1
  recur_counter := oneMatrix1
  succ_scale := 1
  wrap_left_scale := 1
  wrap_right_scale := 1
  recur_base_scale := 1
  recur_step_scale := 1
  recur_counter_scale := 1
  eval_base := by
    funext i
    fin_cases i
    simp [scalarVec1, ko7Schema, simpleSize_ACM]
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [scalarVec1, oneMatrix1,
      StepDuplicatingSchema.vecAdd,
      StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [scalarVec1, oneMatrix1,
      StepDuplicatingSchema.vecAdd,
      StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM, Nat.add_assoc]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [scalarVec1, oneMatrix1,
      StepDuplicatingSchema.vecAdd,
      StepDuplicatingSchema.MixedMatrix.act,
      ko7Schema, simpleSize_ACM, Nat.add_assoc]
  h_succ_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_wrap_left_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_wrap_right_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_recur_base_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_recur_step_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_recur_counter_respects := by
    simpa using
      StepDuplicatingSchema.MixedMatrix.respectsWeight_unit_of_fixedRow
        (A := oneMatrix1) (tracked := (0 : Fin 1)) (scale := 1)
        (by simp [oneMatrix1])
        (by intro j hj; fin_cases j; contradiction)
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

def arcticMeasure1 : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema 1 where
  eval := fun t _ => StepDuplicatingSchema.ArcticNat.fin (simpleSize_ACM.eval t)
  scalarMeasure := arcticUnitMatrixMeasure1

lemma arcticMeasure1_scalarize :
    ∀ t : Trace,
      StepDuplicatingSchema.arcticFinitePart (arcticMeasure1.eval t) =
        arcticUnitMatrixMeasure1.eval t := by
  intro t
  funext i
  fin_cases i
  simp [arcticMeasure1, arcticUnitMatrixMeasure1]

lemma arcticUnitMatrixMeasure1_unbounded :
    StepDuplicatingSchema.HasUnboundedScalarizedRange arcticUnitMatrixMeasure1 := by
  intro k
  refine ⟨appIter k, ?_⟩
  simpa [arcticUnitMatrixMeasure1, scalarVec1,
      StepDuplicatingSchema.matrixScalarize,
      StepDuplicatingSchema.unitWeight] using
    eval_appIter_ge simpleSize_ACM k

def tropicalRowSumMatrixMeasure2 : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema 2 where
  eval := fun t => scalarVec2 (simpleSize_ACM.eval t)
  weight := StepDuplicatingSchema.allOnesWeight
  base_vec := scalarVec2 0
  succ_bias := scalarVec2 1
  succ_mat := diagonalMatrix2
  wrap_bias := scalarVec2 1
  wrap_left := diagonalMatrix2
  wrap_right := diagonalMatrix2
  recur_bias := scalarVec2 1
  recur_base := diagonalMatrix2
  recur_step := diagonalMatrix2
  recur_counter := diagonalMatrix2
  succ_scale := 1
  wrap_left_scale := 1
  wrap_right_scale := 1
  recur_base_scale := 1
  recur_step_scale := 1
  recur_counter_scale := 1
  eval_base := by
    funext i
    fin_cases i <;> simp [scalarVec2, ko7Schema, simpleSize_ACM]
  eval_succ := by
    intro t
    funext i
    fin_cases i <;>
      simp [scalarVec2, diagonalMatrix2,
        StepDuplicatingSchema.vecAdd,
        StepDuplicatingSchema.MixedMatrix.act,
        ko7Schema, simpleSize_ACM]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i <;>
      simp [scalarVec2, diagonalMatrix2,
        StepDuplicatingSchema.vecAdd,
        StepDuplicatingSchema.MixedMatrix.act,
        ko7Schema, simpleSize_ACM, Nat.add_assoc]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i <;>
      simp [scalarVec2, diagonalMatrix2,
        StepDuplicatingSchema.vecAdd,
        StepDuplicatingSchema.MixedMatrix.act,
        ko7Schema, simpleSize_ACM, Nat.add_assoc]
  h_succ_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_wrap_left_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_wrap_right_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_recur_base_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_recur_step_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_recur_counter_respects := by
    refine StepDuplicatingSchema.MixedMatrix.respectsWeight_allOnes_of_columnSums
      (A := diagonalMatrix2) (scale := 1) ?_
    intro j
    fin_cases j <;> simp [diagonalMatrix2]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

def tropicalMeasure2 : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema 2 where
  eval := tropicalRowSumMatrixMeasure2.eval
  scalarMeasure := tropicalRowSumMatrixMeasure2

lemma tropicalMeasure2_scalarize :
    ∀ t : Trace,
      StepDuplicatingSchema.tropicalFinitePart (tropicalMeasure2.eval t) =
        tropicalRowSumMatrixMeasure2.eval t := by
  intro t
  rfl

lemma tropicalRowSumMatrixMeasure2_unbounded :
    StepDuplicatingSchema.HasUnboundedScalarizedRange tropicalRowSumMatrixMeasure2 := by
  intro k
  refine ⟨appIter k, ?_⟩
  have hk : k ≤ simpleSize_ACM.eval (appIter k) :=
    eval_appIter_ge simpleSize_ACM k
  have hk' : k ≤ simpleSize_ACM.eval (appIter k) + simpleSize_ACM.eval (appIter k) := by
    omega
  have hk'' : k ≤ 2 * simpleSize_ACM.eval (appIter k) := by
    simpa [two_mul] using hk'
  simpa [tropicalRowSumMatrixMeasure2, scalarVec2,
      StepDuplicatingSchema.matrixScalarize,
      StepDuplicatingSchema.allOnesWeight] using hk''

end Support

example :
    ¬ (∀ (b s n : Trace),
      StepDuplicatingSchema.ArcticMatrixUnitLt (0 : Fin 1)
        (Support.arcticMeasure1.eval (app s (recΔ b s n)))
        (Support.arcticMeasure1.eval (recΔ b s (delta n)))) := by
  exact
    StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_unit_scalar_dominance_pump
      (S := ko7Schema)
      (tracked := (0 : Fin 1))
      Support.arcticMeasure1
      rfl
      Support.arcticMeasure1_scalarize
      Support.arcticUnitMatrixMeasure1_unbounded

example :
    ¬ StepDuplicatingSchema.GlobalOrients
        ko7System
        Support.tropicalMeasure2.eval
        StepDuplicatingSchema.TropicalMatrixRowSumLt := by
  exact
    OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_rowSum_of_scalar_dominance_pump
      Support.tropicalMeasure2
      rfl
      Support.tropicalMeasure2_scalarize
      Support.tropicalRowSumMatrixMeasure2_unbounded

end MatrixBarrierArcticTropicalInstancesReach
