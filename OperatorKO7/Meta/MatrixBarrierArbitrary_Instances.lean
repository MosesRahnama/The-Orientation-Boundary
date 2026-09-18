import OperatorKO7.Meta.MatrixBarrierArbitrary

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

/-- Unit weight on one explicitly chosen row. -/
@[simp] def unitWeight {d : Nat} (tracked : Fin d) : MatrixVec d :=
  fun i => if i = tracked then 1 else 0

/-- All-ones row-sum weight. -/
@[simp] def allOnesWeight {d : Nat} : MatrixVec d :=
  fun _ => 1

lemma matrixScalarize_unitWeight
    {d : Nat} (tracked : Fin d) (v : MatrixVec d) :
    matrixScalarize (unitWeight tracked) v = v tracked := by
  unfold matrixScalarize unitWeight
  rw [sum_eq_single tracked]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

lemma matrixScalarize_allOnesWeight
    {d : Nat} (v : MatrixVec d) :
    matrixScalarize (allOnesWeight) v = ∑ i, v i := by
  unfold matrixScalarize allOnesWeight
  refine sum_congr rfl ?_
  intro i _
  simp

namespace MixedMatrix

/-- A fixed-row scalarization certificate: the chosen row is supported only on its tracked
column, so unit-weight scalarization commutes with matrix action via that row's scale. -/
theorem respectsWeight_unit_of_fixedRow
    {d : Nat} (A : MixedMatrix d) (tracked : Fin d) (scale : Nat)
    (hdiag : A.coeff tracked tracked = scale)
    (hoff : ∀ j : Fin d, j ≠ tracked → A.coeff tracked j = 0) :
    A.RespectsWeight (unitWeight tracked) scale := by
  intro j
  have hcolumn : weightedColumn (unitWeight tracked) A j = A.coeff tracked j := by
    unfold weightedColumn unitWeight
    rw [sum_eq_single tracked]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [hcolumn]
  by_cases hj : j = tracked
  · subst hj
    simp [unitWeight, hdiag]
  · simp [unitWeight, hj, hoff j hj]

/-- Equal column sums certify the all-ones scalarization. -/
theorem respectsWeight_allOnes_of_columnSums
    {d : Nat} (A : MixedMatrix d) (scale : Nat)
    (hcol : ∀ j : Fin d, ∑ i, A.coeff i j = scale) :
    A.RespectsWeight (allOnesWeight) scale := by
  intro j
  unfold weightedColumn allOnesWeight
  simp [hcol j]

end MixedMatrix

/-- Fixed-row / unit-weight instance of the arbitrary scalarization barrier. -/
theorem no_matrixArbitrary_orients_dup_step_of_unit_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixArbitraryMeasure S d)
    (hweight : M.weight = unitWeight tracked)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ (∀ (b s n : S.T),
      VecLeLt tracked
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  refine no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump M ?_ hunbounded
  refine ⟨?_⟩
  intro u v h
  simpa [hweight] using
    (MatrixScalarDominance.of_pointwise_le_lt (weight := unitWeight tracked) tracked).nonstrict h

/-- Row-sum / all-ones instance of the arbitrary scalarization barrier. -/
theorem no_matrixArbitrary_orients_dup_step_of_rowSum_scalar_dominance_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    (hweight : M.weight = allOnesWeight)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ (∀ (b s n : S.T),
      VecLt
        (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  refine no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump M ?_ hunbounded
  refine ⟨?_⟩
  intro u v h
  simpa [hweight] using
    (MatrixScalarDominance.of_pointwise_lt (weight := allOnesWeight)).nonstrict h

end StepDuplicatingSchema

namespace MatrixBarrierArbitraryInstances

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the fixed-row / unit-weight arbitrary scalarization barrier. -/
theorem no_global_step_orientation_matrixArbitrary_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d}
    (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    (hweight : M.weight = StepDuplicatingSchema.unitWeight tracked)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (StepDuplicatingSchema.VecLeLt tracked) := by
  intro h
  exact
    StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_unit_scalar_dominance_pump
      (S := ko7Schema) M hweight hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 specialization of the row-sum / all-ones arbitrary scalarization barrier. -/
theorem no_global_step_orientation_matrixArbitrary_rowSum_of_scalar_dominance_pump
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    (hweight : M.weight = StepDuplicatingSchema.allOnesWeight)
    (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact
    StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_rowSum_scalar_dominance_pump
      (S := ko7Schema) M hweight hunbounded
      (fun b s n => h (ko7System.dup_step b s n))

end MatrixBarrierArbitraryInstances

end OperatorKO7.StepDuplicating
