import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.BarrierPumpDischarge
import OperatorKO7.Meta.MatrixBarrierNatural

/-!
# Context-Closed Lifts of the Pump-Discharged Barriers

`Meta/ContextClosedBarrier.lean` and `Meta/ContextClosedBarrier_FullClosure.lean`
lift the eighty pumped root-level `no_global_step_orientation_*` theorems to the
full context closure `StepCtxFull`. `Meta/BarrierPumpDischarge.lean` and
`Meta/MatrixBarrierNatural.lean` add twenty-six further root-level exclusions
whose growth premises are discharged. This module lifts those twenty-six by the
same bridge, so root and context-closed inventories stay in step at 106 and 106.

Each statement carries exactly the premises of its root-level source; the lift
adds nothing, because every root contraction is a contextual contraction under
the identity context (`MetaSN_KO7.StepCtxFull.root`).
-/

namespace OperatorKO7.ContextClosedBarrierPumpDischarge

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ContextClosedBarrier
open MetaSN_KO7

/-! ## Scalar and pair families -/

theorem no_stepCtxFull_orientation_affine
    (M : AffineCompositionalMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_affine M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_quadratic
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_quadratic M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_cross_quadratic_of_bounded
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_cross_quadratic_of_bounded
    M hbounded (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_multilinear_of_dominated
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
    (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_multilinear_of_dominated
    M hdom (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polynomial_of_dominated
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_polynomial_of_dominated
    M hdom (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_wpoPolynomialDirect_of_dominated
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrientsStepCtxFull (fun t => t) (fun x y => W.gt y x) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_wpoPolynomialDirect_of_dominated
    W hdom (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_max
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_max M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_arctic_primary
    (M : StepDuplicatingSchema.ArcticPrimaryMeasure ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.ArcticLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_arctic_primary M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_tropical_primary
    {β : Type} (M : StepDuplicatingSchema.TropicalPrimaryMeasure ko7Schema β) :
    ¬ GlobalOrientsStepCtxFull M.eval M.lt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_tropical_primary M
    (fun hab => h (StepCtxFull.root hab))

/-! ## Matrix and vector families -/

theorem no_stepCtxFull_orientation_matrixD
    {d : Nat} {tracked : Fin d}
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixD M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix2 M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_lex_of_fst_pos
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
    (hpos : ∃ t : Trace, 1 ≤ (M.eval t).1) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLexLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix2_lex_of_fst_pos
    M hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixFunctional
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixFunctional M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixMix2
    (M : StepDuplicatingSchema.MatrixMix2Measure ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixMix2 M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLexLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixLexD_of_primary_pos
    M hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexPermD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexPermMeasureD ko7Schema d)
    (hpos : ∃ t : Trace,
      1 ≤ M.eval t (StepDuplicatingSchema.permPrimaryIdx M.priority)) :
    ¬ GlobalOrientsStepCtxFull M.eval
      (StepDuplicatingSchema.VecPermLexLt M.priority) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixLexPermD_of_primary_pos
    M hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixArbitrary_of_scalar_dominance_of_pos
    {d : Nat} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop}
    (D : StepDuplicatingSchema.MatrixScalarDominance M.weight R)
    (hpos : ∃ t : Trace,
      1 ≤ StepDuplicatingSchema.matrixScalarize M.weight (M.eval t)) :
    ¬ GlobalOrientsStepCtxFull M.eval R := by
  intro h
  exact
    OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_of_pos
      M D hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix_fixed_row
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix_fixed_row tracked M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix_row_sum
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (hweight : M.weight = StepDuplicatingSchema.rowSumWeight) :
    ¬ GlobalOrientsStepCtxFull
      (fun t => StepDuplicatingSchema.weightedSum
        StepDuplicatingSchema.rowSumWeight (M.eval t)) (· < ·) := by
  intro h
  exact OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix_row_sum M hweight
    (fun hab => h (StepCtxFull.root hab))

/-! ## Certificate-free natural matrix families -/

theorem no_stepCtxFull_orientation_naturalMatrix_of_tracked_strict
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.WrapDiagPositive M i)
    {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop}
    (hR : ∀ {u v : StepDuplicatingSchema.MatrixVec d}, R u v → u i < v i) :
    ¬ GlobalOrientsStepCtxFull M.eval R := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_of_tracked_strict
      M hi hR (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_naturalMatrix_of_tracked_nonincreasing
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.WrapDiagPositive M i)
    {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop}
    (hR : ∀ {u v : StepDuplicatingSchema.MatrixVec d}, R u v → u i ≤ v i)
    (hpos : ∃ t : Trace, 1 ≤ M.eval t i) :
    ¬ GlobalOrientsStepCtxFull M.eval R := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_of_tracked_nonincreasing
      M hi hR hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_naturalMatrix_componentwise
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d) {i : Fin d}
    (hi : StepDuplicatingSchema.WrapDiagPositive M i) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_componentwise
      M hi (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_naturalMatrix_ewz
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d)
    {tracked : Fin d} (hi : StepDuplicatingSchema.WrapDiagPositive M tracked) :
    ¬ GlobalOrientsStepCtxFull M.eval
      (StepDuplicatingSchema.VecLeLt tracked) := by
  intro h
  exact OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_ewz M hi
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_naturalMatrix_lexD_of_primary_pos
    {d : Nat} (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema (d + 1))
    (hi : StepDuplicatingSchema.WrapDiagPositive M (StepDuplicatingSchema.primaryIdx d))
    (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLexLt := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_lexD_of_primary_pos
      M hi hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_naturalMatrix_lexPermD_of_primary_pos
    {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
    (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema (d + 1))
    (hi : StepDuplicatingSchema.WrapDiagPositive M
      (StepDuplicatingSchema.permPrimaryIdx σ))
    (hpos : ∃ t : Trace,
      1 ≤ M.eval t (StepDuplicatingSchema.permPrimaryIdx σ)) :
    ¬ GlobalOrientsStepCtxFull M.eval
      (StepDuplicatingSchema.VecPermLexLt σ) := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_lexPermD_of_primary_pos
      σ M hi hpos (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixArbitrary_unit_certificateFree
    {d : Nat} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d)
    (tracked : Fin d)
    (hweight : M.weight = StepDuplicatingSchema.unitWeight tracked) :
    ¬ GlobalOrientsStepCtxFull M.eval
      (StepDuplicatingSchema.VecLeLt tracked) := by
  intro h
  exact
    OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_matrixArbitrary_unit_certificateFree
      M tracked hweight (fun hab => h (StepCtxFull.root hab))

end OperatorKO7.ContextClosedBarrierPumpDischarge
