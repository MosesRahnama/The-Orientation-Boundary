import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.Impossibility_Lemmas
import OperatorKO7.Meta.ArcticBarrier
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.Conjecture_Boundary
import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.MPO_Precedence_Barrier
import OperatorKO7.Meta.MatrixBarrier2
import OperatorKO7.Meta.MatrixBarrierArbitrary
import OperatorKO7.Meta.MatrixBarrierArbitrary_Instances
import OperatorKO7.Meta.MatrixBarrierArcticTropical
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Instances
import OperatorKO7.Meta.MatrixBarrierD
import OperatorKO7.Meta.MatrixBarrierFunctional
import OperatorKO7.Meta.MatrixBarrierLex
import OperatorKO7.Meta.MatrixBarrierLexD
import OperatorKO7.Meta.MatrixBarrierLexPermD
import OperatorKO7.Meta.MatrixBarrierMix2
import OperatorKO7.Meta.MatrixProjectionCoverage
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.PrecedenceBarrier
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.TropicalBarrier
import OperatorKO7.Meta.WPO_PolynomialBarrier

/-!
# Context-Closed Barrier Full Closure

`Meta/ContextClosedBarrier.lean` lifts eleven root-step barrier families to the full
context closure `StepCtxFull`. This module completes that layer: every remaining
root-level `no_global_step_orientation_*` theorem in the artifact is lifted here by the
same bridge `stepCtxFull_orientation_implies_root`, so the context-closed corollary
covers the whole barrier stack rather than a named subset.

Each statement is unconditional relative to the hypotheses of its root-level source
theorem: the lift introduces no additional side condition, since every root
contraction is a contextual contraction under the identity context
(`MetaSN_KO7.StepCtxFull.root`).

Coverage: 69 families, completing the 11 already carried by
`Meta/ContextClosedBarrier.lean` to the full set of 80 root-level
`no_global_step_orientation_*` theorems in the artifact.

Trust: Mathlib-only; no `sorry`, no `admit`, no new top-level `axiom`, no
`native_decide`, no `@[csimp]`, no `unsafe`. Every declaration is a two-step
elimination through the existing bridge, so the axiom footprint of each lift equals
that of its root-level source theorem.
-/

namespace OperatorKO7.ContextClosedBarrierFullClosure

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ContextClosedBarrier
open OperatorKO7.MetaConjectureBoundary
open OperatorKO7.Impossibility
open MetaSN_KO7

theorem no_stepCtxFull_orientation_affine_of_unbounded
    (M : AffineCompositionalMeasure) (hunbounded : StepDuplicatingSchema.HasUnboundedRange M.toSchemaMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.CompositionalImpossibility.no_global_step_orientation_affine_of_unbounded M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_arcticMatrix_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d) (C : StepDuplicatingSchema.ArcticMatrixCertificate d) (hweight : C.weight = M.scalarMeasure.weight) (hscalarize : ∀ t : Trace, C.scalarize (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval C.lt := by
  intro h
  exact OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_of_scalar_dominance_pump M C hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_arcticMatrix_rowSum_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d) (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.allOnesWeight) (hscalarize : ∀ t : Trace, StepDuplicatingSchema.arcticFinitePart (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.ArcticMatrixRowSumLt := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_rowSum_of_scalar_dominance_pump M hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_arcticMatrix_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d} (M : StepDuplicatingSchema.ArcticMatrixMeasure ko7Schema d) (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.unitWeight tracked) (hscalarize : ∀ t : Trace, StepDuplicatingSchema.arcticFinitePart (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (StepDuplicatingSchema.ArcticMatrixUnitLt tracked) := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_unit_of_scalar_dominance_pump M hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_arctic_primary_of_unbounded
    (M : StepDuplicatingSchema.ArcticPrimaryMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M.projectedMax) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.ArcticLt := by
  intro h
  exact OperatorKO7.ArcticBarrier.no_global_step_orientation_arctic_primary_of_unbounded M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_constellation :
    ¬ GlobalOrientsStepCtxFull (fun t => ConstellationFailure.constellationSize (ConstellationFailure.toConstellation t)) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_constellation
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_cross_quadratic_of_succ_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticCrossTermBarrier.no_global_step_orientation_cross_quadratic_of_succ_pump M h_succ_bias h_succ_scale hbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_cross_quadratic_of_unbounded
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeX M) (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticCrossTermBarrier.no_global_step_orientation_cross_quadratic_of_unbounded M hunbounded hbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_cross_quadratic_of_wrap_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticCrossTermBarrier.no_global_step_orientation_cross_quadratic_of_wrap_pump M h_wrap_bias hbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_flag :
    ¬ GlobalOrientsStepCtxFull FlagFailure.deltaFlagTop (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_flag
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_headPrecedence
    (rank : OpHead → Nat) :
    ¬ GlobalOrientsStepCtxFull (headPrecedenceMeasure rank) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_headPrecedence rank
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_headPrecedenceFamily
    (M : OperatorKO7.PrecedenceBarrier.HeadPrecedenceFamily) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.PrecedenceBarrier.no_global_step_orientation_headPrecedenceFamily M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_kappa :
    ¬ GlobalOrientsStepCtxFull FailedMeasures.kappa (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_kappa
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_kappa_plus_k
    (k : Nat) :
    ¬ GlobalOrientsStepCtxFull (fun t => FailedMeasures.kappa t + k) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_kappa_plus_k k
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_kappa_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrientsStepCtxFull (fun t => f (FailedMeasures.kappa t)) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_kappa_strictMono f hf
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_linearWeight
    (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) :
    ¬ GlobalOrientsStepCtxFull (linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_lex_of_componentwise_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRange1 M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLexLt := by
  intro h
  exact OperatorKO7.MatrixBarrierLex.no_global_step_orientation_matrix2_lex_of_componentwise_pump M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_lex_of_succ_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.PairLexLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierLex.no_global_step_orientation_matrix2_lex_of_succ_pump M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_lex_of_wrap_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.PairLexLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierLex.no_global_step_orientation_matrix2_lex_of_wrap_pump M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_of_componentwise_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRange1 M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact OperatorKO7.MatrixBarrier2.no_global_step_orientation_matrix2_of_componentwise_pump M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_of_succ_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.PairLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrier2.no_global_step_orientation_matrix2_of_succ_pump M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix2_of_wrap_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.PairLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrier2.no_global_step_orientation_matrix2_of_wrap_pump M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixArbitrary_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d) {R : StepDuplicatingSchema.MatrixVec d → StepDuplicatingSchema.MatrixVec d → Prop} (D : StepDuplicatingSchema.MatrixScalarDominance M.weight R) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval R := by
  intro h
  exact OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump M D hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixArbitrary_rowSum_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d) (hweight : M.weight = StepDuplicatingSchema.allOnesWeight) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArbitraryInstances.no_global_step_orientation_matrixArbitrary_rowSum_of_scalar_dominance_pump M hweight hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixArbitrary_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d} (M : StepDuplicatingSchema.MatrixArbitraryMeasure ko7Schema d) (hweight : M.weight = StepDuplicatingSchema.unitWeight tracked) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval (StepDuplicatingSchema.VecLeLt tracked) := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArbitraryInstances.no_global_step_orientation_matrixArbitrary_unit_of_scalar_dominance_pump M hweight hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixD_of_componentwise_pump
    {d : Nat} (tracked : Fin d) (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeTracked M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.MatrixBarrierD.no_global_step_orientation_matrixD_of_componentwise_pump tracked M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixD_of_succ_pump
    {d : Nat} (tracked : Fin d) (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierD.no_global_step_orientation_matrixD_of_succ_pump tracked M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixD_of_wrap_pump
    {d : Nat} (tracked : Fin d) (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierD.no_global_step_orientation_matrixD_of_wrap_pump tracked M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixFunctional_of_componentwise_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.MatrixBarrierFunctional.no_global_step_orientation_matrixFunctional_of_componentwise_pump M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixFunctional_of_succ_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierFunctional.no_global_step_orientation_matrixFunctional_of_succ_pump M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixFunctional_of_wrap_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierFunctional.no_global_step_orientation_matrixFunctional_of_wrap_pump M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexD_of_succ_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLexLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_of_succ_pump M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexD_of_unbounded_primary
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d) (hunbounded : StepDuplicatingSchema.HasUnboundedPrimaryRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLexLt := by
  intro h
  exact OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_of_unbounded_primary M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexD_of_wrap_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → StepDuplicatingSchema.VecLexLt (M.eval b) (M.eval a)) := by
  intro h
  exact OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_of_wrap_pump M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexD_with_primary_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLexLt := by
  intro h
  exact OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_with_primary_pump M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixLexPermD_with_primary_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
    ¬ GlobalOrientsStepCtxFull M.eval (StepDuplicatingSchema.VecPermLexLt M.priority) := by
  intro h
  exact OperatorKO7.MatrixBarrierLexPermD.no_global_step_orientation_matrixLexPermD_with_primary_pump M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrixMix2_of_sum_pump
    (M : StepDuplicatingSchema.MatrixMix2Measure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeSum M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact OperatorKO7.MatrixBarrierMix2.no_global_step_orientation_matrixMix2_of_sum_pump M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix_fixed_row_of_componentwise_pump
    {d : Nat} (tracked : Fin d) (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeTracked M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.MatrixProjectionCoverage.no_global_step_orientation_matrix_fixed_row_of_componentwise_pump tracked M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_matrix_row_sum_of_componentwise_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d) (hweight : M.weight = StepDuplicatingSchema.rowSumWeight) (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact OperatorKO7.MatrixProjectionCoverage.no_global_step_orientation_matrix_row_sum_of_componentwise_pump M hweight hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_maxDepth
    (M : OperatorKO7.DepthBarrier.MaxDepthMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.DepthBarrier.no_global_step_orientation_maxDepth M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_max_of_succ_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema) (h_succ_const : 1 ≤ M.succ_const) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MaxBarrier.no_global_step_orientation_max_of_succ_pump M h_succ_const
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_max_of_unbounded
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MaxBarrier.no_global_step_orientation_max_of_unbounded M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_max_of_wrap_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema) (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MaxBarrier.no_global_step_orientation_max_of_wrap_pump M h_wrap_drift
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_mpo_bad_prec :
    ¬ (∀ {a b : Trace}, StepCtxFull a b → OperatorKO7.MPOPrecedenceBarrier.MPOBad a b) := by
  intro h
  exact OperatorKO7.MPOPrecedenceBarrier.no_global_step_orientation_mpo_bad_prec
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_multilinear_of_succ_pump
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MultilinearBarrier.no_global_step_orientation_multilinear_of_succ_pump M h_succ_bias h_succ_scale hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_multilinear_of_unbounded
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeML M) (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MultilinearBarrier.no_global_step_orientation_multilinear_of_unbounded M hunbounded hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_multilinear_of_wrap_pump
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.MultilinearBarrier.no_global_step_orientation_multilinear_of_wrap_pump M h_wrap_bias hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_nestingDepth :
    ¬ GlobalOrientsStepCtxFull nestingDepth (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_nestingDepth
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_nodeCount :
    ¬ GlobalOrientsStepCtxFull nodeCount (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_nodeCount
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polyMul
    (w : Nat) :
    ¬ GlobalOrientsStepCtxFull (polyMul w) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_polyMul w
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polynomial_of_succ_pump
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_succ_pump M h_succ_bias h_succ_scale hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polynomial_of_unbounded
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly M) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_unbounded M hunbounded hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polynomial_of_wrap_pump
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_wrap_pump M h_wrap_bias hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_polynomial_with_pump
    (M : StepDuplicatingSchema.PolynomialMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.PumpedBarrierClasses.no_global_step_orientation_polynomial_with_pump M
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_quadratic_of_succ_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticBarrier.no_global_step_orientation_quadratic_of_succ_pump M h_succ_bias h_succ_scale
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_quadratic_of_unbounded
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeQ M) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticBarrier.no_global_step_orientation_quadratic_of_unbounded M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_quadratic_of_wrap_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact OperatorKO7.QuadraticBarrier.no_global_step_orientation_quadratic_of_wrap_pump M h_wrap_bias
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_simpleSize :
    ¬ GlobalOrientsStepCtxFull UncheckedRecursionFailure.simpleSize (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_simpleSize
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_simpleSize_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrientsStepCtxFull (fun t => f (UncheckedRecursionFailure.simpleSize t)) (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_simpleSize_strictMono f hf
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_simple_lex :
    ¬ GlobalOrientsStepCtxFull (fun t => (FailedMeasures.kappa t, FailedMeasures.mu t)) (Prod.Lex (· < ·) (· < ·)) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_simple_lex
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_standardTreeDepth :
    ¬ GlobalOrientsStepCtxFull MetaConjectureBoundary.treeDepth (· < ·) := by
  intro h
  exact OperatorKO7.DepthBarrier.no_global_step_orientation_standardTreeDepth
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_treeDepth :
    ¬ GlobalOrientsStepCtxFull treeDepth (· < ·) := by
  intro h
  exact OperatorKO7.MetaConjectureBoundary.no_global_step_orientation_treeDepth
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_tropicalMatrix_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d) (C : StepDuplicatingSchema.TropicalMatrixCertificate d) (hweight : C.weight = M.scalarMeasure.weight) (hscalarize : ∀ t : Trace, C.scalarize (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval C.lt := by
  intro h
  exact OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_of_scalar_dominance_pump M C hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_tropicalMatrix_rowSum_of_scalar_dominance_pump
    {d : Nat} (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d) (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.allOnesWeight) (hscalarize : ∀ t : Trace, StepDuplicatingSchema.tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.TropicalMatrixRowSumLt := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_rowSum_of_scalar_dominance_pump M hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_tropicalMatrix_unit_of_scalar_dominance_pump
    {d : Nat} {tracked : Fin d} (M : StepDuplicatingSchema.TropicalMatrixMeasure ko7Schema d) (hweight : M.scalarMeasure.weight = StepDuplicatingSchema.unitWeight tracked) (hscalarize : ∀ t : Trace, StepDuplicatingSchema.tropicalFinitePart (M.eval t) = M.scalarMeasure.eval t) (hunbounded : StepDuplicatingSchema.HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (StepDuplicatingSchema.TropicalMatrixUnitLt tracked) := by
  intro h
  exact OperatorKO7.StepDuplicating.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_unit_of_scalar_dominance_pump M hweight hscalarize hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_tropical_primary_of_unbounded
    {β : Type} (M : StepDuplicatingSchema.TropicalPrimaryMeasure ko7Schema β) (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M.projectedMax) :
    ¬ GlobalOrientsStepCtxFull M.eval M.lt := by
  intro h
  exact OperatorKO7.TropicalBarrier.no_global_step_orientation_tropical_primary_of_unbounded M hunbounded
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_wpoPolynomialDirect_of_succ_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema) (h_succ_bias : 1 ≤ W.measure.succ_bias) (h_succ_scale : 1 ≤ W.measure.succ_scale) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrientsStepCtxFull (fun t => t) (fun x y => W.gt y x) := by
  intro h
  exact OperatorKO7.WPOPolynomialBarrier.no_global_step_orientation_wpoPolynomialDirect_of_succ_pump W h_succ_bias h_succ_scale hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_wpoPolynomialDirect_of_unbounded
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema) (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrientsStepCtxFull (fun t => t) (fun x y => W.gt y x) := by
  intro h
  exact OperatorKO7.WPOPolynomialBarrier.no_global_step_orientation_wpoPolynomialDirect_of_unbounded W hunbounded hdom
    (fun hab => h (StepCtxFull.root hab))

theorem no_stepCtxFull_orientation_wpoPolynomialDirect_of_wrap_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema) (h_wrap_bias : 1 ≤ W.measure.wrap_const + W.measure.wrap_right * W.measure.c_base) (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrientsStepCtxFull (fun t => t) (fun x y => W.gt y x) := by
  intro h
  exact OperatorKO7.WPOPolynomialBarrier.no_global_step_orientation_wpoPolynomialDirect_of_wrap_pump W h_wrap_bias hdom
    (fun hab => h (StepCtxFull.root hab))

end OperatorKO7.ContextClosedBarrierFullClosure
