import OperatorKO7.Meta.DirectToolSearchMapping
import OperatorKO7.Meta.ExtendedDirectToolSearchMapping
import OperatorKO7.Meta.MatrixToolSearchMapping

/-!
# Tool Search Fragment Coverage

This module packages the current M4 paper-facing fragment coverage ledger as a
catalog over existing wrapper theorems.

Residual exclusions:

- unrestricted nonlinear direct families remain outside this catalog;
- unrestricted matrix classes remain outside this catalog.
-/

namespace OperatorKO7.ToolSearchFragmentCoverage

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.DirectToolSearchMapping
open OperatorKO7.ExtendedDirectToolSearchMapping
open OperatorKO7.MatrixToolSearchMapping

/-- Paper-facing family labels for the theorem-backed tool-search fragment catalog. -/
inductive ToolSearchFragmentFamily
  | directAdditive
  | directAffine
  | directQuadratic
  | directMultilinear
  | directPolynomial
  | extendedCrossQuadratic
  | extendedMaxPlus
  | extendedWPOPolynomial
  | matrixFixedRow
  | matrixRowSum
  | matrixArcticFixedRow
  | matrixArcticRowSum
  | matrixTropicalFixedRow
  | matrixTropicalRowSum
  deriving DecidableEq, Repr

/-- Proposition packaging the direct scalar fragment families covered by the current M4 ledger. -/
abbrev DirectScalarFragmentCoverageCatalog (Sys : StepDuplicatingSystem) : Prop :=
  (∀ F : AdditiveFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : AffineUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : AffineSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : AffineWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : QuadraticUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : QuadraticSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : QuadraticWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MultilinearUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MultilinearSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MultilinearWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : PolynomialUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : PolynomialSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : PolynomialWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·))

/-- The theorem-backed direct scalar fragment families already covered by the M4 ledger. -/
theorem direct_scalar_fragment_coverage_catalog
    {Sys : StepDuplicatingSystem} : DirectScalarFragmentCoverageCatalog Sys := by
  repeat' constructor
  · intro F
    exact additive_fragment_no_global_orientation F
  · intro F
    exact affineUnbounded_fragment_no_global_orientation F
  · intro F
    exact affineSuccPump_fragment_no_global_orientation F
  · intro F
    exact affineWrapPump_fragment_no_global_orientation F
  · intro F
    exact quadraticUnbounded_fragment_no_global_orientation F
  · intro F
    exact quadraticSuccPump_fragment_no_global_orientation F
  · intro F
    exact quadraticWrapPump_fragment_no_global_orientation F
  · intro F
    exact multilinearUnbounded_fragment_no_global_orientation F
  · intro F
    exact multilinearSuccPump_fragment_no_global_orientation F
  · intro F
    exact multilinearWrapPump_fragment_no_global_orientation F
  · intro F
    exact polynomialUnbounded_fragment_no_global_orientation F
  · intro F
    exact polynomialSuccPump_fragment_no_global_orientation F
  · intro F
    exact polynomialWrapPump_fragment_no_global_orientation F

/-- Proposition packaging the extended-direct fragment families covered by the current M4 ledger. -/
abbrev ExtendedDirectFragmentCoverageCatalog (Sys : StepDuplicatingSystem) : Prop :=
  (∀ F : CrossQuadraticUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : CrossQuadraticSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : CrossQuadraticWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MaxUnboundedFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MaxSuccPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : MaxWrapPumpFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (· < ·)) ∧
  (∀ F : WPOPolynomialDirectUnboundedFragment Sys,
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x)) ∧
  (∀ F : WPOPolynomialDirectSuccPumpFragment Sys,
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x)) ∧
  (∀ F : WPOPolynomialDirectWrapPumpFragment Sys,
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x)) ∧
  (∀ F : WPOPolynomialDirectBaseDominanceFailureFragment Sys,
    GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x) →
    ¬ EventuallyDominatedAtBase F.order.measure)

/-- The theorem-backed extended-direct fragment families already covered by the M4 ledger. -/
theorem extended_direct_fragment_coverage_catalog
    {Sys : StepDuplicatingSystem} : ExtendedDirectFragmentCoverageCatalog Sys := by
  repeat' constructor
  · intro F
    exact crossQuadraticUnbounded_fragment_no_global_orientation F
  · intro F
    exact crossQuadraticSuccPump_fragment_no_global_orientation F
  · intro F
    exact crossQuadraticWrapPump_fragment_no_global_orientation F
  · intro F
    exact maxUnbounded_fragment_no_global_orientation F
  · intro F
    exact maxSuccPump_fragment_no_global_orientation F
  · intro F
    exact maxWrapPump_fragment_no_global_orientation F
  · intro F
    exact wpoPolynomialDirectUnbounded_fragment_no_global_orientation F
  · intro F
    exact wpoPolynomialDirectSuccPump_fragment_no_global_orientation F
  · intro F
    exact wpoPolynomialDirectWrapPump_fragment_no_global_orientation F
  · intro F h
    exact
      wpoPolynomialDirectBaseDominanceFailure_fragment_escape_requires_failure_of_base_dominance
        F h

/-- Proposition packaging the matrix projection fragment families covered by the current M4 ledger. -/
abbrev MatrixProjectionFragmentCoverageCatalog (Sys : StepDuplicatingSystem) : Prop :=
  (∀ F : FixedRowFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (VecLeLt F.tracked)) ∧
  (∀ F : RowSumFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval VecLt) ∧
  (∀ F : ArcticFixedRowFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (ArcticMatrixUnitLt F.tracked)) ∧
  (∀ F : ArcticRowSumFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval ArcticMatrixRowSumLt) ∧
  (∀ F : TropicalFixedRowFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval (TropicalMatrixUnitLt F.tracked)) ∧
  (∀ F : TropicalRowSumFragment Sys,
    ¬ GlobalOrients Sys F.measure.eval TropicalMatrixRowSumLt)

/-- The theorem-backed matrix projection fragment families already covered by the M4 ledger. -/
theorem matrix_projection_fragment_coverage_catalog
    {Sys : StepDuplicatingSystem} : MatrixProjectionFragmentCoverageCatalog Sys := by
  repeat' constructor
  · intro F
    exact fixedRow_fragment_no_global_orientation F
  · intro F
    exact rowSum_fragment_no_global_orientation F
  · intro F
    exact arcticFixedRow_fragment_no_global_orientation F
  · intro F
    exact arcticRowSum_fragment_no_global_orientation F
  · intro F
    exact tropicalFixedRow_fragment_no_global_orientation F
  · intro F
    exact tropicalRowSum_fragment_no_global_orientation F

/-- Combined paper-facing coverage ledger for the current theorem-backed tool-search fragments. -/
theorem tool_search_fragment_coverage_catalog
    {Sys : StepDuplicatingSystem} :
    DirectScalarFragmentCoverageCatalog Sys ∧
    ExtendedDirectFragmentCoverageCatalog Sys ∧
    MatrixProjectionFragmentCoverageCatalog Sys := by
  exact
    ⟨direct_scalar_fragment_coverage_catalog,
      ⟨extended_direct_fragment_coverage_catalog,
        matrix_projection_fragment_coverage_catalog⟩⟩

end OperatorKO7.ToolSearchFragmentCoverage
