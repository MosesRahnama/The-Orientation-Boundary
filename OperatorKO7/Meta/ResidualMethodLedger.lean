import OperatorKO7.Meta.MatrixResidualTaxonomy
import OperatorKO7.Meta.ResidualMethodClosureCatalog

/-!
# Residual Method Ledger

Unified per-family status carrier consistent with the WS-F
`ResidualCoverageManifest`. This module is the canonical upstream Lean
home of the four-element `ResidualCoverageStatus` enum
`{closed, conditional, adapter_only, open}`. Lane W's
`ToolSearchFragmentCoverageResidual.lean` imports from this module.

Headline theorem: `residual_method_ledger_consistent` — the ledger
classifies every known matrix residual family and every cross-family
RMCC row under the WS-F status vocabulary, and the classification is
consistent with the underlying source-catalog status functions from
`MatrixResidualTaxonomy` and `ResidualMethodClosureCatalog`.

No `axiom`, no `sorry`, no `PartialProgressClaim` carriers.
All theorems discharged via `decide` or direct case analysis.
-/

namespace OperatorKO7.ResidualMethodLedger

open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.ResidualMethodClosureCatalog

/-! ## WS-F four-element coverage status enum -/

/-- The four-element coverage status vocabulary used by the WS-F
`ResidualCoverageManifest`. Hard invariant per `LEDGER_ENGINE.md`
§3.2 row WS-F: NO BLANKET CLOSURE CLAIM. -/
inductive ResidualCoverageStatus
  | closed        -- unconditional Lean theorem closes the family
  | conditional   -- Lean theorem under a named hypothesis
  | adapter_only  -- closure goes via an external adapter
  | open_status   -- explicit named-obstruction record
  deriving DecidableEq, Repr

/-! ## Mappings from existing upstream status enums -/

/-- Inject a `MatrixClosureStatus` into the WS-F four-element status.
Maps:
  - `reducedToExistingTheorem` / `certifiedSuccess` /
    `closedByUnrestrictedSplitFinalCatalog` → `closed`
  - `licensedEscape` → `adapter_only`  (closure via external adapter)
  - `notYetMethodClass` / `blocked` → `open_status` -/
def matrixClosureStatus_to_wsf :
    MatrixClosureStatus → ResidualCoverageStatus
  | .reducedToExistingTheorem            => .closed
  | .certifiedSuccess                    => .closed
  | .closedByUnrestrictedSplitFinalCatalog => .closed
  | .licensedEscape                      => .adapter_only
  | .notYetMethodClass                   => .open_status
  | .blocked                             => .open_status

/-- Inject a `ResidualMethodClosureStatus` into the WS-F four-element
status. The upstream enum carries exactly five tags. Maps:
  - `closedByLeanTheorem` / `certifiedSuccess` → `closed`
  - `reducedToExistingTheorem` → `conditional` (the reduction cites
    an existing theorem; the WS-F manifest records the cited theorem
    name as the `hypothesis_anchor`)
  - `licensedEscape` → `adapter_only`
  - `blocked` → `open_status` -/
def rmccStatus_to_wsf :
    ResidualMethodClosureStatus → ResidualCoverageStatus
  | .closedByLeanTheorem        => .closed
  | .certifiedSuccess           => .closed
  | .reducedToExistingTheorem   => .conditional
  | .licensedEscape             => .adapter_only
  | .blocked                    => .open_status

/-! ## Ledger row type -/

/-- A single row in the WS-F residual-method ledger. Carries the
family identifier (one of the two upstream inductive types) plus the
projected WS-F coverage status. -/
inductive ResidualLedgerFamily
  -- matrix residual subfamilies (10 rows from MatrixResidualTaxonomy)
  | matrixRow    (f : MatrixResidualFamily)
  -- cross-family RMCC rows (25 rows from ResidualMethodClosureCatalog)
  | rmccRow      (r : ResidualMethodClosureCatalogRow)
  deriving DecidableEq, Repr

/-- Project the WS-F coverage status of any ledger family. -/
def residualLedgerStatus : ResidualLedgerFamily → ResidualCoverageStatus
  | .matrixRow f =>
    matrixClosureStatus_to_wsf (matrixResidualClosureStatus f)
  | .rmccRow r =>
    rmccStatus_to_wsf (residualMethodClosureCatalogRowStatus r)

/-! ## Canonical ledger rows -/

/-- Complete ordered list of all residual-method ledger rows. -/
def residualLedgerRows : List ResidualLedgerFamily :=
  -- 10 matrix rows
  (matrixResidualFamilies.map .matrixRow) ++
  -- 25 RMCC rows
  (residualMethodClosureCatalogRows.map .rmccRow)

theorem residualLedgerRows_length :
    residualLedgerRows.length = 35 := by
  decide

theorem residualLedgerRows_nodup :
    residualLedgerRows.Nodup := by
  decide

/-! ## Headline theorem: residual_method_ledger_consistent -/

/-- The WS-F consistency predicate: for each ledger family, the
projected status is the correct WS-F classification derived from the
upstream source-catalog functions. -/
def ResidualLedgerConsistent : Prop :=
  ∀ family : ResidualLedgerFamily,
    family ∈ residualLedgerRows ∧
    residualLedgerStatus family =
      match family with
      -- matrix rows: map matrixResidualClosureStatus → WS-F enum
      | .matrixRow .componentwiseWeakStrict     => .closed
      | .matrixRow .paretoProduct               => .closed
      | .matrixRow .lexPriority                 => .closed
      | .matrixRow .permutationLexPriority      => .closed
      | .matrixRow .scalarizableWeight          => .closed
      | .matrixRow .arcticFull                  => .adapter_only
      | .matrixRow .tropicalFull                => .adapter_only
      | .matrixRow .importDependentMatrix       => .adapter_only
      | .matrixRow .unconstrainedRelation       => .open_status
      | .matrixRow .unconstrainedRelationClosed => .closed
      -- RMCC rows
      | .rmccRow .matrixComponentwiseWeakStrictReduction     => .conditional
      | .rmccRow .matrixParetoProductReduction               => .conditional
      | .rmccRow .matrixLexPriorityReduction                 => .conditional
      | .rmccRow .matrixPermutationLexPriorityReduction      => .conditional
      | .rmccRow .matrixScalarizableWeightReduction          => .conditional
      | .rmccRow .matrixArcticFullLicensedEscape             => .adapter_only
      | .rmccRow .matrixTropicalFullLicensedEscape           => .adapter_only
      | .rmccRow .matrixImportDependentLicensedEscape        => .adapter_only
      | .rmccRow .matrixUnconstrainedRelationClosedByExactSplit => .closed
      | .rmccRow .fbiFinalRouteStatusCatalog                 => .closed
      | .rmccRow .fbiAdequacyBoundaryClosed                  => .closed
      | .rmccRow .genericDPDirectPairExtraction              => .open_status
      | .rmccRow .genericDPTransformedCallRoute              => .adapter_only
      | .rmccRow .genericDPImportedOrdering                  => .adapter_only
      | .rmccRow .genericDPCertifiedEngine                   => .closed
      | .rmccRow .semanticTransparentWholeTermMeasure        => .conditional
      | .rmccRow .semanticImportedModelLogicalRelation       => .adapter_only
      | .rmccRow .semanticCertifiedExternalEngine            => .closed
      | .rmccRow .nonlinearBoundedDegreeProjection           => .conditional
      | .rmccRow .nonlinearBoundedCrossTermQuadratic         => .closed
      | .rmccRow .nonlinearBoundedMultilinear                => .closed
      | .rmccRow .nonlinearWpoPolynomialBranch               => .closed
      | .rmccRow .nonlinearMaxPlusDirectFragment             => .closed
      | .rmccRow .nonlinearGlobalCrossCoupledWitness         => .adapter_only
      | .rmccRow .nonlinearUnconstrainedDirectExactLawBoundary => .closed

/-- **R.1 headline theorem.**
The WS-F residual-method ledger is consistent: every family row is
present in the canonical inventory, and each row's projected WS-F
status matches the classification derived from the upstream
`MatrixResidualTaxonomy` and `ResidualMethodClosureCatalog` source
functions. No `axiom`; no `sorry`; closed by decidable computation. -/
theorem residual_method_ledger_consistent :
    ResidualLedgerConsistent := by
  intro family
  constructor
  · -- membership: every family is in residualLedgerRows
    cases family with
    | matrixRow f =>
      simp only [residualLedgerRows, List.mem_append, List.mem_map]
      left
      exact ⟨f, (matrixResidualFamilies_complete_exact f).2
        (by cases f <;> simp), rfl⟩
    | rmccRow r =>
      simp only [residualLedgerRows, List.mem_append, List.mem_map]
      right
      -- upstream `..._complete_exact` is now a direct membership statement
      exact ⟨r, residualMethodClosureCatalogRows_complete_exact r, rfl⟩
  · -- status consistency: decidable by case analysis
    cases family with
    | matrixRow f => cases f <;> rfl
    | rmccRow r   => cases r <;> rfl

/-- The ledger contains at least one `closed` row. -/
theorem residual_method_ledger_has_closed :
    ∃ f : ResidualLedgerFamily,
      f ∈ residualLedgerRows ∧
      residualLedgerStatus f = .closed :=
  ⟨.matrixRow .paretoProduct,
   (residual_method_ledger_consistent (.matrixRow .paretoProduct)).1,
   (residual_method_ledger_consistent (.matrixRow .paretoProduct)).2⟩

/-- The ledger contains at least one `open_status` row (non-overclaim). -/
theorem residual_method_ledger_has_open :
    ∃ f : ResidualLedgerFamily,
      f ∈ residualLedgerRows ∧
      residualLedgerStatus f = .open_status :=
  ⟨.matrixRow .unconstrainedRelation,
   (residual_method_ledger_consistent (.matrixRow .unconstrainedRelation)).1,
   (residual_method_ledger_consistent (.matrixRow .unconstrainedRelation)).2⟩

/-- The ledger contains at least one `adapter_only` row. -/
theorem residual_method_ledger_has_adapter_only :
    ∃ f : ResidualLedgerFamily,
      f ∈ residualLedgerRows ∧
      residualLedgerStatus f = .adapter_only :=
  ⟨.matrixRow .arcticFull,
   (residual_method_ledger_consistent (.matrixRow .arcticFull)).1,
   (residual_method_ledger_consistent (.matrixRow .arcticFull)).2⟩

/-- The ledger contains at least one `conditional` row. -/
theorem residual_method_ledger_has_conditional :
    ∃ f : ResidualLedgerFamily,
      f ∈ residualLedgerRows ∧
      residualLedgerStatus f = .conditional :=
  ⟨.rmccRow .matrixComponentwiseWeakStrictReduction,
   (residual_method_ledger_consistent
     (.rmccRow .matrixComponentwiseWeakStrictReduction)).1,
   (residual_method_ledger_consistent
     (.rmccRow .matrixComponentwiseWeakStrictReduction)).2⟩

end OperatorKO7.ResidualMethodLedger
