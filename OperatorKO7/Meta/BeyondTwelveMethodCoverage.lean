import OperatorKO7.Meta.ResidualMethodLedger
import OperatorKO7.Meta.UniversalFirstOrderDichotomy

/-!
# Additional termination-method families

This module classifies methods outside the core matrix-barrier families. Each
constructor maps to a `ResidualCoverageStatus`. The finite list and status map
record the classifications encoded by `beyondTwelveStatus`.

The theorem `beyond_twelve_coverage_status_catalog` checks that every declared
family is listed with its assigned status.

Trust: kernel-only. No `axiom` or `sorry`.
-/

namespace OperatorKO7.BeyondTwelveMethodCoverage

open OperatorKO7.ResidualMethodLedger
open OperatorKO7.UniversalFirstOrderDichotomy

/-! ## Additional method families -/

/-- The 12 constructors name methods beyond the 10 `MatrixResidualFamily` constructors. -/
inductive BeyondTwelveFamily
  -- Dependency-pair methods
  | dpDirectPairExtraction
  | dpTransformedCallRoute
  | dpImportedOrdering
  | dpCertifiedEngine
  -- Usable-rules method
  | usableRulesConditional
  -- Semantic-labeling methods
  | semanticTransparentWholeTermMeasure
  | semanticImportedModelLogicalRelation
  | semanticCertifiedExternalEngine
  -- Match-bounds method
  | matchBoundsConditional
  -- Size-change method
  | sizeChangeOpen
  -- FBI adequacy condition
  | fbiAdequacyConditional
  -- Tool-search fragment residual
  | toolSearchResidualOpen
  deriving DecidableEq, Repr

/-! ## Coverage status classification -/

/-- Status assigned to each additional method family.

- `dpDirectPairExtraction`: `open_status`; no certified extraction method closes it.
- `dpTransformedCallRoute`: `adapter_only`; represented by `w2LicensedEscape`.
- `dpImportedOrdering`: `adapter_only`; represented by `w1LicensedEscape`.
- `dpCertifiedEngine`: `closed`; represented by `genericDPMember`.
- `usableRulesConditional`: `conditional`; requires usable-rules soundness.
- `semanticTransparentWholeTermMeasure`: `conditional`; requires transparent-polynomial dominance.
- `semanticImportedModelLogicalRelation`: `adapter_only`; uses an imported model-logic oracle.
- `semanticCertifiedExternalEngine`: `closed`; represented by `ko7CertifiedExternal`.
- `matchBoundsConditional`: `conditional`; requires a match-bound certificate for each obligation.
- `sizeChangeOpen`: `open_status`; no certified size-change method is included.
- `fbiAdequacyConditional`: `conditional`; requires residual-adequacy support.
- `toolSearchResidualOpen`: `open_status`; tool-search residual coverage is incomplete. -/
def beyondTwelveStatus : BeyondTwelveFamily → ResidualCoverageStatus
  | .dpDirectPairExtraction          => .open_status
  | .dpTransformedCallRoute          => .adapter_only
  | .dpImportedOrdering              => .adapter_only
  | .dpCertifiedEngine               => .closed
  | .usableRulesConditional          => .conditional
  | .semanticTransparentWholeTermMeasure => .conditional
  | .semanticImportedModelLogicalRelation => .adapter_only
  | .semanticCertifiedExternalEngine => .closed
  | .matchBoundsConditional          => .conditional
  | .sizeChangeOpen                  => .open_status
  | .fbiAdequacyConditional          => .conditional
  | .toolSearchResidualOpen          => .open_status

/-! ## Finite family list -/

/-- The finite list of all `BeyondTwelveFamily` constructors. -/
def beyondTwelveFamilies : List BeyondTwelveFamily :=
  [ .dpDirectPairExtraction
  , .dpTransformedCallRoute
  , .dpImportedOrdering
  , .dpCertifiedEngine
  , .usableRulesConditional
  , .semanticTransparentWholeTermMeasure
  , .semanticImportedModelLogicalRelation
  , .semanticCertifiedExternalEngine
  , .matchBoundsConditional
  , .sizeChangeOpen
  , .fbiAdequacyConditional
  , .toolSearchResidualOpen
  ]

theorem beyondTwelveFamilies_nodup :
    beyondTwelveFamilies.Nodup := by decide

theorem beyondTwelveFamilies_length :
    beyondTwelveFamilies.length = 12 := by decide

theorem beyondTwelveFamilies_complete :
    ∀ f : BeyondTwelveFamily, f ∈ beyondTwelveFamilies := by
  intro f; cases f <;> decide

/-! ## Status consistency theorem -/

/-- Every family appears in the finite list and has the status assigned by `beyondTwelveStatus`. -/
def BeyondTwelveCoverageConsistent : Prop :=
  ∀ f : BeyondTwelveFamily,
    f ∈ beyondTwelveFamilies ∧
    beyondTwelveStatus f =
      match f with
      | .dpDirectPairExtraction          => .open_status
      | .dpTransformedCallRoute          => .adapter_only
      | .dpImportedOrdering              => .adapter_only
      | .dpCertifiedEngine               => .closed
      | .usableRulesConditional          => .conditional
      | .semanticTransparentWholeTermMeasure => .conditional
      | .semanticImportedModelLogicalRelation => .adapter_only
      | .semanticCertifiedExternalEngine => .closed
      | .matchBoundsConditional          => .conditional
      | .sizeChangeOpen                  => .open_status
      | .fbiAdequacyConditional          => .conditional
      | .toolSearchResidualOpen          => .open_status

/--
Proves: every `BeyondTwelveFamily` constructor occurs in the finite list and
its status matches the encoded case table.
Trust: kernel-only. No `axiom` or `sorry`; the proof uses finite case analysis.
Scope: the declared family constructors and their status map.
-/
theorem beyond_twelve_coverage_status_catalog :
    BeyondTwelveCoverageConsistent := by
  intro f
  exact ⟨beyondTwelveFamilies_complete f, by cases f <;> rfl⟩

/-- The finite family contains an `open_status` member. -/
theorem beyond_twelve_catalog_has_open :
    ∃ f : BeyondTwelveFamily,
      f ∈ beyondTwelveFamilies ∧
      beyondTwelveStatus f = .open_status :=
  ⟨.sizeChangeOpen,
   (beyond_twelve_coverage_status_catalog .sizeChangeOpen).1,
   (beyond_twelve_coverage_status_catalog .sizeChangeOpen).2⟩

/-- The finite family contains a `closed` member. -/
theorem beyond_twelve_catalog_has_closed :
    ∃ f : BeyondTwelveFamily,
      f ∈ beyondTwelveFamilies ∧
      beyondTwelveStatus f = .closed :=
  ⟨.dpCertifiedEngine,
   (beyond_twelve_coverage_status_catalog .dpCertifiedEngine).1,
   (beyond_twelve_coverage_status_catalog .dpCertifiedEngine).2⟩

end OperatorKO7.BeyondTwelveMethodCoverage
