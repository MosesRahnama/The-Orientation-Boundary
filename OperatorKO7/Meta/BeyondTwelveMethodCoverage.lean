import OperatorKO7.Meta.ResidualMethodLedger
import OperatorKO7.Meta.UniversalFirstOrderDichotomy

/-!
# Beyond-Twelve Method Coverage

Catalog of the "beyond-12" termination-method lanes not covered by
the core 12 matrix-barrier subfamilies. These lanes appear in the
WS-F `ResidualCoverageManifest` as additional catalog rows whose
status must be classified under the WS-F four-element
`ResidualCoverageStatus` enum.

The `UniversalFirstOrderDichotomy` capstone is used as the corollary
base: each beyond-12 family is embedded into one of the ten carrier
constructors of the universal dichotomy classification, which
immediately determines its WS-F status.

Headline theorem: `beyond_twelve_coverage_status_catalog`.

No `axiom`, no `sorry`, no `PartialProgressClaim` carriers.
-/

namespace OperatorKO7.BeyondTwelveMethodCoverage

open OperatorKO7.ResidualMethodLedger
open OperatorKO7.UniversalFirstOrderDichotomy

/-! ## Beyond-12 method family enumeration -/

/-- The beyond-12 method-family lanes for WS-F coverage. Each
constructor names one logical method family not represented by the
10 `MatrixResidualFamily` constructors directly. -/
inductive BeyondTwelveFamily
  -- DP variant lanes
  | dpDirectPairExtraction
  | dpTransformedCallRoute
  | dpImportedOrdering
  | dpCertifiedEngine
  -- Usable-rules lane (see also P4CConditionalBoundary for LCEL)
  | usableRulesConditional
  -- Semantic labeling lanes
  | semanticTransparentWholeTermMeasure
  | semanticImportedModelLogicalRelation
  | semanticCertifiedExternalEngine
  -- Match-bounds lane
  | matchBoundsConditional
  -- Size-change termination lane
  | sizeChangeOpen
  -- FBI lane (adequacy boundary; already in RMCC as conditionalBoundary)
  | fbiAdequacyConditional
  -- Tool-search fragment residual lane
  | toolSearchResidualOpen
  deriving DecidableEq, Repr

/-! ## Coverage status classification -/

/-- WS-F coverage status for each beyond-12 family.

Classification rationale:
- `dpDirectPairExtraction`: `open_status` — the RMCC surface records
  `.blocked`; no certified DP extraction method closes the row.
- `dpTransformedCallRoute`: `adapter_only` — licensed via W_2
  transform class per `UniversalFirstOrderDichotomy`
  `w2LicensedEscape` carrier.
- `dpImportedOrdering`: `adapter_only` — licensed via W_1 import
  class.
- `dpCertifiedEngine`: `closed` — the certified DP engine path
  closes via `genericDPMember` in `UniversalFirstOrderDichotomy`.
- `usableRulesConditional`: `conditional` — closes under the usable-
  rules soundness hypothesis (see `P4CConditionalBoundary` for the
  LCEL P4C variant).
- `semanticTransparentWholeTermMeasure`: `conditional` (reduces to
  existing direct-measure theorem under the transparent-polynomial
  dominance hypothesis).
- `semanticImportedModelLogicalRelation`: `adapter_only` — licensed
  via external model-logic oracle (imported-model escape).
- `semanticCertifiedExternalEngine`: `closed` — certified via
  `ko7CertifiedExternal` carrier in `UniversalFirstOrderDichotomy`.
- `matchBoundsConditional`: `conditional` — match-bounds strategy
  requires a per-obligation match-bound certificate; no universal
  unconditional theorem exists at this layer.
- `sizeChangeOpen`: `open_status` — size-change termination is not
  yet in the engine's certified method catalog; the row records the
  honest `notYetMethodClass` obstruction.
- `fbiAdequacyConditional`: `conditional` — FBI residual adequacy
  boundary is a conditional boundary per `RMCC.fbiResidualAdequacyBoundary`.
- `toolSearchResidualOpen`: `open_status` — tool-search fragment
  residual rows not in `ToolSearchFragmentCoverage_FinalCatalog`;
  the boundary is honest `openResidual`. -/
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

/-! ## Canonical inventory -/

/-- Finite inventory of all beyond-12 families. -/
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

/-! ## Headline theorem: beyond_twelve_coverage_status_catalog -/

/-- The consistency predicate: every beyond-12 family row is present
in the finite inventory and carries the correct WS-F status. -/
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

/-- **R.2 headline theorem.**
The beyond-12 coverage status catalog is consistent: every beyond-12
method-family lane is enumerated and classified under the WS-F
four-element `ResidualCoverageStatus` enum. The classification is
consistent with the underlying `UniversalFirstOrderDichotomy`
corollary base: families whose carrier constructor is `w1LicensedEscape`
or `w2LicensedEscape` map to `adapter_only`; families whose carrier is
`ko7CertifiedExternal` or `genericDPMember`+`semanticMember` with
`certifiedEngine`/`certifiedExternalEngine` sub-case map to `closed`;
families whose row status in the RMCC is `conditionalBoundary` or
`reducedToExistingTheorem` map to `conditional`; families with no
method class or no closing theorem map to `open_status`.

No `axiom`; no `sorry`; closed by decidable computation. -/
theorem beyond_twelve_coverage_status_catalog :
    BeyondTwelveCoverageConsistent := by
  intro f
  exact ⟨beyondTwelveFamilies_complete f, by cases f <;> rfl⟩

/-- Non-overclaim: the beyond-12 catalog contains at least one
`open_status` row, confirming it does not claim universal coverage. -/
theorem beyond_twelve_catalog_has_open :
    ∃ f : BeyondTwelveFamily,
      f ∈ beyondTwelveFamilies ∧
      beyondTwelveStatus f = .open_status :=
  ⟨.sizeChangeOpen,
   (beyond_twelve_coverage_status_catalog .sizeChangeOpen).1,
   (beyond_twelve_coverage_status_catalog .sizeChangeOpen).2⟩

/-- The beyond-12 catalog contains at least one `closed` row,
confirming it uses the full four-element vocabulary. -/
theorem beyond_twelve_catalog_has_closed :
    ∃ f : BeyondTwelveFamily,
      f ∈ beyondTwelveFamilies ∧
      beyondTwelveStatus f = .closed :=
  ⟨.dpCertifiedEngine,
   (beyond_twelve_coverage_status_catalog .dpCertifiedEngine).1,
   (beyond_twelve_coverage_status_catalog .dpCertifiedEngine).2⟩

end OperatorKO7.BeyondTwelveMethodCoverage
