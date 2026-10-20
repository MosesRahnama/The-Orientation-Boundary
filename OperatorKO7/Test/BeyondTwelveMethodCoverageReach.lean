import OperatorKO7.Meta.BeyondTwelveMethodCoverage

namespace BeyondTwelveMethodCoverageReach

open OperatorKO7.BeyondTwelveMethodCoverage
open OperatorKO7.ResidualMethodLedger

#check BeyondTwelveFamily
#check beyondTwelveStatus
#check beyondTwelveFamilies
#check beyondTwelveFamilies_nodup
#check beyondTwelveFamilies_length
#check beyondTwelveFamilies_complete
#check BeyondTwelveCoverageConsistent
#check beyond_twelve_coverage_status_catalog
#check beyond_twelve_catalog_has_open
#check beyond_twelve_catalog_has_closed

-- R.2 headline: catalog covers all 12 beyond-12 families
example : beyondTwelveFamilies.length = 12 := beyondTwelveFamilies_length

-- Non-overclaim witness
example : ∃ f : BeyondTwelveFamily,
    f ∈ beyondTwelveFamilies ∧ beyondTwelveStatus f = .open_status :=
  beyond_twelve_catalog_has_open

-- Closed witness (DP certified engine closes via UniversalFirstOrderDichotomy)
example : ∃ f : BeyondTwelveFamily,
    f ∈ beyondTwelveFamilies ∧ beyondTwelveStatus f = .closed :=
  beyond_twelve_catalog_has_closed

-- Specific canonical statuses
example : beyondTwelveStatus .dpDirectPairExtraction = .open_status := by
  exact (beyond_twelve_coverage_status_catalog .dpDirectPairExtraction).2

example : beyondTwelveStatus .dpTransformedCallRoute = .adapter_only := by
  exact (beyond_twelve_coverage_status_catalog .dpTransformedCallRoute).2

example : beyondTwelveStatus .usableRulesConditional = .conditional := by
  exact (beyond_twelve_coverage_status_catalog .usableRulesConditional).2

example : beyondTwelveStatus .semanticCertifiedExternalEngine = .closed := by
  exact (beyond_twelve_coverage_status_catalog .semanticCertifiedExternalEngine).2

example : beyondTwelveStatus .sizeChangeOpen = .open_status := by
  exact (beyond_twelve_coverage_status_catalog .sizeChangeOpen).2

end BeyondTwelveMethodCoverageReach
