import OperatorKO7.Meta.SafeStep
import OperatorKO7.Meta.Recursor.DPConfessionLicense

namespace SafeStepAggregatorReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.SafeStep.SmugglingUndecidability
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

-- Anchors visible through aggregator
#check @CriticalPairAt
#print axioms CriticalPairAt
#check @local_confluence_fails_at_eqW_void_void
#print axioms local_confluence_fails_at_eqW_void_void

-- Anchors visible through aggregator
#check @SafeStepGuard
#print axioms SafeStepGuard
#check @ExternalGaugeChoice
#print axioms ExternalGaugeChoice
#check @safestep_guard_restores_local_confluence
#print axioms safestep_guard_restores_local_confluence

-- Anchors visible through aggregator
#check @GaugeAnomalyAsSmuggling
#print axioms GaugeAnomalyAsSmuggling
#check @safestep_guard_smuggles_external_observer
#print axioms safestep_guard_smuggles_external_observer

-- Anchors visible through the aggregator
#check @disequality_is_not_substitution_invariant
#print axioms disequality_is_not_substitution_invariant
#check @disequality_not_sigma_expressible
#print axioms disequality_not_sigma_expressible

-- `PartialProgressClaim` is NOT re-exported by `Meta/SafeStep.lean`; it is
-- Declared in its own module and referenced here.
#check @OperatorKO7.Meta.Recursor.DPConfessionLicense.PartialProgressClaim
#print axioms OperatorKO7.Meta.Recursor.DPConfessionLicense.PartialProgressClaim

end SafeStepAggregatorReach
