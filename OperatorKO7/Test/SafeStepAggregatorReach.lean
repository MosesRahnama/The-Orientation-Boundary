import OperatorKO7.Meta.SafeStep
import OperatorKO7.Meta.Recursor.DPConfessionLicense

namespace SafeStepAggregatorReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.SafeStep.SmugglingUndecidability
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

-- W16.1 anchors visible through aggregator
#check @CriticalPairAt
#print axioms CriticalPairAt
#check @local_confluence_fails_at_eqW_void_void
#print axioms local_confluence_fails_at_eqW_void_void

-- W16.2 anchors visible through aggregator
#check @SafeStepGuard
#print axioms SafeStepGuard
#check @ExternalGaugeChoice
#print axioms ExternalGaugeChoice
#check @safestep_guard_restores_local_confluence
#print axioms safestep_guard_restores_local_confluence

-- W16.3 anchors visible through aggregator
#check @GaugeAnomalyAsSmuggling
#print axioms GaugeAnomalyAsSmuggling
#check @safestep_guard_smuggles_external_observer
#print axioms safestep_guard_smuggles_external_observer

-- W16.7 anchors visible through the aggregator
#check @disequality_is_not_substitution_invariant
#print axioms disequality_is_not_substitution_invariant
#check @disequality_not_sigma_expressible
#print axioms disequality_not_sigma_expressible

-- `PartialProgressClaim` is NOT re-exported by `Meta/SafeStep.lean`; it is
-- pinned here through its own module so this gate states what it checks.
#check @OperatorKO7.Meta.Recursor.DPConfessionLicense.PartialProgressClaim
#print axioms OperatorKO7.Meta.Recursor.DPConfessionLicense.PartialProgressClaim

end SafeStepAggregatorReach
