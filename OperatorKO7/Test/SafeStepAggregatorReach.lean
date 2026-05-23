import OperatorKO7.Meta.SafeStep

namespace SafeStepAggregatorReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.SafeStep.SmugglingUndecidability
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

-- W16.1 anchors visible through aggregator
#check @CriticalPairAt
#check @local_confluence_fails_at_eqW_void_void

-- W16.2 anchors visible through aggregator
#check @SafeStepGuard
#check @ExternalGaugeChoice
#check @safestep_guard_restores_local_confluence
#check @safestep_is_meta_halt

-- W16.3 anchors visible through aggregator
#check @GaugeAnomalyAsSmuggling
#check @safestep_guard_smuggles_external_observer

-- W16.7 anchors visible through aggregator (partial)
#check @disequality_is_not_substitution_invariant
#check @disequality_not_sigma_expressible
#check @PartialProgressClaim

end SafeStepAggregatorReach
