import OperatorKO7.Meta.SafeStep.SmugglingUndecidability

namespace SafeStepSmugglingUndecidabilityReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.SafeStep.SmugglingUndecidability

#check @GaugeAnomalyAsSmuggling
#check @eqW_void_void_is_pre_undecidability_fracture
#check @safestep_guard_smuggles_external_observer

example {a b : Trace} (g : SafeStepGuard a b) : a ≠ b :=
  safestep_guard_smuggles_external_observer g

end SafeStepSmugglingUndecidabilityReach
