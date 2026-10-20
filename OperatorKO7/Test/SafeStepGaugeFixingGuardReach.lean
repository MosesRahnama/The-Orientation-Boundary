import OperatorKO7.Meta.SafeStep.GaugeFixingGuard

namespace SafeStepGaugeFixingGuardReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard

#check @SafeStepGuard
#check @ExternalGaugeChoice
#check @safestep_guard_restores_local_confluence

example : SafeStepGuard void (integrate void) :=
  { disequality := by intro h; cases h }

example : ExternalGaugeChoice void (integrate void) :=
  { decide := Or.inl (by intro h; cases h) }

end SafeStepGaugeFixingGuardReach
