import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

namespace SafeStepEqWVoidAnomalyReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

#check @CriticalPairAt
#check @eqW_void_void_admits_two_normal_forms
#check @eqW_void_void_normal_forms_are_unjoinable
#check @local_confluence_fails_at_eqW_void_void

example :
    CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  local_confluence_fails_at_eqW_void_void

end SafeStepEqWVoidAnomalyReach
