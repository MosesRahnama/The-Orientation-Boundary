import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalFork

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-- Root nonjoinability embeds as the root contextual obstruction certificate. -/
structure RootContextualObstruction : Prop where
  rootCriticalPair :
    CriticalPairAt (eqW void void) void (integrate (merge void void))
  rootNotJoinable :
    Not (exists d, StepStar void d ∧ StepStar (integrate (merge void void)) d)
  guardedContextConfluent :
    ConfluentSafeCtx

/-- The full-kernel root fork and the guarded contextual confluence theorem coexist in one certificate. -/
theorem eqW_void_void_contextual_obstruction_certificate :
    RootContextualObstruction :=
  { rootCriticalPair := local_confluence_fails_at_eqW_void_void
    rootNotJoinable := eqW_void_void_normal_forms_are_unjoinable
    guardedContextConfluent :=
      OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStepCtx_globally_confluent }

#print axioms eqW_void_void_contextual_obstruction_certificate

end OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalFork
