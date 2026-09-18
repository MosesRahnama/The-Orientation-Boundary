import OperatorKO7.Meta.SafeTrace_TripleLexExactness_FinalCatalog

namespace SafeTraceSurjectivityReach

open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.SafeTraceTripleLexExactnessFinalCatalog

#check concreteCarrierFaithfulnessObstruction
#check exists_trace_carrier_collision
#check final_catalog_projects_concreteCarrierFaithfulnessObstruction
#check final_catalog_projects_exists_trace_carrier_collision

example :
    ∃ t1 t2 : OperatorKO7.Trace,
      t1 ≠ t2 ∧ traceRealization.toCarrier t1 = traceRealization.toCarrier t2 :=
  exists_trace_carrier_collision

example : ¬ Function.Injective traceRealization.toCarrier :=
  concreteCarrierFaithfulnessObstruction.not_toCarrier_injective

example :
    ∃ t1 t2 : OperatorKO7.Trace,
      t1 ≠ t2 ∧ traceRealization.toCarrier t1 = traceRealization.toCarrier t2 :=
  final_catalog_projects_exists_trace_carrier_collision

end SafeTraceSurjectivityReach
