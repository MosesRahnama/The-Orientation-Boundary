import OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry

set_option autoImplicit false

namespace OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateLoop

open OperatorKO7 Trace
open OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateAsymmetry

theorem one_way_normalization_well_founded : WellFounded OneWayNormRev :=
  oneWayNormRev_wf

theorem two_way_delta_integrate_loops (t : Trace) :
    TwoWayNorm (integrate (delta t)) void
      ∧ TwoWayNorm void (integrate (delta t)) :=
  twoWayNorm_has_cycle t

theorem two_way_delta_integrate_not_wellFounded :
    ¬ WellFounded (fun a b => TwoWayNorm b a) :=
  twoWayNorm_not_wellFounded_rev

#print axioms one_way_normalization_well_founded
#print axioms two_way_delta_integrate_loops
#print axioms two_way_delta_integrate_not_wellFounded

end OperatorKO7.Meta.NormalizationBoundary.DeltaIntegrateLoop
