import OperatorKO7.Meta.DirectToolSearchMapping
import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.MaxBarrier_Schema
import OperatorKO7.Meta.WPO_PolynomialBarrier_Schema

/-!
# Extended Direct Tool Search Mapping

This module packages hypotheses for three direct scalar families and specializes imported barrier
theorems to those packages:

- bounded cross-term quadratic direct fragments with explicit unbounded,
  successor-pump, or wrap-pump witnesses;
- max-plus direct fragments with explicit unbounded, successor-pump, or
  wrap-pump witnesses;
- WPO-facing direct polynomial fragments with explicit unboundedness, successor-pump, wrap-pump, or
  base-dominance hypotheses.

The quantified universe is restricted to the represented structures and their stated fields;
unrestricted nonlinear families, matrix orders, and LCEL constructions require separate interfaces.
-/

namespace OperatorKO7.ExtendedDirectToolSearchMapping

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Tool-facing bounded cross-term quadratic fragment with an explicit unbounded witness. -/
structure CrossQuadraticUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangeX measure
  bounded : CrossTermBoundedAtBase measure

/-- Tool-facing bounded cross-term quadratic fragment with an explicit successor-pump witness. -/
structure CrossQuadraticSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ measure.succ_bias
  succ_scale_pos : 1 ≤ measure.succ_scale
  bounded : CrossTermBoundedAtBase measure

/-- Tool-facing bounded cross-term quadratic fragment with an explicit wrap-pump witness. -/
structure CrossQuadraticWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ measure.wrap_const + measure.wrap_right * measure.c_base
  bounded : CrossTermBoundedAtBase measure

/-- Tool-facing max-plus fragment with an explicit unbounded witness. -/
structure MaxUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : MaxMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangeMax measure

/-- Tool-facing max-plus fragment with an explicit successor-pump witness. -/
structure MaxSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : MaxMeasure Sys.toStepDuplicatingSchema
  succ_const_pos : 1 ≤ measure.succ_const

/-- Tool-facing max-plus fragment with an explicit wrap-pump witness. -/
structure MaxWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : MaxMeasure Sys.toStepDuplicatingSchema
  wrap_drift_pos : 1 ≤ measure.wrap_const + measure.wrap_left

/-- Tool-facing WPO-direct polynomial fragment with an explicit unbounded witness. -/
structure WPOPolynomialDirectUnboundedFragment (Sys : StepDuplicatingSystem) where
  order : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangePoly order.measure
  dominance : EventuallyDominatedAtBase order.measure

/-- Tool-facing WPO-direct polynomial fragment with an explicit successor-pump witness. -/
structure WPOPolynomialDirectSuccPumpFragment (Sys : StepDuplicatingSystem) where
  order : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ order.measure.succ_bias
  succ_scale_pos : 1 ≤ order.measure.succ_scale
  dominance : EventuallyDominatedAtBase order.measure

/-- Tool-facing WPO-direct polynomial fragment with an explicit wrap-pump witness. -/
structure WPOPolynomialDirectWrapPumpFragment (Sys : StepDuplicatingSystem) where
  order : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ order.measure.wrap_const + order.measure.wrap_right * order.measure.c_base
  dominance : EventuallyDominatedAtBase order.measure

/-- Tool-facing WPO-direct polynomial escape fragment: a successful orienter with an
explicit unbounded witness must violate the base-dominance condition. -/
structure WPOPolynomialDirectBaseDominanceFailureFragment (Sys : StepDuplicatingSystem) where
  order : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangePoly order.measure

/-- Apply the global cross-term quadratic barrier to the packaged hypotheses. -/
theorem crossQuadraticUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : CrossQuadraticUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_cross_quadratic_of_unbounded (Sys := Sys) F.measure F.unbounded F.bounded

/-- Apply the cross-term quadratic successor-pump barrier to the packaged hypotheses. -/
theorem crossQuadraticSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : CrossQuadraticSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_cross_quadratic_of_succ_pump
      (Sys := Sys) F.measure F.succ_bias_pos F.succ_scale_pos F.bounded

/-- Apply the cross-term quadratic wrap-pump barrier to the packaged hypotheses. -/
theorem crossQuadraticWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : CrossQuadraticWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_cross_quadratic_of_wrap_pump (Sys := Sys) F.measure F.wrap_bias_pos F.bounded

/-- Apply the global max barrier to the packaged unboundedness witness. -/
theorem maxUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MaxUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_max_of_unbounded (Sys := Sys) F.measure F.unbounded

/-- Lift the max successor-pump theorem through `Sys.dup_step`. -/
theorem maxSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MaxSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  intro h
  exact
    no_max_orients_dup_step_of_succ_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.succ_const_pos
      (fun b s n => h (Sys.dup_step b s n))

/-- Lift the max wrap-pump theorem through `Sys.dup_step`. -/
theorem maxWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MaxWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  intro h
  exact
    no_max_orients_dup_step_of_wrap_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.wrap_drift_pos
      (fun b s n => h (Sys.dup_step b s n))

/-- Apply the global WPO-direct polynomial barrier to the packaged hypotheses. -/
theorem wpoPolynomialDirectUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : WPOPolynomialDirectUnboundedFragment Sys) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x) := by
  exact
    no_global_orients_wpoPolynomialDirect_of_unbounded
      (Sys := Sys) F.order F.unbounded F.dominance

/-- Lift the WPO-direct polynomial successor-pump theorem through `Sys.dup_step`. -/
theorem wpoPolynomialDirectSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : WPOPolynomialDirectSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x) := by
  intro h
  exact
    no_wpoPolynomialDirect_orients_dup_step_of_succ_pump
      (W := F.order)
      F.succ_bias_pos
      F.succ_scale_pos
      F.dominance
      (fun b s n => h (Sys.dup_step b s n))

/-- Lift the WPO-direct polynomial wrap-pump theorem through `Sys.dup_step`. -/
theorem wpoPolynomialDirectWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : WPOPolynomialDirectWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x) := by
  intro h
  exact
    no_wpoPolynomialDirect_orients_dup_step_of_wrap_pump
      (W := F.order)
      F.wrap_bias_pos
      F.dominance
      (fun b s n => h (Sys.dup_step b s n))

/-- Any successful WPO-direct polynomial escape with an explicit unbounded witness must violate
the base-dominance condition. -/
theorem wpoPolynomialDirectBaseDominanceFailure_fragment_escape_requires_failure_of_base_dominance
    {Sys : StepDuplicatingSystem} (F : WPOPolynomialDirectBaseDominanceFailureFragment Sys)
    (horient : GlobalOrients Sys (fun t => t) (fun x y => F.order.gt y x)) :
    ¬ EventuallyDominatedAtBase F.order.measure := by
  exact
    wpoPolynomialDirect_escape_requires_failure_of_base_dominance
      (W := F.order)
      F.unbounded
      (fun b s n => horient (Sys.dup_step b s n))

end OperatorKO7.ExtendedDirectToolSearchMapping
