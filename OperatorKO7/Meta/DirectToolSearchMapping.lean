import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.QuadraticBarrier_Schema
import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema

/-!
# Direct Tool Search Mapping

This module packages the next reviewer-facing direct scalar search fragments that
are already theorem-backed in the schema barrier stack.

Covered fragments:

- additive direct fragments;
- affine direct fragments with explicit unbounded, successor-pump, or wrap-pump
  hypotheses;
- restricted quadratic direct fragments with explicit unbounded,
  successor-pump, or wrap-pump hypotheses;
- bounded multilinear direct fragments with explicit base-dominance and either
  unbounded, successor-pump, or wrap-pump hypotheses;
- generalized bounded-polynomial direct fragments with explicit eventual
  base-dominance and either unbounded, successor-pump, or wrap-pump
  hypotheses.

Still open:

- unrestricted nonlinear direct families without theorem-backed dominance or
  pump witnesses;
- cross-term quadratic, max-plus, and matrix-side continuations that belong to
  other mapping layers.
-/

namespace OperatorKO7.DirectToolSearchMapping

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Tool-facing direct additive fragment. -/
structure AdditiveFragment (Sys : StepDuplicatingSystem) where
  measure : AdditiveMeasure Sys.toStepDuplicatingSchema

/-- Tool-facing direct affine fragment with an explicit unbounded-range witness. -/
structure AffineUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : AffineMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRange measure

/-- Tool-facing direct affine fragment with an explicit successor-pump witness. -/
structure AffineSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : AffineMeasure Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ measure.succ_bias
  succ_scale_pos : 1 ≤ measure.succ_scale

/-- Tool-facing direct affine fragment with an explicit wrap-pump witness. -/
structure AffineWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : AffineMeasure Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ measure.wrap_const + measure.wrap_right * measure.c_base

/-- Tool-facing restricted quadratic fragment with an explicit unbounded-range witness. -/
structure QuadraticUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : QuadraticCounterMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangeQ measure

/-- Tool-facing restricted quadratic fragment with an explicit successor-pump witness. -/
structure QuadraticSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : QuadraticCounterMeasure Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ measure.succ_bias
  succ_scale_pos : 1 ≤ measure.succ_scale

/-- Tool-facing restricted quadratic fragment with an explicit wrap-pump witness. -/
structure QuadraticWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : QuadraticCounterMeasure Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ measure.wrap_const + measure.wrap_right * measure.c_base

/-- Tool-facing bounded multilinear fragment with explicit base-dominance and
unbounded-range witnesses. -/
structure MultilinearUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangeML measure
  dominance : MultilinearDominatedAtBase measure

/-- Tool-facing bounded multilinear fragment with explicit base-dominance and
successor-pump witnesses. -/
structure MultilinearSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ measure.succ_bias
  succ_scale_pos : 1 ≤ measure.succ_scale
  dominance : MultilinearDominatedAtBase measure

/-- Tool-facing bounded multilinear fragment with explicit base-dominance and
wrap-pump witnesses. -/
structure MultilinearWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ measure.wrap_const + measure.wrap_right * measure.c_base
  dominance : MultilinearDominatedAtBase measure

/-- Tool-facing generalized bounded-polynomial fragment with explicit eventual
base-dominance and unbounded-range witnesses. -/
structure PolynomialUnboundedFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedPolynomialMeasure Sys.toStepDuplicatingSchema
  unbounded : HasUnboundedRangePoly measure
  dominance : EventuallyDominatedAtBase measure

/-- Tool-facing generalized bounded-polynomial fragment with explicit eventual
base-dominance and successor-pump witnesses. -/
structure PolynomialSuccPumpFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedPolynomialMeasure Sys.toStepDuplicatingSchema
  succ_bias_pos : 1 ≤ measure.succ_bias
  succ_scale_pos : 1 ≤ measure.succ_scale
  dominance : EventuallyDominatedAtBase measure

/-- Tool-facing generalized bounded-polynomial fragment with explicit eventual
base-dominance and wrap-pump witnesses. -/
structure PolynomialWrapPumpFragment (Sys : StepDuplicatingSystem) where
  measure : BoundedPolynomialMeasure Sys.toStepDuplicatingSchema
  wrap_bias_pos : 1 ≤ measure.wrap_const + measure.wrap_right * measure.c_base
  dominance : EventuallyDominatedAtBase measure

/-- Direct additive fragments are blocked by the existing global additive barrier. -/
theorem additive_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : AdditiveFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_additive (Sys := Sys) F.measure

/-- Direct affine fragments with an explicit unbounded witness are blocked by the
existing global affine barrier. -/
theorem affineUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : AffineUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_affine_of_unbounded (Sys := Sys) F.measure F.unbounded

/-- Direct affine fragments with an explicit successor-pump witness are blocked by the
existing global affine successor-pump barrier. -/
theorem affineSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : AffineSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_affine_of_succ_pump
      (Sys := Sys) F.measure F.succ_bias_pos F.succ_scale_pos

/-- Direct affine fragments with an explicit wrap-pump witness are blocked by the
existing global affine wrap-pump barrier. -/
theorem affineWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : AffineWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_affine_of_wrap_pump (Sys := Sys) F.measure F.wrap_bias_pos

/-- Direct restricted quadratic fragments with an explicit unbounded witness are blocked by
the existing global restricted quadratic barrier. -/
theorem quadraticUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : QuadraticUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_quadratic_of_unbounded (Sys := Sys) F.measure F.unbounded

/-- Direct restricted quadratic fragments with an explicit successor-pump witness are blocked
by the existing global restricted quadratic successor-pump barrier. -/
theorem quadraticSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : QuadraticSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_quadratic_of_succ_pump
      (Sys := Sys) F.measure F.succ_bias_pos F.succ_scale_pos

/-- Direct restricted quadratic fragments with an explicit wrap-pump witness are blocked by
the existing global restricted quadratic wrap-pump barrier. -/
theorem quadraticWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : QuadraticWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_quadratic_of_wrap_pump (Sys := Sys) F.measure F.wrap_bias_pos

/-- Direct bounded multilinear fragments with explicit base-dominance and unbounded-range
witnesses are blocked by the existing global multilinear barrier. -/
theorem multilinearUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MultilinearUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_multilinear_of_unbounded
      (Sys := Sys) F.measure F.unbounded F.dominance

/-- Direct bounded multilinear fragments with explicit base-dominance and successor-pump
witnesses are blocked by the existing global multilinear successor-pump barrier. -/
theorem multilinearSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MultilinearSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_multilinear_of_succ_pump
      (Sys := Sys) F.measure F.succ_bias_pos F.succ_scale_pos F.dominance

/-- Direct bounded multilinear fragments with explicit base-dominance and wrap-pump
witnesses are blocked by the existing global multilinear wrap-pump barrier. -/
theorem multilinearWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : MultilinearWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact
    no_global_orients_multilinear_of_wrap_pump
      (Sys := Sys) F.measure F.wrap_bias_pos F.dominance

/-- Direct generalized bounded-polynomial fragments with explicit eventual base-dominance and
unbounded-range witnesses are blocked by the existing global polynomial barrier. -/
theorem polynomialUnbounded_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : PolynomialUnboundedFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  exact no_global_orients_polynomial_of_unbounded (Sys := Sys) F.measure F.unbounded F.dominance

/-- Direct generalized bounded-polynomial fragments with explicit eventual base-dominance and
successor-pump witnesses are blocked by the existing global polynomial successor-pump barrier. -/
theorem polynomialSuccPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : PolynomialSuccPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  intro h
  exact
    no_polynomial_orients_dup_step_of_succ_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.succ_bias_pos
      F.succ_scale_pos
      F.dominance
      (fun b s n => h (Sys.dup_step b s n))

/-- Direct generalized bounded-polynomial fragments with explicit eventual base-dominance and
wrap-pump witnesses are blocked by the existing global polynomial wrap-pump barrier. -/
theorem polynomialWrapPump_fragment_no_global_orientation
    {Sys : StepDuplicatingSystem} (F : PolynomialWrapPumpFragment Sys) :
    ¬ GlobalOrients Sys F.measure.eval (· < ·) := by
  intro h
  exact
    no_polynomial_orients_dup_step_of_wrap_pump
      (S := Sys.toStepDuplicatingSchema)
      F.measure
      F.wrap_bias_pos
      F.dominance
      (fun b s n => h (Sys.dup_step b s n))

end OperatorKO7.DirectToolSearchMapping
