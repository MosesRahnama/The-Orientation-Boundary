import OperatorKO7.Meta.WPO_PolynomialBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# WPO-facing bounded polynomial-algebra barrier corollaries

This module specializes the generalized bounded polynomial barrier to
`WPOPolynomialDirectOrder`. Under the stated unboundedness and eventual base-dominance assumptions,
the duplicating step obstructs global orientation in this direct polynomial-algebra branch.

Generic recursive-path, maximum-branch, and completeness results require additional definitions and
theorems beyond this branch.
-/

namespace OperatorKO7.WPOPolynomialBarrier

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7-facing WPO polynomial-branch corollary under an unbounded direct algebra. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_unbounded
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  exact
    StepDuplicatingSchema.no_global_orients_wpoPolynomialDirect_of_unbounded
      (Sys := ko7System) W hunbounded hdom

/-- KO7 successor-pump specialization for the direct polynomial branch. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_succ_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (h_succ_bias : 1 ≤ W.measure.succ_bias) (h_succ_scale : 1 ≤ W.measure.succ_scale)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply
    StepDuplicatingSchema.no_wpoPolynomialDirect_orients_dup_step_of_succ_pump
      (W := W) h_succ_bias h_succ_scale hdom
  intro b s n
  exact h (ko7System.dup_step b s n)

/-- KO7 wrap-pump specialization for the direct polynomial branch. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_wrap_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (h_wrap_bias : 1 ≤ W.measure.wrap_const + W.measure.wrap_right * W.measure.c_base)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply
    StepDuplicatingSchema.no_wpoPolynomialDirect_orients_dup_step_of_wrap_pump
      (W := W) h_wrap_bias hdom
  intro b s n
  exact h (ko7System.dup_step b s n)

/-- Under unboundedness and global orientation, eventual base dominance fails. -/
theorem wpoPolynomialDirect_escape_requires_failure_of_base_dominance
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
    (horient : StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x)) :
    ¬ StepDuplicatingSchema.EventuallyDominatedAtBase W.measure := by
  apply
    StepDuplicatingSchema.wpoPolynomialDirect_escape_requires_failure_of_base_dominance
      (W := W) hunbounded
  intro b s n
  exact horient (ko7System.dup_step b s n)

end OperatorKO7.WPOPolynomialBarrier
