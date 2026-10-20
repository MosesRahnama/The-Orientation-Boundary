import OperatorKO7.Kernel
import OperatorKO7.Meta.Confluence_Safe

/-!
# SafeStep Worked Example: the eqW void void Gauge Anomaly

## Formal Scope

The formal full-kernel relation treats void and integrate (merge void void) as distinct normal forms and proves them unjoinable. No subsequent reduction of the latter is asserted in this module.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-- The two-witness critical-pair record at a source `Trace` term.
Bundles the two outgoing root reductions and the propositional
witness that the two targets are unjoinable in the multi-step closure
of the full kernel. -/
structure CriticalPairAt (a b1 b2 : Trace) : Prop where
  step_left  : Step a b1
  step_right : Step a b2
  unjoinable : ¬ ∃ d, StepStar b1 d ∧ StepStar b2 d

/-- The eqW void void critical pair admits two distinct normal forms.
Verbatim from the kernel rules: `R_eq_refl void` and `R_eq_diff void void`. -/
theorem eqW_void_void_admits_two_normal_forms :
    Step (eqW void void) void
      ∧ Step (eqW void void) (integrate (merge void void)) :=
  ⟨Step.R_eq_refl void, Step.R_eq_diff void void⟩

/-- The two normal forms reachable from `eqW void void` are unjoinable:
no common reduct exists in the multi-step closure of the full kernel
relation. This is directly the existing
`MetaSN_KO7.not_localJoinStep_eqW_void_void` result repackaged in the
`CriticalPairAt` record. -/
theorem eqW_void_void_normal_forms_are_unjoinable :
    ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge void void)) d := by
  intro ⟨d, hbStar, hcStar⟩
  have hnf_void : NormalForm void := by
    intro ⟨_, hu⟩; cases hu
  have hnf_int_merge : NormalForm (integrate (merge void void)) := by
    intro ⟨_, hu⟩; cases hu
  have hd_eq_void : d = void :=
    (nf_no_stepstar_forward hnf_void hbStar).symm
  have hd_eq_int : d = integrate (merge void void) :=
    (nf_no_stepstar_forward hnf_int_merge hcStar).symm
  have hneq : (integrate (merge void void) : Trace) ≠ void := by
    intro h; cases h
  exact hneq (hd_eq_int.symm.trans hd_eq_void)

/-- Local confluence of the full kernel `Step` relation fails at
`eqW void void`. Direct corollary of the two-rules-overlap structure
of the `eqW` rule pair plus the unjoinability witness. -/
theorem local_confluence_fails_at_eqW_void_void :
    CriticalPairAt (eqW void void) void (integrate (merge void void)) :=
  { step_left  := Step.R_eq_refl void
    step_right := Step.R_eq_diff void void
    unjoinable := eqW_void_void_normal_forms_are_unjoinable }

end OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
