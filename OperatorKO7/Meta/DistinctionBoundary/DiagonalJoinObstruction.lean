import OperatorKO7.Meta.EqW_Guard_Barrier

set_option autoImplicit false

/-!
# Independent diagonal join obstruction

This module isolates the non-circular local confluence fact used by the Tier-17
repair.  It contains no `SemanticsPreservingSafeSubrel` structure and no
definition-driven maximality premise.  Legacy modules may import this root, but
the new admissibility surface does not need to import those legacy results.
-/

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_DM
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary

/-- Local join at a fixed source, measured in the ambient full kernel closure. -/
def LocalJoinRel (R : Trace -> Trace -> Prop) (a : Trace) : Prop :=
  ∀ {b c}, R a b -> R a c -> ∃ d, StepStar b d ∧ StepStar c d

/-- `void` is a full-kernel normal form. -/
theorem normalForm_void : NormalForm void := by
  intro ex
  rcases ex with ⟨u, hu⟩
  cases hu

/-- The two diagonal `eqW` verdicts have no common full-kernel reduct. -/
theorem void_integrate_merge_self_not_joinable (a : Trace) :
    ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge a a)) d := by
  intro h
  rcases h with ⟨d, hv, hi⟩
  have hd_eq_void : d = void := (nf_no_stepstar_forward normalForm_void hv).symm
  have hd_eq_int : d = integrate (merge a a) :=
    (nf_no_stepstar_forward
      (OperatorKO7.Meta.EqW_Guard_Barrier.normalForm_integrate_merge_self a) hi).symm
  exact OperatorKO7.Meta.EqW_Guard_Barrier.void_ne_integrate_merge_self a
    (hd_eq_void.symm.trans hd_eq_int)

/-- If the reflexive diagonal branch is retained, local join forces the
diagonal difference branch away. -/
theorem confluence_forces_no_diagonal_diff
    {R : Trace -> Trace -> Prop} {a : Trace}
    (href : R (eqW a a) void)
    (hjoin : LocalJoinRel R (eqW a a)) :
    ¬ R (eqW a a) (integrate (merge a a)) := by
  intro hdiff
  rcases hjoin href hdiff with ⟨d, hv, hi⟩
  exact void_integrate_merge_self_not_joinable a ⟨d, hv, hi⟩

section AuditChecks

#check @LocalJoinRel
#check @normalForm_void
#check @void_integrate_merge_self_not_joinable
#check @confluence_forces_no_diagonal_diff

#print axioms normalForm_void
#print axioms void_integrate_merge_self_not_joinable
#print axioms confluence_forces_no_diagonal_diff

end AuditChecks

end OperatorKO7.Meta.DistinctionBoundary
