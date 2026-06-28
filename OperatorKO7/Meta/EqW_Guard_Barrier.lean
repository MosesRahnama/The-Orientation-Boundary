import OperatorKO7.Meta.Confluence_Safe

set_option autoImplicit false

/-!
Guard-necessity results for the `eqW` overlap in the full kernel relation.

The original affine-orientation target for this suggestion was too strong and in fact false.
What the artifact can prove cleanly is the confluence-theoretic obstruction directly: in the
unguarded kernel relation, the overlap at `eqW a a` is never locally joinable.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- `integrate (merge a a)` is a full-step normal form. -/
theorem normalForm_integrate_merge_self (a : Trace) :
    NormalForm (integrate (merge a a)) := by
  intro ex
  rcases ex with ⟨u, hu⟩
  cases hu

/-- The two unguarded `eqW` reducts are always distinct. -/
theorem void_ne_integrate_merge_self (a : Trace) :
    (void : Trace) ≠ integrate (merge a a) := by
  intro h
  cases h

/-- In the full unguarded kernel relation, the `eqW a a` overlap is never locally joinable. -/
theorem not_localJoinStep_eqW_refl (a : Trace) : ¬ LocalJoinStep (eqW a a) := by
  intro hjoin
  have hb : Step (eqW a a) void := Step.R_eq_refl a
  have hc : Step (eqW a a) (integrate (merge a a)) := Step.R_eq_diff a a
  rcases hjoin hb hc with ⟨d, hbStar, hcStar⟩
  have hnf_void : NormalForm void := by
    intro ex
    rcases ex with ⟨u, hu⟩
    cases hu
  have hnf_int : NormalForm (integrate (merge a a)) :=
    normalForm_integrate_merge_self a
  have hd_eq_void : d = void := (nf_no_stepstar_forward hnf_void hbStar).symm
  have hd_eq_int : d = integrate (merge a a) :=
    (nf_no_stepstar_forward hnf_int hcStar).symm
  exact void_ne_integrate_merge_self a (hd_eq_void.symm.trans hd_eq_int)

/-- The `eqW` guards in `SafeStep` are genuine local-confluence guards. -/
theorem eqW_guards_are_confluence_necessary :
    ∀ a : Trace, ¬ LocalJoinStep (eqW a a) :=
  not_localJoinStep_eqW_refl

end MetaSN_KO7

namespace OperatorKO7.Meta.EqW_Guard_Barrier

/-- Namespace-stable alias for the root normal-form fact used by the Distinction
Boundary claim ledger. -/
theorem normalForm_integrate_merge_self (a : Trace) :
    NormalForm (integrate (merge a a)) :=
  MetaSN_KO7.normalForm_integrate_merge_self a

/-- Namespace-stable alias for the target-separation fact used by the
Distinction Boundary claim ledger. -/
theorem void_ne_integrate_merge_self (a : Trace) :
    (void : Trace) ≠ integrate (merge a a) :=
  MetaSN_KO7.void_ne_integrate_merge_self a

/-- Namespace-stable alias for the unguarded `eqW a a` local-join obstruction. -/
theorem not_localJoinStep_eqW_refl (a : Trace) :
    ¬ MetaSN_KO7.LocalJoinStep (eqW a a) :=
  MetaSN_KO7.not_localJoinStep_eqW_refl a

/-- Namespace-stable alias for the guard-necessity theorem. -/
theorem eqW_guards_are_confluence_necessary :
    ∀ a : Trace, ¬ MetaSN_KO7.LocalJoinStep (eqW a a) :=
  MetaSN_KO7.eqW_guards_are_confluence_necessary

#print axioms not_localJoinStep_eqW_refl
#print axioms eqW_guards_are_confluence_necessary

end OperatorKO7.Meta.EqW_Guard_Barrier
