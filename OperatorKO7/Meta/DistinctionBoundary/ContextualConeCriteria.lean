import OperatorKO7.Meta.DistinctionBoundary.ContextualClassification

/-!
# The two contextual cones as equivalences

`ContextualClassification` proves the necessity direction of the two cone lemmas behind the
contextual join-region characterization (`thm:ctxproven` of the Confluence paper):
`ctxStar_integrate_void_imp` and `ctxStar_merge_self_delta_imp`. This file adds the sufficiency
direction of each, so both cones are stated as equivalences.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.ContextualClassification

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

/-- The integrate cone: `integrate X` reaches `void` contextually if and only if `X` reaches a
`delta`-headed term. -/
theorem ctxStar_integrate_void_iff (X : Trace) :
    CtxStar (integrate X) void ↔ ∃ t, CtxStar X (delta t) := by
  constructor
  · exact ctxStar_integrate_void_imp
  · rintro ⟨t, ht⟩
    exact (ctxStar_integrate ht).tail (StepCtxFull.root (Step.R_int_delta t))

/-- The merge cone: `merge a a` reaches a `delta`-headed term contextually if and only if `a`
does. -/
theorem ctxStar_merge_self_delta_iff (a : Trace) :
    (∃ t, CtxStar (merge a a) (delta t)) ↔ ∃ t', CtxStar a (delta t') := by
  constructor
  · rintro ⟨t, ht⟩
    exact ctxStar_merge_self_delta_imp ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : CtxStar (merge a a) (merge (delta t) a) := ctxStar_mergeL ht
    have h2 : CtxStar (merge (delta t) a) (merge (delta t) (delta t)) := ctxStar_mergeR ht
    exact (h1.trans h2).tail (StepCtxFull.root (Step.R_merge_cancel (delta t)))

end OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
