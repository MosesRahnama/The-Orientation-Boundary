import OperatorKO7.Meta.ContextClosed_SN_Full
import Mathlib.Logic.Relation

/-!
# Scope of the contextual diagonal fork

The root fork at `eqW a a` holds for every `a`: the reflexive verdict `void` and the
difference verdict `integrate (merge a a)` are distinct root normal forms
(`Meta/SafeStep/EqWVoidAnomaly.lean`). Under the *full context closure* `StepCtxFull`
the situation is no longer uniform in `a`, and this module fixes the scope.

The difference verdict contracts contextually as
`integrate (merge a a) → integrate a`, using `R_merge_cancel` under the `integrate`
context. The resulting term reduces to `void` exactly when `integrate a` is an
`R_int_delta` redex, that is when `a` is `delta`-headed. Hence:

* at `a = delta t` the contextual peak **joins** at `void`
  (`eqW_delta_diagonal_ctx_joinable`), so the fracture dissolves under context;
* at `a = void` the contextual peak stays **unjoined**
  (`eqW_void_void_ctx_not_joinable`), because `integrate void` is a normal form
  distinct from `void`.

The headline `contextual_fracture_scope` records both, which pins `eqW void void`
as a witness whose fracture survives contextual closure and shows that a general
"the fracture survives under context for every diagonal" reading is false.

Relation: `StepCtxFull` (full context closure of the unguarded kernel `Step`).
Closure: `Relation.ReflTransGen StepCtxFull`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

open OperatorKO7 Trace
open MetaSN_KO7

/-- Reflexive-transitive closure of the full contextual kernel relation. -/
abbrev CtxStar : Trace → Trace → Prop := Relation.ReflTransGen StepCtxFull

/-- `void` has no outgoing full-context step. -/
theorem void_normal {b : Trace} : ¬ StepCtxFull void b := by
  intro h
  cases h with
  | root hs => cases hs

/-- Any full-context reduct of `void` is `void`. -/
theorem ctxStar_void {d : Trace} (h : CtxStar void d) : d = void := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) void_normal

/-- The only full-context reduct of `merge void void` is `void`. -/
theorem merge_void_void_step {u : Trace} (h : StepCtxFull (merge void void) u) :
    u = void := by
  cases h with
  | root hs => cases hs with
    | R_merge_void_left _ => rfl
    | R_merge_void_right _ => rfl
    | R_merge_cancel _ => rfl
  | mergeL h' => exact absurd h' void_normal
  | mergeR h' => exact absurd h' void_normal

/-- The invariant satisfied by every full-context reduct of the diagonal difference
verdict at `void`. -/
def OnDiffCone (x : Trace) : Prop :=
  x = integrate (merge void void) ∨ x = integrate void

/-- `void` lies outside the cone. -/
theorem void_not_onDiffCone : ¬ OnDiffCone void := by
  rintro (h | h) <;> exact Trace.noConfusion h

/-- The cone is closed under full-context steps. -/
theorem onDiffCone_step {x y : Trace} (hx : OnDiffCone x) (h : StepCtxFull x y) :
    OnDiffCone y := by
  rcases hx with rfl | rfl
  · cases h with
    | root hs => cases hs
    | integrate h' =>
        have : _ = void := merge_void_void_step h'
        subst this
        exact Or.inr rfl
  · cases h with
    | root hs => cases hs
    | integrate h' => exact absurd h' void_normal

/-- Every full-context reduct of the diagonal difference verdict at `void` stays in
the cone. -/
theorem onDiffCone_ctxStar {x y : Trace} (hx : OnDiffCone x) (h : CtxStar x y) :
    OnDiffCone y := by
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact onDiffCone_step ih hstep

/-- HEADLINE (survival): under the full context closure the diagonal peak at
`eqW void void` stays unjoined. -/
theorem eqW_void_void_ctx_not_joinable :
    ¬ ∃ d, CtxStar void d ∧ CtxStar (integrate (merge void void)) d := by
  rintro ⟨d, hv, hi⟩
  have hdv : d = void := ctxStar_void hv
  subst hdv
  exact void_not_onDiffCone (onDiffCone_ctxStar (Or.inl rfl) hi)

/-- HEADLINE (dissolution): at a `delta`-headed diagonal the contextual peak joins at
`void`, so the contextual fracture is absent there. -/
theorem eqW_delta_diagonal_ctx_joinable (t : Trace) :
    ∃ d, CtxStar void d ∧ CtxStar (integrate (merge (delta t) (delta t))) d := by
  refine ⟨void, Relation.ReflTransGen.refl, ?_⟩
  have h1 : StepCtxFull (integrate (merge (delta t) (delta t))) (integrate (delta t)) :=
    StepCtxFull.integrate (StepCtxFull.root (Step.R_merge_cancel (delta t)))
  have h2 : StepCtxFull (integrate (delta t)) void :=
    StepCtxFull.root (Step.R_int_delta t)
  exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)

/-- HEADLINE: the contextual fracture is instance-dependent. It survives at the
minimal closed witness `eqW void void` and dissolves at every `delta`-headed
diagonal, so the root-level uniformity in `a` does not transfer to the context
closure. -/
theorem contextual_fracture_scope :
    (¬ ∃ d, CtxStar void d ∧ CtxStar (integrate (merge void void)) d)
    ∧ (∀ t : Trace,
        ∃ d, CtxStar void d ∧ CtxStar (integrate (merge (delta t) (delta t))) d) :=
  ⟨eqW_void_void_ctx_not_joinable, eqW_delta_diagonal_ctx_joinable⟩

#check @eqW_void_void_ctx_not_joinable
#check @eqW_delta_diagonal_ctx_joinable
#check @contextual_fracture_scope
#print axioms contextual_fracture_scope

end OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
