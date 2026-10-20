import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

set_option autoImplicit false

/-!
# Contextual classification of the diagonal fracture

Manuscript anchor: the scope-of-the-contextual-fracture theorem of
`Rahnama_The_Distinction_Boundary`, whose general biconditional was prose.

## What this module proves

* **T-H, normalisation (the pinned quantifier).** `void` carries no full-context
  step, so joinability of the contextual diagonal peak is the same statement as
  reduction of the difference verdict to `void`:
  `JoinCtx void (integrate (merge a a)) ↔ CtxStar (integrate (merge a a)) void`.
  This replaces the informal reading of joinability with one quantifier over
  one reduction sequence.
* **Sufficiency, strengthened.** The dissolution family widens from the
  syntactically `delta`-headed diagonals to every `a` that contextually reaches
  a `delta`-headed term: `a →* delta t` suffices for the peak to join. The
  earlier statement is the special case `a = delta t`.
* **The congruence closures** the strengthening needs, as reusable lemmas.
* **T-H, the classifier (both directions).** The contextual diagonal peak at
  `eqW a a` joins if and only if `a` contextually reaches a `delta`-headed
  term. The converse is carried by two cone invariants: every full-context
  reduct of `integrate X` is an `integrate` of a reduct of `X` until the root
  rule fires, and every reduct of `merge a a` is either a `merge` of two
  reducts of `a` or itself a reduct of `a`, because each root merge rule
  returns a descendant of `a`. The carrier therefore splits into a
  contextual-join region and a contextual-nonjoin region, which is the
  boundary made literal.

Relation: `StepCtxFull` (full context closure of the unguarded kernel).
Closure: `Relation.ReflTransGen StepCtxFull`. Strategy: not applicable.
Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.ContextualClassification

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

/-- Joinability of two terms under the full context closure. -/
def JoinCtx (t u : Trace) : Prop := ∃ d, CtxStar t d ∧ CtxStar u d

/-! ## T-H, the normalisation step -/

/-- **T-H, normalisation.** Since `void` is contextually normal, the contextual
diagonal peak joins exactly when the difference verdict reduces to `void`. The
quantifier is pinned: one reduction sequence, one target. -/
theorem joinCtx_void_iff_ctxStar_void (a : Trace) :
    JoinCtx void (integrate (merge a a)) ↔ CtxStar (integrate (merge a a)) void := by
  constructor
  · rintro ⟨d, hd1, hd2⟩
    have hdv : d = void := ctxStar_void hd1
    subst hdv
    exact hd2
  · intro h
    exact ⟨void, Relation.ReflTransGen.refl, h⟩

/-! ## Congruence closures under the full context relation -/

/-- The `integrate` congruence lifts to the reflexive-transitive closure. -/
theorem ctxStar_integrate {s t : Trace} (h : CtxStar s t) :
    CtxStar (integrate s) (integrate t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.tail (StepCtxFull.integrate hlast)

/-- The left `merge` congruence lifts to the reflexive-transitive closure. -/
theorem ctxStar_mergeL {s t u : Trace} (h : CtxStar s t) :
    CtxStar (merge s u) (merge t u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.tail (StepCtxFull.mergeL hlast)

/-- The right `merge` congruence lifts to the reflexive-transitive closure. -/
theorem ctxStar_mergeR {s t u : Trace} (h : CtxStar s t) :
    CtxStar (merge u s) (merge u t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.tail (StepCtxFull.mergeR hlast)

/-! ## Sufficiency, strengthened -/

/-- **Strengthened dissolution.** If `a` contextually reaches a `delta`-headed
term then the contextual diagonal peak at `eqW a a` joins at `void`. The
previously proven family is the case `a = delta t`, where the reduction is
reflexive. -/
theorem diagonal_ctx_joins_of_reaches_delta {a t : Trace} (h : CtxStar a (delta t)) :
    JoinCtx void (integrate (merge a a)) := by
  rw [joinCtx_void_iff_ctxStar_void]
  have h1 : CtxStar (merge a a) (merge (delta t) a) := ctxStar_mergeL h
  have h2 : CtxStar (merge (delta t) a) (merge (delta t) (delta t)) := ctxStar_mergeR h
  have h3 : CtxStar (merge a a) (merge (delta t) (delta t)) := h1.trans h2
  have h4 : CtxStar (integrate (merge a a)) (integrate (merge (delta t) (delta t))) :=
    ctxStar_integrate h3
  have h5 : StepCtxFull (integrate (merge (delta t) (delta t))) (integrate (delta t)) :=
    StepCtxFull.integrate (StepCtxFull.root (Step.R_merge_cancel (delta t)))
  have h6 : StepCtxFull (integrate (delta t)) void :=
    StepCtxFull.root (Step.R_int_delta t)
  exact (h4.tail h5).tail h6

/-- The syntactic family of the manuscript, recovered as the reflexive case. -/
theorem diagonal_ctx_joins_at_delta (t : Trace) :
    JoinCtx void (integrate (merge (delta t) (delta t))) :=
  diagonal_ctx_joins_of_reaches_delta (Relation.ReflTransGen.refl)

/-- The survival family of the manuscript, restated against `JoinCtx`. -/
theorem diagonal_ctx_fails_at_void : ¬ JoinCtx void (integrate (merge void void)) := by
  intro h
  exact eqW_void_void_ctx_not_joinable h

/-! ## The proven scope, packaged -/

/-- **The proven contextual scope.** Joinability is reduction of the difference
verdict to `void`; every `a` reaching a `delta`-headed term dissolves the
fracture; and the `void` diagonal keeps it. The converse of the middle clause
is `diagonal_ctx_joins_iff_reaches_delta` below. -/
theorem contextual_scope_proven :
    (∀ a : Trace, JoinCtx void (integrate (merge a a)) ↔
        CtxStar (integrate (merge a a)) void) ∧
      (∀ a t : Trace, CtxStar a (delta t) → JoinCtx void (integrate (merge a a))) ∧
      ¬ JoinCtx void (integrate (merge void void)) :=
  ⟨joinCtx_void_iff_ctxStar_void,
    fun _ _ h => diagonal_ctx_joins_of_reaches_delta h,
    diagonal_ctx_fails_at_void⟩

/-- R5 non-vacuity: both sides of the scope are inhabited by concrete terms. -/
theorem contextual_scope_nonvacuous :
    JoinCtx void (integrate (merge (delta void) (delta void))) ∧
      ¬ JoinCtx void (integrate (merge void void)) :=
  ⟨diagonal_ctx_joins_at_delta void, diagonal_ctx_fails_at_void⟩

/-- Non-triviality: the strengthening is proper. The term `merge void (delta void)`
reaches `delta void` without being `delta`-headed, so it lies in the widened
family and outside the syntactic one. -/
theorem strengthening_is_proper :
    CtxStar (merge void (delta void)) (delta void) ∧
      JoinCtx void (integrate (merge (merge void (delta void)) (merge void (delta void)))) := by
  have hred : CtxStar (merge void (delta void)) (delta void) :=
    Relation.ReflTransGen.single (StepCtxFull.root (Step.R_merge_void_left (delta void)))
  exact ⟨hred, diagonal_ctx_joins_of_reaches_delta hred⟩


/-! ## T-H, the classifier: the descendant invariant

The converse direction is closed here. Two cone invariants carry it: every
full-context reduct of `integrate X` is an `integrate` of a reduct of `X`
until the root rule fires, and every reduct of `merge a a` is either a `merge`
of two reducts of `a` or itself a reduct of `a`. -/

/-- The reachable cone of `integrate X`. -/
def IntegrateCone (X Y : Trace) : Prop :=
  (∃ X', Y = integrate X' ∧ CtxStar X X') ∨ (Y = void ∧ ∃ t, CtxStar X (delta t))

theorem integrateCone_step {X Y Z : Trace} (h : IntegrateCone X Y)
    (hstep : StepCtxFull Y Z) : IntegrateCone X Z := by
  rcases h with ⟨X', rfl, hXX'⟩ | ⟨rfl, ht⟩
  · cases hstep with
    | root hs =>
        cases hs with
        | R_int_delta t => exact Or.inr ⟨rfl, ⟨t, hXX'⟩⟩
    | integrate h' => exact Or.inl ⟨_, rfl, hXX'.tail h'⟩
  · exact absurd hstep void_normal

theorem integrateCone_ctxStar {X Y : Trace} (h : CtxStar (integrate X) Y) :
    IntegrateCone X Y := by
  induction h with
  | refl => exact Or.inl ⟨X, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hlast ih => exact integrateCone_step ih hlast

/-- **Integrate cone.** A contextual reduction of `integrate X` to `void` forces
`X` to reach a `delta`-headed term, since the only root rule for `integrate`
consumes a `delta`-headed argument. -/
theorem ctxStar_integrate_void_imp {X : Trace} (h : CtxStar (integrate X) void) :
    ∃ t, CtxStar X (delta t) := by
  rcases integrateCone_ctxStar h with ⟨X', hEq, _⟩ | ⟨_, ht⟩
  · exact absurd hEq.symm (by intro hc; cases hc)
  · exact ht

/-- The reachable cone of `merge a a`. -/
def MergeCone (a Y : Trace) : Prop :=
  (∃ u v, Y = merge u v ∧ CtxStar a u ∧ CtxStar a v) ∨ CtxStar a Y

theorem mergeCone_step {a Y Z : Trace} (h : MergeCone a Y)
    (hstep : StepCtxFull Y Z) : MergeCone a Z := by
  rcases h with ⟨u, v, rfl, hu, hv⟩ | hY
  · cases hstep with
    | root hs =>
        cases hs with
        | R_merge_void_left _ => exact Or.inr hv
        | R_merge_void_right _ => exact Or.inr hu
        | R_merge_cancel _ => exact Or.inr hu
    | mergeL h' => exact Or.inl ⟨_, v, rfl, hu.tail h', hv⟩
    | mergeR h' => exact Or.inl ⟨u, _, rfl, hu, hv.tail h'⟩
  · exact Or.inr (hY.tail hstep)

theorem mergeCone_ctxStar {a Y : Trace} (h : CtxStar (merge a a) Y) :
    MergeCone a Y := by
  induction h with
  | refl => exact Or.inl ⟨a, a, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hlast ih => exact mergeCone_step ih hlast

/-- **Merge cone.** A contextual reduction of `merge a a` to a `delta`-headed
term forces `a` itself to reach a `delta`-headed term: leaving merge form uses a
root merge rule, and every such rule returns a descendant of `a`. -/
theorem ctxStar_merge_self_delta_imp {a t : Trace} (h : CtxStar (merge a a) (delta t)) :
    ∃ t', CtxStar a (delta t') := by
  rcases mergeCone_ctxStar h with ⟨u, v, hEq, _, _⟩ | hY
  · exact absurd hEq (by intro hc; cases hc)
  · exact ⟨t, hY⟩

/-- **T-H, the classifier.** The contextual diagonal peak at `eqW a a` joins if
and only if `a` contextually reaches a `delta`-headed term. Both directions are
proven, so the carrier splits into a contextual-join region and a
contextual-nonjoin region. -/
theorem diagonal_ctx_joins_iff_reaches_delta (a : Trace) :
    JoinCtx void (integrate (merge a a)) ↔ ∃ t, CtxStar a (delta t) := by
  constructor
  · intro hjoin
    have hred : CtxStar (integrate (merge a a)) void :=
      (joinCtx_void_iff_ctxStar_void a).mp hjoin
    obtain ⟨t, ht⟩ := ctxStar_integrate_void_imp hred
    exact ctxStar_merge_self_delta_imp ht
  · rintro ⟨t, ht⟩
    exact diagonal_ctx_joins_of_reaches_delta ht

/-- The classifier partitions the carrier: the `void` diagonal lands in the
nonjoin region, and every `delta`-headed diagonal lands in the join region. -/
theorem classifier_partitions :
    (¬ ∃ t, CtxStar void (delta t)) ∧ (∀ t, ∃ t', CtxStar (delta t) (delta t')) := by
  constructor
  · rintro ⟨t, ht⟩
    exact absurd (ctxStar_void ht).symm (by intro hc; cases hc)
  · intro t
    exact ⟨t, Relation.ReflTransGen.refl⟩

end OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
