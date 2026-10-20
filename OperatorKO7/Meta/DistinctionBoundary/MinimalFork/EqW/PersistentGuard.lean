import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.ContextualScope
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.GuardedRoot
import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.Rewriting.CriticalPairLemma

/-!
# Context-stable repair III: persistent disequality

A difference verdict is licensed only when the two operands are distinct now and
remain distinct under every independent future guarded-context reduction. This
is the exact dynamic strengthening that removes guard expiration while retaining
full descent into both comparison arguments.

Relation: `MiniEqWPersistentCtxStep`.
Closure: exact-length `Quantitative.Reach` for the public statements; a proved
bridge to `Relation.ReflTransGen` is used only to invoke the generic Newman lemma.
Strategy: full contextual licensed rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Persistent disequality for the minimal comparator: every independently
reachable guarded-context pair remains off the diagonal. -/
structure PersistentDisequality (a b : MiniEqWTerm) : Prop where
  current : a ≠ b
  forward : ∀ {a' b'},
    Reach MiniEqWGuardedCtxStep a a' →
    Reach MiniEqWGuardedCtxStep b b' →
    a' ≠ b'

/-- Persistent disequality is stronger than current disequality. -/
theorem persistentDisequality_current {a b : MiniEqWTerm}
    (h : PersistentDisequality a b) : a ≠ b := h.current

/-- Persistence advances with the left argument. -/
theorem persistentDisequality_left
    {a a' b : MiniEqWTerm} (h : PersistentDisequality a b)
    (haa' : Reach MiniEqWGuardedCtxStep a a') :
    PersistentDisequality a' b where
  current := h.forward haa' (reach_refl b)
  forward := fun ha' hb => h.forward (reach_trans haa' ha') hb

/-- Persistence advances with the right argument. -/
theorem persistentDisequality_right
    {a b b' : MiniEqWTerm} (h : PersistentDisequality a b)
    (hbb' : Reach MiniEqWGuardedCtxStep b b') :
    PersistentDisequality a b' where
  current := h.forward (reach_refl a) hbb'
  forward := fun ha hb' => h.forward ha (reach_trans hbb' hb')

/-- Persistence advances independently in both arguments. -/
theorem persistentDisequality_forward
    {a b a' b' : MiniEqWTerm} (h : PersistentDisequality a b)
    (haa' : Reach MiniEqWGuardedCtxStep a a')
    (hbb' : Reach MiniEqWGuardedCtxStep b b') :
    PersistentDisequality a' b' :=
  persistentDisequality_right (persistentDisequality_left h haa') hbb'

/-- A persistent license cannot expire: all independently reachable operand
states remain distinct. -/
theorem persistent_guard_no_expiration
    {a b a' b' : MiniEqWTerm} (h : PersistentDisequality a b)
    (haa' : Reach MiniEqWGuardedCtxStep a a')
    (hbb' : Reach MiniEqWGuardedCtxStep b b') :
    a' ≠ b' :=
  h.forward haa' hbb'

/-- Any pair that can coalesce is denied a persistent-disequality license. -/
theorem no_persistentDisequality_of_common_reduct
    {a b z : MiniEqWTerm}
    (haz : Reach MiniEqWGuardedCtxStep a z)
    (hbz : Reach MiniEqWGuardedCtxStep b z) :
    ¬ PersistentDisequality a b := by
  intro h
  exact h.forward haz hbz rfl

/-- In particular, the diagonal can never carry a persistent-difference license. -/
theorem no_persistentDisequality_diagonal (a : MiniEqWTerm) :
    ¬ PersistentDisequality a a :=
  no_persistentDisequality_of_common_reduct (reach_refl a) (reach_refl a)

/-- Positive inhabited license: the two verdict constants can never move and are distinct. -/
theorem same_different_persistent : PersistentDisequality .same .different where
  current := miniEqW_same_ne_different
  forward := by
    intro a' b' ha hb
    have haeq : a' = .same :=
      eq_of_normalForm_reach miniEqW_same_guardedCtx_normal ha
    have hbeq : b' = .different :=
      eq_of_normalForm_reach miniEqW_different_guardedCtx_normal hb
    rw [haeq, hbeq]
    exact miniEqW_same_ne_different

/-- The contextual counterexample's outer arguments fail the persistent license
because the left operand reaches the right operand. -/
theorem contextualCounterexample_not_persistent :
    ¬ PersistentDisequality (.eqW .same .different) .different := by
  have hleft : Reach MiniEqWGuardedCtxStep (.eqW .same .different) .different := by
    apply reach_step
    exact MiniEqWGuardedCtxStep.root
      (MiniEqWGuardedRootStep.diff .same .different miniEqW_same_ne_different)
  exact no_persistentDisequality_of_common_reduct hleft
    (reach_refl (R := MiniEqWGuardedCtxStep) MiniEqWTerm.different)

/-- Componentwise guarded-context dynamics on operand pairs. -/
inductive MiniPairStep : MiniEqWTerm × MiniEqWTerm → MiniEqWTerm × MiniEqWTerm → Prop where
  | left {a a' b : MiniEqWTerm} :
      MiniEqWGuardedCtxStep a a' → MiniPairStep (a,b) (a',b)
  | right {a b b' : MiniEqWTerm} :
      MiniEqWGuardedCtxStep b b' → MiniPairStep (a,b) (a,b')

/-- Pair predicate used by the live `Box` infrastructure. -/
def MiniDistinct (p : MiniEqWTerm × MiniEqWTerm) : Prop := p.1 ≠ p.2

private theorem reach_to_reflTransGen {α : Type} {R : α → α → Prop}
    {x y : α} (h : Reach R x y) : Relation.ReflTransGen R x y := by
  rcases h with ⟨n, hn⟩
  induction hn with
  | zero => exact Relation.ReflTransGen.refl
  | @succ n a b c hab hbc ih =>
      exact Relation.ReflTransGen.head hab ih

private theorem reflTransGen_to_reach {α : Type} {R : α → α → Prop}
    {x y : α} (h : Relation.ReflTransGen R x y) : Reach R x y := by
  induction h with
  | refl => exact reach_refl _
  | tail hab hbc ih =>
      exact reach_trans ih (reach_step hbc)

private theorem miniPair_reach_left {a a' b : MiniEqWTerm}
    (h : Reach MiniEqWGuardedCtxStep a a') :
    Reach MiniPairStep (a,b) (a',b) := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  induction hn with
  | zero => exact Steps.zero _
  | @succ n x y z hxy hyz ih =>
      exact Steps.succ (MiniPairStep.left hxy) ih

private theorem miniPair_reach_right {a b b' : MiniEqWTerm}
    (h : Reach MiniEqWGuardedCtxStep b b') :
    Reach MiniPairStep (a,b) (a,b') := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  induction hn with
  | zero => exact Steps.zero _
  | @succ n x y z hxy hyz ih =>
      exact Steps.succ (MiniPairStep.right hxy) ih

/-- Public bridge to the live greatest-stable-sublicense `Box`. -/
theorem persistentDisequality_iff_box (a b : MiniEqWTerm) :
    PersistentDisequality a b ↔ OperatorKO7.Meta.DistinctionBoundary.PersistentLicense.Box MiniPairStep MiniDistinct (a,b) := by
  constructor
  · intro h
    refine ⟨h.current, ?_⟩
    intro p hp
    have htransport :
        ∀ {q : MiniEqWTerm × MiniEqWTerm},
          Relation.ReflTransGen MiniPairStep (a,b) q →
          PersistentDisequality q.1 q.2 := by
      intro q hq
      induction hq with
      | refl => exact h
      | tail hxy hyz ih =>
          cases hyz with
          | left hleft =>
              exact persistentDisequality_left ih (reach_step hleft)
          | right hright =>
              exact persistentDisequality_right ih (reach_step hright)
    exact (htransport hp).current
  · intro hbox
    refine ⟨hbox.holds, ?_⟩
    intro a' b' haa' hbb'
    have hpairs : Reach MiniPairStep (a,b) (a',b') :=
      reach_trans (miniPair_reach_left haa') (miniPair_reach_right hbb')
    exact hbox.persists (a',b') (reach_to_reflTransGen hpairs)

/-- Full contextual relation with a persistent license on every difference root. -/
inductive MiniEqWPersistentCtxStep : MiniEqWTerm → MiniEqWTerm → Prop where
  | refl (a : MiniEqWTerm) : MiniEqWPersistentCtxStep (.eqW a a) .same
  | diff (a b : MiniEqWTerm) (h : PersistentDisequality a b) :
      MiniEqWPersistentCtxStep (.eqW a b) .different
  | left {a a' b : MiniEqWTerm} : MiniEqWPersistentCtxStep a a' →
      MiniEqWPersistentCtxStep (.eqW a b) (.eqW a' b)
  | right {a b b' : MiniEqWTerm} : MiniEqWPersistentCtxStep b b' →
      MiniEqWPersistentCtxStep (.eqW a b) (.eqW a b')

/-- Every persistent licensed step is an unrestricted guarded-context step. -/
theorem persistentCtx_sub_guardedCtx {s t : MiniEqWTerm}
    (h : MiniEqWPersistentCtxStep s t) : MiniEqWGuardedCtxStep s t := by
  induction h with
  | refl a => exact MiniEqWGuardedCtxStep.root (MiniEqWGuardedRootStep.refl a)
  | diff a b hp =>
      exact MiniEqWGuardedCtxStep.root
        (MiniEqWGuardedRootStep.diff a b hp.current)
  | left _ ih => exact MiniEqWGuardedCtxStep.left ih
  | right _ ih => exact MiniEqWGuardedCtxStep.right ih

/-- Every persistent licensed step strictly lowers query count. -/
theorem persistentCtx_count_decreases {s t : MiniEqWTerm}
    (h : MiniEqWPersistentCtxStep s t) : miniEqWCount t < miniEqWCount s :=
  miniEqW_guardedCtx_count_decreases (persistentCtx_sub_guardedCtx h)

/-- Full persistent licensed rewriting is strongly normalizing. -/
theorem persistentGuard_context_SN : WellFounded (flip MiniEqWPersistentCtxStep) :=
  wf_flip_of_nat_decrease miniEqWCount persistentCtx_count_decreases

/-- Lift a persistent exact-length path through the left argument. -/
theorem persistent_reach_left {a a' b : MiniEqWTerm}
    (h : Reach MiniEqWPersistentCtxStep a a') :
    Reach MiniEqWPersistentCtxStep (.eqW a b) (.eqW a' b) := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  induction hn with
  | zero => exact Steps.zero _
  | @succ n x y z hxy hyz ih =>
      exact Steps.succ (MiniEqWPersistentCtxStep.left hxy) ih

/-- Lift a persistent exact-length path through the right argument. -/
theorem persistent_reach_right {a b b' : MiniEqWTerm}
    (h : Reach MiniEqWPersistentCtxStep b b') :
    Reach MiniEqWPersistentCtxStep (.eqW a b) (.eqW a b') := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  induction hn with
  | zero => exact Steps.zero _
  | @succ n x y z hxy hyz ih =>
      exact Steps.succ (MiniEqWPersistentCtxStep.right hxy) ih

/-- Persistence survives a persistent step in the left operand. -/
theorem persistent_after_left_step {a a' b : MiniEqWTerm}
    (h : PersistentDisequality a b)
    (haa' : MiniEqWPersistentCtxStep a a') :
    PersistentDisequality a' b :=
  persistentDisequality_left h
    (reach_step (persistentCtx_sub_guardedCtx haa'))

/-- Persistence survives a persistent step in the right operand. -/
theorem persistent_after_right_step {a b b' : MiniEqWTerm}
    (h : PersistentDisequality a b)
    (hbb' : MiniEqWPersistentCtxStep b b') :
    PersistentDisequality a b' :=
  persistentDisequality_right h
    (reach_step (persistentCtx_sub_guardedCtx hbb'))

/-- A unilateral reduct of one copy of an originally identical operand cannot
receive a persistent-difference license against the unreduced copy, because the
other copy can replay the same reduct and coalesce. -/
theorem no_persistent_after_unilateral_copy_step
    {a a' : MiniEqWTerm} (h : MiniEqWPersistentCtxStep a a') :
    ¬ PersistentDisequality a' a := by
  apply no_persistentDisequality_of_common_reduct (reach_refl a')
  exact reach_step (persistentCtx_sub_guardedCtx h)

/-- Quantitative local confluence of the persistent licensed relation. The proof
is structural on the source term and covers root/root, root/context,
context/root, same-side context, and commuting opposite-side contexts. -/
theorem persistent_localJoin_all :
    ∀ s, ∀ {l r},
      MiniEqWPersistentCtxStep s l →
      MiniEqWPersistentCtxStep s r →
      Joinable MiniEqWPersistentCtxStep l r := by
  intro s
  induction s with
  | same =>
      intro l r hl
      cases hl
  | different =>
      intro l r hl
      cases hl
  | eqW a b iha ihb =>
      intro l r hl hr
      cases hl with
      | refl x =>
          cases hr with
          | refl _ => exact ⟨.same, reach_refl _, reach_refl _⟩
          | diff _ _ hp => exact False.elim (hp.current rfl)
          | left hright =>
              exact ⟨.same, reach_refl _,
                reach_trans
                  (reach_step (MiniEqWPersistentCtxStep.right hright))
                  (reach_step (MiniEqWPersistentCtxStep.refl _))⟩
          | right hright =>
              exact ⟨.same, reach_refl _,
                reach_trans
                  (reach_step (MiniEqWPersistentCtxStep.left hright))
                  (reach_step (MiniEqWPersistentCtxStep.refl _))⟩
      | diff x y hp =>
          cases hr with
          | refl _ => exact False.elim (hp.current rfl)
          | diff _ _ _ => exact ⟨.different, reach_refl _, reach_refl _⟩
          | left hright =>
              have hp' := persistent_after_left_step hp hright
              exact ⟨.different, reach_refl _,
                reach_step (MiniEqWPersistentCtxStep.diff _ _ hp')⟩
          | right hright =>
              have hp' := persistent_after_right_step hp hright
              exact ⟨.different, reach_refl _,
                reach_step (MiniEqWPersistentCtxStep.diff _ _ hp')⟩
      | left hleft =>
          cases hr with
          | refl _ =>
              exact ⟨.same,
                reach_trans
                  (reach_step (MiniEqWPersistentCtxStep.right hleft))
                  (reach_step (MiniEqWPersistentCtxStep.refl _)),
                reach_refl _⟩
          | diff _ _ hp =>
              have hp' := persistent_after_left_step hp hleft
              exact ⟨.different,
                reach_step (MiniEqWPersistentCtxStep.diff _ _ hp'),
                reach_refl _⟩
          | left hright =>
              rcases iha hleft hright with ⟨z, hlz, hrz⟩
              exact ⟨.eqW z b, persistent_reach_left hlz, persistent_reach_left hrz⟩
          | right hright =>
              exact ⟨.eqW _ _,
                reach_step (MiniEqWPersistentCtxStep.right hright),
                reach_step (MiniEqWPersistentCtxStep.left hleft)⟩
      | right hleft =>
          cases hr with
          | refl _ =>
              exact ⟨.same,
                reach_trans
                  (reach_step (MiniEqWPersistentCtxStep.left hleft))
                  (reach_step (MiniEqWPersistentCtxStep.refl _)),
                reach_refl _⟩
          | diff _ _ hp =>
              have hp' := persistent_after_right_step hp hleft
              exact ⟨.different,
                reach_step (MiniEqWPersistentCtxStep.diff _ _ hp'),
                reach_refl _⟩
          | left hright =>
              exact ⟨.eqW _ _,
                reach_step (MiniEqWPersistentCtxStep.left hright),
                reach_step (MiniEqWPersistentCtxStep.right hleft)⟩
          | right hright =>
              rcases ihb hleft hright with ⟨z, hlz, hrz⟩
              exact ⟨.eqW a z, persistent_reach_right hlz, persistent_reach_right hrz⟩

private theorem persistent_localJoin_rtg :
    OperatorKO7.Meta.Rewriting.AbsLocalConfluent MiniEqWPersistentCtxStep := by
  intro s l r hsl hsr
  rcases persistent_localJoin_all s hsl hsr with ⟨z, hlz, hrz⟩
  exact ⟨z, reach_to_reflTransGen hlz, reach_to_reflTransGen hrz⟩

/-- Full persistent licensed rewriting is confluent in Mathlib's reflexive-
transitive closure, by the generic Newman theorem. -/
theorem persistentGuard_context_confluent_rtg :
    OperatorKO7.Meta.Rewriting.AbsConfluent MiniEqWPersistentCtxStep :=
  OperatorKO7.Meta.Rewriting.confluent_of_wf_of_localConfluent MiniEqWPersistentCtxStep
    persistentGuard_context_SN persistent_localJoin_rtg

/-- Full persistent licensed rewriting is confluent in the project's exact
`Reach` closure as well. -/
theorem persistentGuard_context_confluent (source : MiniEqWTerm) :
    ConfluentAt MiniEqWPersistentCtxStep source := by
  intro x y hx hy
  have hx' := reach_to_reflTransGen hx
  have hy' := reach_to_reflTransGen hy
  rcases persistentGuard_context_confluent_rtg source x y hx' hy' with
    ⟨z, hxz, hyz⟩
  exact ⟨z, reflTransGen_to_reach hxz, reflTransGen_to_reach hyz⟩

/-- Roadmap-stable confluence name for the fully contextual persistent-license
repair. The relation and closure remain explicit in the theorem type. -/
theorem persistent_guard_context_confluent (source : MiniEqWTerm) :
    ConfluentAt MiniEqWPersistentCtxStep source :=
  persistentGuard_context_confluent source

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork


