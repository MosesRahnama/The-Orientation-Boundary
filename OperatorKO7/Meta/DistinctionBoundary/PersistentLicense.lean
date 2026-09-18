/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.EqGuardedConfluence

/-!
# Greatest stable sublicense (Roadmap 09, F1)

For a relation `R` and a predicate `P`, the interior

`Box R P x := P x ∧ ∀ y, R∗ x y → P y`

is the unique greatest forward-invariant subpredicate of `P`. Containment,
star-closed forward invariance, greatestness, and idempotence are proved
generically. The comparator instance takes `R` to be componentwise
`EqGuardedStep` on `Trace` pairs and `P (a, b) := a ≠ b`. Persistence then
means the operands never coalesce under independent reduction.

Negative witness: `(merge void void, void)` satisfies disequality, but
`merge void void` reduces to `void`, so the pair becomes diagonal and `Box`
fails. Positive witness: `(delta void, void)` is stably distinct; both
components are `EqGuardedStep`-normal, so the only star-reduct is the pair
itself (persistence by normality).

This is the dynamic dual of `eqGuardedStep_unique_greatest_admissible`.
No freeze-set claim is made here.

Relation: generic `R`; comparator `PairStep` (componentwise `EqGuardedStep`).
Closure: `Relation.ReflTransGen`. Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence

namespace OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

/-! ## Generic interior -/

/-- The greatest stable sublicense of `P` along `R`: `P` holds at `x` and
at every `R∗`-reduct of `x`. -/
structure Box {α : Type} (R : α → α → Prop) (P : α → Prop) (x : α) : Prop where
  holds : P x
  persists : ∀ y, Relation.ReflTransGen R x y → P y

/-- Star-closed forward invariance: `Q` is preserved along `R∗`. -/
def ForwardInvariant {α : Type} (R : α → α → Prop) (Q : α → Prop) : Prop :=
  ∀ {x y : α}, Q x → Relation.ReflTransGen R x y → Q y

/-- `Box R P` is contained in `P`. -/
theorem box_subset {α : Type} {R : α → α → Prop} {P : α → Prop} {x : α}
    (h : Box R P x) : P x :=
  h.holds

/-- A star-reduct of a `Box` point is again a `Box` point. Stated against
`R∗` so the predicate is genuinely invariant, not merely one-step closed. -/
theorem box_forwardInvariant {α : Type} {R : α → α → Prop} {P : α → Prop}
    {x y : α} (hx : Box R P x) (hy : Relation.ReflTransGen R x y) :
    Box R P y :=
  ⟨hx.persists y hy, fun z hz =>
    hx.persists z (Relation.ReflTransGen.trans hy hz)⟩

/-- Every forward-invariant `Q ⊆ P` is contained in `Box R P`. -/
theorem box_greatest {α : Type} {R : α → α → Prop} {P Q : α → Prop}
    (hsub : ∀ x, Q x → P x) (hinv : ForwardInvariant R Q) {x : α}
    (hx : Q x) : Box R P x :=
  ⟨hsub x hx, fun y hy => hsub y (hinv hx hy)⟩

/-- `Box` is idempotent: the interior of the interior is the interior. -/
theorem box_idempotent {α : Type} (R : α → α → Prop) (P : α → Prop) :
    Box R (Box R P) = Box R P := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.holds
  · intro h
    exact ⟨h, fun y hy => box_forwardInvariant h hy⟩

/-- If `x` has no `R`-successor, the only `R∗`-reduct of `x` is `x`. -/
theorem reflTransGen_eq_of_normal {α : Type} {R : α → α → Prop} {x y : α}
    (hnorm : ∀ z, ¬ R x z) (h : Relation.ReflTransGen R x y) : x = y := by
  induction h with
  | refl => rfl
  | tail hstar hstep ih =>
      cases ih
      exact absurd hstep (hnorm _)

/-! ## Comparator dynamics: componentwise `EqGuardedStep` on pairs -/

/-- One component takes an `EqGuardedStep`; the other is held fixed. -/
inductive PairStep : Trace × Trace → Trace × Trace → Prop
  | left {a a' b : Trace} :
      EqGuardedStep a a' → PairStep (a, b) (a', b)
  | right {a b b' : Trace} :
      EqGuardedStep b b' → PairStep (a, b) (a, b')

/-- Comparator license: the two traces are distinct. -/
def Distinct : Trace × Trace → Prop :=
  fun p => p.1 ≠ p.2

private theorem pairStep_star_left {a a' b : Trace}
    (h : Relation.ReflTransGen EqGuardedStep a a') :
    Relation.ReflTransGen PairStep (a, b) (a', b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (PairStep.left hstep)

private theorem pairStep_star_right {a b b' : Trace}
    (h : Relation.ReflTransGen EqGuardedStep b b') :
    Relation.ReflTransGen PairStep (a, b) (a, b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (PairStep.right hstep)

/-- Independent reduction of each component is exactly `PairStep∗`. -/
theorem pairStep_star_components {p q : Trace × Trace}
    (h : Relation.ReflTransGen PairStep p q) :
    Relation.ReflTransGen EqGuardedStep p.1 q.1 ∧
      Relation.ReflTransGen EqGuardedStep p.2 q.2 := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      cases hstep with
      | left hL =>
          exact ⟨Relation.ReflTransGen.tail ih.1 hL, ih.2⟩
      | right hR =>
          exact ⟨ih.1, Relation.ReflTransGen.tail ih.2 hR⟩

theorem pairStep_star_iff {a b a' b' : Trace} :
    Relation.ReflTransGen PairStep (a, b) (a', b') ↔
      Relation.ReflTransGen EqGuardedStep a a' ∧
      Relation.ReflTransGen EqGuardedStep b b' := by
  constructor
  · intro h
    simpa using pairStep_star_components h
  · intro h
    exact Relation.ReflTransGen.trans
      (pairStep_star_left h.1) (pairStep_star_right h.2)

/-- `Box PairStep Distinct` is the license that never expires: no pair of
independent reducts coalesces. -/
theorem persistent_distinct_iff (a b : Trace) :
    Box PairStep Distinct (a, b) ↔
      ∀ a' b', Relation.ReflTransGen EqGuardedStep a a' →
        Relation.ReflTransGen EqGuardedStep b b' → a' ≠ b' := by
  constructor
  · intro h a' b' ha hb
    have hstar : Relation.ReflTransGen PairStep (a, b) (a', b') :=
      (pairStep_star_iff).mpr ⟨ha, hb⟩
    exact h.persists (a', b') hstar
  · intro h
    refine ⟨?holds, ?persists⟩
    · exact h a b Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    · intro p hp
      rcases p with ⟨a', b'⟩
      have hc := (pairStep_star_iff).mp hp
      exact h a' b' hc.1 hc.2

/-! ## Normality of the positive-witness components -/

/-- `void` is `EqGuardedStep`-normal: no root rule has source `void`. -/
theorem eqGuardedStep_not_void {t : Trace} : ¬ EqGuardedStep void t := by
  intro h
  cases h

/-- `delta void` is `EqGuardedStep`-normal: no root rule has source `delta _`. -/
theorem eqGuardedStep_not_delta_void {t : Trace} :
    ¬ EqGuardedStep (delta void) t := by
  intro h
  cases h

/-- If both components are normal, the only `PairStep∗`-reduct is the pair
itself. This is the persistence-by-normality argument. -/
theorem pairStep_star_of_normals {a b a' b' : Trace}
    (ha : ∀ t, ¬ EqGuardedStep a t) (hb : ∀ t, ¬ EqGuardedStep b t)
    (h : Relation.ReflTransGen PairStep (a, b) (a', b')) :
    a' = a ∧ b' = b := by
  have hc := (pairStep_star_iff).mp h
  exact ⟨(reflTransGen_eq_of_normal ha hc.1).symm,
    (reflTransGen_eq_of_normal hb hc.2).symm⟩

/-! ## R5 negative witness: coalescing pair -/

/-- `merge void void` reduces to `void` (cancel, or either void-merge). -/
theorem merge_void_void_steps_void :
    EqGuardedStep (merge void void) void :=
  EqGuardedStep.R_merge_cancel void

/-- Disequality holds at the coalescing pair: the constructors differ. -/
theorem coalescing_is_distinct : Distinct (merge void void, void) := by
  intro h
  cases h

/-- The coalescing pair is not persistent: one left step reaches the
diagonal `(void, void)`. -/
theorem coalescing_not_box :
    ¬ Box PairStep Distinct (merge void void, void) := by
  intro h
  have hstep : PairStep (merge void void, void) (void, void) :=
    PairStep.left merge_void_void_steps_void
  have : Distinct (void, void) :=
    h.persists (void, void) (Relation.ReflTransGen.single hstep)
  exact this rfl

/-- Non-triviality: `Box` sits strictly below `Distinct` at the coalescing
pair (`P` holds, `Box` fails). -/
theorem box_strictly_below_at_coalescing :
    Distinct (merge void void, void) ∧
      ¬ Box PairStep Distinct (merge void void, void) :=
  ⟨coalescing_is_distinct, coalescing_not_box⟩

/-! ## R5 positive witness: stably distinct pair -/

/-- The only `PairStep∗`-reduct of `(delta void, void)` is itself. -/
theorem stably_distinct_only_reduct {a b : Trace}
    (h : Relation.ReflTransGen PairStep (delta void, void) (a, b)) :
    a = delta void ∧ b = void :=
  pairStep_star_of_normals
    (fun _ ht => eqGuardedStep_not_delta_void ht)
    (fun _ ht => eqGuardedStep_not_void ht) h

/-- Disequality holds at `(delta void, void)`. -/
theorem stably_distinct_is_distinct : Distinct (delta void, void) := by
  intro h
  cases h

/-- Persistence by normality: both components are `EqGuardedStep`-normal,
so every reduct remains the same distinct pair. -/
theorem stably_distinct_box : Box PairStep Distinct (delta void, void) := by
  refine ⟨stably_distinct_is_distinct, ?_⟩
  intro p hp
  rcases p with ⟨a, b⟩
  rcases stably_distinct_only_reduct hp with ⟨ha, hb⟩
  cases ha
  cases hb
  exact stably_distinct_is_distinct

end OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
