/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-!
# Dynamic diagonal grades

This module separates four semantic capabilities that cannot be represented by
numeric grade labels alone. D1s distinguishes a pair now. D1p requires that
distinction to persist under every independent future reduction. D2 additionally
requires an internal code whose denotation is the observer comparator.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions

variable {α β : Type}

/-- D0 carries no separation license. -/
def D0 (_q : α → β) (_x _y : α) : Prop := True

/-- D1s is static separation by the named observer. -/
def D1s (q : α → β) (x y : α) : Prop :=
  q x ≠ q y

/-- D1p is persistent separation: every pair of independently reachable
future states remains separated by the same observer. -/
def D1p (R : α → α → Prop) (q : α → β) (x y : α) : Prop :=
  ∀ x' y', Relation.ReflTransGen R x x' →
    Relation.ReflTransGen R y y' → q x' ≠ q y'

/-- D2 at a represented comparator class: persistent separation plus an
internally represented predicate extensionally equal to observer disequality. -/
def D2At (Represented : (α → α → Prop) → Prop)
    (R : α → α → Prop) (q : α → β) (x y : α) : Prop :=
  D1p R q x y ∧
    ∃ cmp : α → α → Prop,
      Represented cmp ∧ ∀ a b, cmp a b ↔ q a ≠ q b

/-- D2 always supplies the persistent D1p license. -/
theorem d2At_to_d1p {Represented : (α → α → Prop) → Prop}
    {R : α → α → Prop} {q : α → β} {x y : α}
    (h : D2At Represented R q x y) : D1p R q x y :=
  h.1

/-- Persistent separation implies current separation by reflexivity. -/
theorem d1p_to_d1s {R : α → α → Prop} {q : α → β} {x y : α}
    (h : D1p R q x y) : D1s q x y := by
  exact h x y Relation.ReflTransGen.refl Relation.ReflTransGen.refl

/-- The complete forward semantic ladder. -/
theorem d2At_to_d1s {Represented : (α → α → Prop) → Prop}
    {R : α → α → Prop} {q : α → β} {x y : α}
    (h : D2At Represented R q x y) : D1s q x y :=
  d1p_to_d1s (d2At_to_d1p h)

/-- Every static distinction forgets to D0. -/
theorem d1s_to_d0 {q : α → β} {x y : α} (_h : D1s q x y) : D0 q x y :=
  trivial

/-- Independent lifting of a relation to a pair. -/
inductive PairLift (R : α → α → Prop) : α × α → α × α → Prop
  | left {a a' b : α} : R a a' → PairLift R (a, b) (a', b)
  | right {a b b' : α} : R b b' → PairLift R (a, b) (a, b')

/-- Lift a left reduction sequence to the product. -/
theorem pairLift_star_left {R : α → α → Prop} {a a' b : α}
    (h : Relation.ReflTransGen R a a') :
    Relation.ReflTransGen (PairLift R) (a, b) (a', b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (PairLift.left hstep)

/-- Lift a right reduction sequence to the product. -/
theorem pairLift_star_right {R : α → α → Prop} {a b b' : α}
    (h : Relation.ReflTransGen R b b') :
    Relation.ReflTransGen (PairLift R) (a, b) (a, b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (PairLift.right hstep)

/-- Every lifted product reduction projects to the two component reductions. -/
theorem pairLift_star_components {R : α → α → Prop} {p q : α × α}
    (h : Relation.ReflTransGen (PairLift R) p q) :
    Relation.ReflTransGen R p.1 q.1 ∧
      Relation.ReflTransGen R p.2 q.2 := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      cases hstep with
      | left hL => exact ⟨Relation.ReflTransGen.tail ih.1 hL, ih.2⟩
      | right hR => exact ⟨ih.1, Relation.ReflTransGen.tail ih.2 hR⟩

/-- Independent future reduction is exactly the reflexive-transitive closure
of the lifted pair relation. -/
theorem pairLift_star_iff {R : α → α → Prop} {a b a' b' : α} :
    Relation.ReflTransGen (PairLift R) (a, b) (a', b') ↔
      Relation.ReflTransGen R a a' ∧ Relation.ReflTransGen R b b' := by
  constructor
  · intro h
    simpa using pairLift_star_components h
  · rintro ⟨ha, hb⟩
    exact Relation.ReflTransGen.trans
      (pairLift_star_left ha) (pairLift_star_right hb)

/-- Exact dynamic-license bridge: D1p is the persistent `Box` of observer
separation under independently lifted dynamics. -/
theorem box_pairLift_separation_iff {R : α → α → Prop}
    (q : α → β) (x y : α) :
    Box (PairLift R) (fun p : α × α => q p.1 ≠ q p.2) (x, y) ↔
      D1p R q x y := by
  constructor
  · intro h x' y' hx hy
    exact h.persists (x', y') ((pairLift_star_iff).2 ⟨hx, hy⟩)
  · intro h
    refine ⟨d1p_to_d1s h, ?_⟩
    intro p hp
    rcases p with ⟨x', y'⟩
    have hc := (pairLift_star_iff).1 hp
    exact h x' y' hc.1 hc.2

/-- The existing KO7 persistent-disequality license is exactly D1p for the
identity observer on the root equality-guarded relation. -/
theorem ko7_box_iff_d1p (a b : Trace) :
    Box PersistentLicense.PairStep PersistentLicense.Distinct (a, b) ↔
      D1p EqGuardedStep (id : Trace → Trace) a b := by
  simpa [D1p] using PersistentLicense.persistent_distinct_iff a b

/-- The live coalescing pair is statically distinguished. -/
theorem ko7_coalescing_d1s :
    D1s (id : Trace → Trace) (.merge .void .void) .void := by
  exact PersistentLicense.coalescing_is_distinct

/-- The same pair has no persistent distinction license. -/
theorem ko7_coalescing_not_d1p :
    ¬ D1p EqGuardedStep (id : Trace → Trace) (.merge .void .void) .void := by
  intro h
  exact PersistentLicense.coalescing_not_box ((ko7_box_iff_d1p _ _).2 h)

/-- Strictness of the dynamic ladder: D1s does not imply D1p. -/
theorem ko7_d1s_not_imply_d1p :
    D1s (id : Trace → Trace) (.merge .void .void) .void ∧
      ¬ D1p EqGuardedStep (id : Trace → Trace) (.merge .void .void) .void :=
  ⟨ko7_coalescing_d1s, ko7_coalescing_not_d1p⟩

/-- The live normal pair carries a positive persistent distinction license. -/
theorem ko7_stable_pair_d1p :
    D1p EqGuardedStep (id : Trace → Trace) (.delta .void) .void :=
  (ko7_box_iff_d1p _ _).1 PersistentLicense.stably_distinct_box

/-- Closed internal comparator language used for the concrete D2 witness. -/
inductive TraceComparatorCode where
  | disequality

/-- Denotation of the closed comparator language. -/
def denoteTraceComparator : TraceComparatorCode → Trace → Trace → Prop
  | .disequality, a, b => a ≠ b

/-- A predicate is represented when it is the denotation of an actual code. -/
def TraceComparatorRepresented (cmp : Trace → Trace → Prop) : Prop :=
  ∃ code : TraceComparatorCode, denoteTraceComparator code = cmp

/-- The stable KO7 pair reaches D2 for the explicit one-code internal
comparator language. -/
theorem ko7_stable_pair_d2 :
    D2At TraceComparatorRepresented EqGuardedStep (id : Trace → Trace)
      (.delta .void) .void := by
  refine ⟨ko7_stable_pair_d1p, ?_⟩
  refine ⟨fun a b => a ≠ b, ⟨.disequality, rfl⟩, ?_⟩
  intro a b
  rfl

/-- Every pair of reducts of the compiled instability endpoints remains
distinct, for an arbitrary positional selection. -/
theorem instability_endpoints_d1p (S : CtorPos → Prop) :
    D1p (CtxOnPos S EqGuardedStep) (id : Trace → Trace)
      FreezePositions.instabilityDifferenceVerdict .void := by
  intro x y hx hy hxy
  change x = y at hxy
  subst y
  exact FreezePositions.instabilityDifference_not_joinable_void S ⟨x, hx, hy⟩

/-- The canonical write-closed repair removes the concrete `eqW`-congruence
branch to `void`. This is a theorem about the live reduction relation. -/
theorem confluenceRepair_blocks_instability_void (S : CtorPos → Prop) :
    ¬ CtxStarPos (WriteClosure.confluenceRepair S) EqGuardedStep
      FreezePositions.instabilityWitness .void := by
  intro hVoid
  have hDifference :=
    FreezePositions.instabilityWitness_to_difference
      (WriteClosure.confluenceRepair S)
  obtain ⟨d, hD, hV⟩ :=
    WriteClosure.confluenceRepair_confluent S _ _ _ hDifference hVoid
  exact FreezePositions.instabilityDifference_not_joinable_void
    (WriteClosure.confluenceRepair S) ⟨d, hD, hV⟩

end OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
