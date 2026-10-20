import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
Remark rem:dynamic-boundary identifies persistent observational separation with
separation of all independent reducts, and its corrected complement is
reachability of the full observational kernel, including coalescence on the
diagonal and collisions at the off-diagonal observer boundary.
-/

namespace DynamicBoundary

universe u v
variable {α : Type u} {β : Type v}

open Relation (ReflTransGen)

inductive PairStep (r : α → α → Prop) : (α × α) → (α × α) → Prop where
  | left {a a' b : α} : r a a' → PairStep r (a, b) (a', b)
  | right {a b b' : α} : r b b' → PairStep r (a, b) (a, b')

def Box (r : α → α → Prop) (P : α → Prop) (s : α) : Prop :=
  ∀ t, ReflTransGen r s t → P t

def Separated (q : α → β) (p : α × α) : Prop :=
  q p.1 ≠ q p.2

def Kernel (q : α → β) (p : α × α) : Prop :=
  q p.1 = q p.2

def Boundary (q : α → β) (p : α × α) : Prop :=
  Kernel q p ∧ p.1 ≠ p.2

def Reaches (r : α → α → Prop) (P : α → Prop) (s : α) : Prop :=
  ∃ t, ReflTransGen r s t ∧ P t

def Coalesces (r : α → α → Prop) (p : α × α) : Prop :=
  Relation.Join (ReflTransGen r) p.1 p.2

lemma pair_reductions_components {r : α → α → Prop} {p p' : α × α}
    (h : ReflTransGen (PairStep r) p p') :
    ReflTransGen r p.1 p'.1 ∧ ReflTransGen r p.2 p'.2 := by
  induction h with
  | refl => exact ⟨ReflTransGen.refl, ReflTransGen.refl⟩
  | tail _ h₂ ih =>
      cases h₂ with
      | left hleft => exact ⟨ih.1.tail hleft, ih.2⟩
      | right hright => exact ⟨ih.1, ih.2.tail hright⟩

lemma reduce_left {r : α → α → Prop} {a a' : α}
    (h : ReflTransGen r a a') (b : α) :
    ReflTransGen (PairStep r) (a, b) (a', b) :=
  ReflTransGen.lift (fun x => (x, b)) (fun _ _ hx => PairStep.left hx) h

lemma reduce_right {r : α → α → Prop} {b b' : α}
    (h : ReflTransGen r b b') (a : α) :
    ReflTransGen (PairStep r) (a, b) (a, b') :=
  ReflTransGen.lift (fun x => (a, x)) (fun _ _ hx => PairStep.right hx) h

lemma pair_reductions_iff {r : α → α → Prop} {p p' : α × α} :
    ReflTransGen (PairStep r) p p' ↔
      ReflTransGen r p.1 p'.1 ∧ ReflTransGen r p.2 p'.2 := by
  constructor
  · exact pair_reductions_components
  · rcases p with ⟨a, b⟩
    rcases p' with ⟨a', b'⟩
    intro h
    exact (reduce_left h.1 b).trans (reduce_right h.2 a')

lemma box_current {r : α → α → Prop} {P : α → Prop} {s : α}
    (h : Box r P s) : P s :=
  h s ReflTransGen.refl

lemma box_forward {r : α → α → Prop} {P : α → Prop} {s t : α}
    (hs : Box r P s) (hst : ReflTransGen r s t) : Box r P t := by
  intro z htz
  exact hs z (hst.trans htz)

lemma box_pair_iff (r : α → α → Prop) (P : α × α → Prop) (a b : α) :
    Box (PairStep r) P (a, b) ↔
      ∀ a' b', ReflTransGen r a a' → ReflTransGen r b b' → P (a', b') := by
  constructor
  · intro h a' b' ha hb
    exact h (a', b') (pair_reductions_iff.mpr ⟨ha, hb⟩)
  · rintro h ⟨a', b'⟩ hp
    have hc := pair_reductions_components hp
    exact h a' b' hc.1 hc.2

lemma persistent_separation_iff (r : α → α → Prop) (q : α → β) (a b : α) :
    Box (PairStep r) (Separated q) (a, b) ↔
      ∀ a' b', ReflTransGen r a a' → ReflTransGen r b b' → q a' ≠ q b' :=
  box_pair_iff r (Separated q) a b

lemma not_box_iff_reaches_kernel (r : α → α → Prop) (q : α → β)
    (p : α × α) :
    ¬ Box (PairStep r) (Separated q) p ↔
      Reaches (PairStep r) (Kernel q) p := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    intro t ht heq
    exact hn ⟨t, ht, heq⟩
  · rintro ⟨t, ht, heq⟩ hbox
    exact (hbox t ht) heq

lemma not_box_iff_independent_equal (r : α → α → Prop) (q : α → β)
    (a b : α) :
    ¬ Box (PairStep r) (Separated q) (a, b) ↔
      ∃ a' b', ReflTransGen r a a' ∧ ReflTransGen r b b' ∧ q a' = q b' := by
  rw [not_box_iff_reaches_kernel]
  constructor
  · rintro ⟨⟨a', b'⟩, hp, heq⟩
    have hc := pair_reductions_components hp
    exact ⟨a', b', hc.1, hc.2, heq⟩
  · rintro ⟨a', b', ha, hb, heq⟩
    exact ⟨(a', b'), pair_reductions_iff.mpr ⟨ha, hb⟩, heq⟩

lemma complement_persistent_separation (r : α → α → Prop) (q : α → β) :
    {p : α × α | ¬ Box (PairStep r) (Separated q) p} =
      {p : α × α | Reaches (PairStep r) (Kernel q) p} := by
  ext p
  exact not_box_iff_reaches_kernel r q p

lemma kernel_iff_diagonal_or_boundary (q : α → β) (p : α × α) :
    Kernel q p ↔ p.1 = p.2 ∨ Boundary q p := by
  classical
  constructor
  · intro h
    by_cases hp : p.1 = p.2
    · exact Or.inl hp
    · exact Or.inr ⟨h, hp⟩
  · rintro (h | h)
    · exact congrArg q h
    · exact h.1

lemma not_box_iff_coalesces_or_boundary (r : α → α → Prop) (q : α → β)
    (p : α × α) :
    ¬ Box (PairStep r) (Separated q) p ↔
      Coalesces r p ∨ Reaches (PairStep r) (Boundary q) p := by
  classical
  rw [not_box_iff_reaches_kernel]
  constructor
  · rintro ⟨⟨a', b'⟩, hp, hq⟩
    have hc := pair_reductions_components hp
    by_cases heq : a' = b'
    · subst b'
      exact Or.inl ⟨a', hc.1, hc.2⟩
    · exact Or.inr ⟨(a', b'), hp, hq, heq⟩
  · rintro (⟨c, ha, hb⟩ | ⟨t, ht, hboundary⟩)
    · exact ⟨(c, c), pair_reductions_iff.mpr ⟨ha, hb⟩, rfl⟩
    · exact ⟨t, ht, hboundary.1⟩

lemma not_box_iff_boundary_of_no_coalescence
    (r : α → α → Prop) (q : α → β) (p : α × α)
    (hnc : ¬ Coalesces r p) :
    ¬ Box (PairStep r) (Separated q) p ↔
      Reaches (PairStep r) (Boundary q) p := by
  constructor
  · intro h
    rcases (not_box_iff_coalesces_or_boundary r q p).mp h with hc | hb
    · exact (hnc hc).elim
    · exact hb
  · intro hb
    exact (not_box_iff_coalesces_or_boundary r q p).mpr (Or.inr hb)

def LosesSeparation (r : α → α → Prop) (q : α → β) (p : α × α) : Prop :=
  Separated q p ∧ Reaches (PairStep r) (Kernel q) p

lemma loses_separation_iff (r : α → α → Prop) (q : α → β) (p : α × α) :
    LosesSeparation r q p ↔
      Separated q p ∧ ¬ Box (PairStep r) (Separated q) p := by
  constructor
  · rintro ⟨hs, hr⟩
    exact ⟨hs, (not_box_iff_reaches_kernel r q p).mpr hr⟩
  · rintro ⟨hs, hn⟩
    exact ⟨hs, (not_box_iff_reaches_kernel r q p).mp hn⟩

lemma loss_has_different_target {r : α → α → Prop} {q : α → β} {p : α × α}
    (h : LosesSeparation r q p) :
    ∃ t, ReflTransGen (PairStep r) p t ∧ t ≠ p ∧ Kernel q t := by
  rcases h with ⟨hs, t, ht, hk⟩
  have hne : t ≠ p := by
    intro htp
    subst t
    exact hs hk
  exact ⟨t, ht, hne, hk⟩

lemma diagonal_outside_box (r : α → α → Prop) (q : α → β) (a : α) :
    ¬ Box (PairStep r) (Separated q) (a, a) := by
  intro h
  exact (box_current h) rfl

lemma identity_boundary_empty (p : α × α) :
    ¬ Boundary (id : α → α) p := by
  rintro ⟨heq, hne⟩
  exact hne heq

lemma identity_never_reaches_boundary (r : α → α → Prop) (p : α × α) :
    ¬ Reaches (PairStep r) (Boundary (id : α → α)) p := by
  rintro ⟨t, _, hb⟩
  exact identity_boundary_empty t hb

/-- The empty singleton system already refutes initial separation of every outside pair. -/
theorem empty_diagonal_counterexample :
    ¬ Box (PairStep (fun _ _ : Unit => False))
        (Separated (id : Unit → Unit)) ((), ()) ∧
      ¬ Separated (id : Unit → Unit) ((), ()) ∧
      ¬ Reaches (PairStep (fun _ _ : Unit => False))
        (Boundary (id : Unit → Unit)) ((), ()) := by
  have hs : ¬ Separated (id : Unit → Unit) ((), ()) := by
    intro h
    exact h rfl
  exact ⟨diagonal_outside_box _ _ (), hs, identity_never_reaches_boundary _ _⟩

def collapse (a b : Bool) : Prop :=
  a = true ∧ b = false

/-- An initially separated identity-observer pair coalesces without reaching a boundary. -/
theorem coalescence_counterexample :
    Separated (id : Bool → Bool) (true, false) ∧
      PairStep collapse (true, false) (false, false) ∧
      ¬ Box (PairStep collapse) (Separated (id : Bool → Bool)) (true, false) ∧
      ¬ Reaches (PairStep collapse) (Boundary (id : Bool → Bool)) (true, false) := by
  have hs : Separated (id : Bool → Bool) (true, false) := by
    intro h
    cases h
  have hp : PairStep collapse (true, false) (false, false) :=
    PairStep.left ⟨rfl, rfl⟩
  have hn : ¬ Box (PairStep collapse)
      (Separated (id : Bool → Bool)) (true, false) := by
    intro h
    exact (h (false, false) (ReflTransGen.single hp)) rfl
  exact ⟨hs, hp, hn, identity_never_reaches_boundary collapse (true, false)⟩

end DynamicBoundary

open DynamicBoundary in
theorem dynamic_boundary
    {α : Type*} {β : Type*} (r : α → α → Prop) (q : α → β) (a b : α) :
    (Box (PairStep r) (Separated q) (a, b) ↔
      ∀ a' b', Relation.ReflTransGen r a a' →
        Relation.ReflTransGen r b b' → q a' ≠ q b') ∧
    (¬ Box (PairStep r) (Separated q) (a, b) ↔
      ∃ a' b', Relation.ReflTransGen r a a' ∧
        Relation.ReflTransGen r b b' ∧ q a' = q b') ∧
    (¬ Box (PairStep r) (Separated q) (a, b) ↔
      Coalesces r (a, b) ∨ Reaches (PairStep r) (Boundary q) (a, b)) :=
  ⟨persistent_separation_iff r q a b,
    not_box_iff_independent_equal r q a b,
    not_box_iff_coalesces_or_boundary r q (a, b)⟩

end OperatorKO7.Meta.LiteratureReview
