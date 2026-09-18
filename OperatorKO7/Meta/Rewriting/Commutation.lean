import OperatorKO7.Meta.Rewriting.Rewrite
import Mathlib.Logic.Relation

/-!
# The abstract confluence toolkit: confluence, Church-Rosser, the diamond property, and commutation

Roadmap source: the confluence-toolkit expansion. This module is an abstract layer
over an arbitrary relation `r : α → α → Prop`. It packages the classical
abstract-rewriting vocabulary, proves the equivalence of confluence with the
Church-Rosser property, proves the strip lemma that the diamond property lifts to
confluence of the reflexive-transitive closure, proves the Hindley-Rosen theorem
that commuting confluent relations have a confluent union, and specializes the
diamond lemma to the library rewrite relation `StepStar`.

## Relationship to Mathlib

Mathlib's `Mathlib/Logic/Relation.lean` supplies the join of a relation
(`Relation.Join`), the reflexive-transitive closure `Relation.ReflTransGen` with a
full lemma API (`single`, `head`, `tail`, `trans`, `lift`, `mono`, `cases_head`,
`reflTransGen_idem`), the reflexive closure `Relation.ReflGen`, the equivalence
closure `Relation.EqvGen`, and the strip-style sufficient condition for joinability
`Relation.church_rosser`. These are reused directly. Mathlib does not provide named
predicates for confluence, the Church-Rosser property, the diamond property, or
commutation of an abstract relation; those are introduced here and connected to the
reused machinery.

The earlier module `Meta/Rewriting/CriticalPairLemma.lean` introduced
`AbsConfluent` / `AbsLocalConfluent` as bare quantified statements for its Newman
engine; the `Confluent` predicate here is the textbook packaging of the same peak,
phrased through `Relation.Join` so the Mathlib `Join` lemmas apply.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is inherited through `Term`/`Subst` plumbing used by the `StepStar`
specialization.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open Relation

universe u v

section Abstract

variable {α : Type u} (r s : α → α → Prop)

/-! ## Priority 1: the abstract vocabulary -/

/-- The diamond property: every one-step peak `b ← a → c` is completed by a
one-step valley `b → d ← c`. -/
def Diamond : Prop :=
  ∀ ⦃a b c⦄, r a b → r a c → ∃ d, r b d ∧ r c d

/-- Confluence of `r`: every peak of the reflexive-transitive closure joins. Phrased
through `Relation.Join`, so `b` and `c` reachable from a common `a` are both
reducts of a common `d`. -/
def Confluent : Prop :=
  ∀ ⦃a b c⦄, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c

/-- The Church-Rosser property of `r`: any two convertible terms (related by the
equivalence closure) are joinable through the reflexive-transitive closure. -/
def ChurchRosser : Prop :=
  ∀ ⦃a b⦄, EqvGen r a b → Join (ReflTransGen r) a b

/-- Commutation of `r` over `s`: an `s`-step followed against an `r`-step can be
completed, `r`-first then `s`-second. The shape is the one consumed by the
Hindley-Rosen theorem when instantiated at the two reflexive-transitive closures. -/
def Commute : Prop :=
  ∀ ⦃a b c⦄, s a b → r a c → ∃ d, r b d ∧ s c d

end Abstract

/-! ## Priority 1, continued: non-vacuity

Each predicate is inhabited by a concrete relation, so none is vacuously definable.
Equality on any type has the diamond property, is confluent, is Church-Rosser, and
commutes with itself; the common reduct or completion is the point itself. -/

section NonVacuity

variable {α : Type u}

/-- Equality has the diamond property: the two targets of a peak are already equal. -/
theorem diamond_eq : Diamond (α := α) (· = ·) := by
  rintro a b c rfl rfl
  exact ⟨a, rfl, rfl⟩

/-- Equality is confluent: a peak of the closure of `=` has both legs landing on
the source, so the source itself is the common reduct. -/
theorem confluent_eq : Confluent (α := α) (· = ·) := by
  have hself : ReflTransGen (α := α) (· = ·) = (· = ·) :=
    reflTransGen_eq_self (fun _ => rfl) (fun _ _ _ => Eq.trans)
  rintro a b c hab hac
  rw [hself] at hab hac
  subst hab; subst hac
  exact ⟨a, ReflTransGen.refl, ReflTransGen.refl⟩

/-- Equality commutes with itself. -/
theorem commute_eq : Commute (α := α) (· = ·) (· = ·) := by
  rintro a b c rfl rfl
  exact ⟨a, rfl, rfl⟩

end NonVacuity

section Theory

variable {α : Type u} {r s : α → α → Prop}

/-! ## Priority 2: Church-Rosser is equivalent to confluence

A relation has the Church-Rosser property exactly when it is confluent. The two
directions are the standard arguments: a peak is a special convertibility, and
confluence makes joinability a transitive (hence equivalence-closing) relation. -/

/-- A peak of the reflexive-transitive closure is a convertibility: if `a ↠ b` and
`a ↠ c` then `b` and `c` are related by the equivalence closure. The two reduction
sequences are embedded into `EqvGen` and glued at `a`. -/
theorem eqvGen_of_peak {a b c : α} (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) :
    EqvGen r b c := by
  have hgen : ∀ {x y : α}, ReflTransGen r x y → EqvGen r x y := by
    intro x y h
    induction h with
    | refl => exact EqvGen.refl _
    | tail _ hstep ih => exact ih.trans _ _ _ (EqvGen.rel _ _ hstep)
  exact (hgen hab).symm _ _ |>.trans _ _ _ (hgen hac)

/-- Joinability through the reflexive-transitive closure is symmetric. -/
theorem join_symm {b c : α} (h : Join (ReflTransGen r) b c) : Join (ReflTransGen r) c b :=
  symmetric_join h

/-- Under confluence, joinability through the reflexive-transitive closure is
transitive: a common reduct of `a, b` and a common reduct of `b, c` are bridged by
confluence at `b`. -/
theorem join_trans_of_confluent (hcr : Confluent r) {a b c : α}
    (hab : Join (ReflTransGen r) a b) (hbc : Join (ReflTransGen r) b c) :
    Join (ReflTransGen r) a c := by
  obtain ⟨x, hax, hbx⟩ := hab
  obtain ⟨y, hby, hcy⟩ := hbc
  obtain ⟨z, hxz, hyz⟩ := hcr hbx hby
  exact ⟨z, hax.trans hxz, hcy.trans hyz⟩

/-- Forward direction: the Church-Rosser property implies confluence. A peak is a
convertibility by `eqvGen_of_peak`, and Church-Rosser joins every convertibility. -/
theorem confluent_of_churchRosser (h : ChurchRosser r) : Confluent r := by
  intro a b c hab hac
  exact h (eqvGen_of_peak hab hac)

/-- Backward direction: confluence implies the Church-Rosser property. Induction on
the equivalence closure: a single step joins through one reduction, reflexivity is
the trivial join, symmetry uses `join_symm`, and transitivity uses
`join_trans_of_confluent`. -/
theorem churchRosser_of_confluent (hcr : Confluent r) : ChurchRosser r := by
  intro a b h
  induction h with
  | rel x y hxy => exact ⟨y, ReflTransGen.single hxy, ReflTransGen.refl⟩
  | refl x => exact ⟨x, ReflTransGen.refl, ReflTransGen.refl⟩
  | symm x y _ ih => exact join_symm ih
  | trans x y z _ _ ihxy ihyz => exact join_trans_of_confluent hcr ihxy ihyz

/-- The Church-Rosser property and confluence are equivalent. -/
theorem churchRosser_iff_confluent : ChurchRosser r ↔ Confluent r :=
  ⟨confluent_of_churchRosser, churchRosser_of_confluent⟩

/-! ## Priority 3: the diamond property lifts to confluence of the closure

If `r` has the diamond property then `ReflTransGen r` is confluent. The diamond
gives the strip condition `Relation.church_rosser` consumes (a one-step peak closes
into a one-step `ReflGen` valley on one side), so every peak of the closure joins.
The headline is stated for `ReflTransGen r`; since
`ReflTransGen (ReflTransGen r) = ReflTransGen r`, this is confluence of the closure
relation. -/

/-- The diamond property of `r` gives confluence of `r` itself: every peak of
`ReflTransGen r` joins. The diamond supplies the `ReflGen` strip that
`Relation.church_rosser` requires. -/
theorem diamond_imp_confluent_base (hd : Diamond r) : Confluent r := by
  intro a b c hab hac
  refine church_rosser ?_ hab hac
  intro x y z hxy hxz
  obtain ⟨w, hyw, hzw⟩ := hd hxy hxz
  exact ⟨w, ReflGen.single hyw, ReflTransGen.single hzw⟩

/-- The strip/diamond lemma: the diamond property lifts to confluence of the
reflexive-transitive closure. -/
theorem diamond_imp_confluent (hd : Diamond r) : Confluent (ReflTransGen r) := by
  intro a b c hab hac
  rw [reflTransGen_idem] at hab hac
  obtain ⟨d, hbd, hcd⟩ := diamond_imp_confluent_base hd hab hac
  exact ⟨d, by rw [reflTransGen_idem]; exact hbd, by rw [reflTransGen_idem]; exact hcd⟩

end Theory

/-! ## Priority 4: the Hindley-Rosen theorem

Two commuting confluent relations have a confluent union. Confluence of each
closure means each is a diamond on itself; commutation links the two. The bridge is
the composite relation `commStep`, one full `r`-reduction followed by one full
`s`-reduction. It sits between the union and the union closure, and the three
hypotheses paste together to give it the diamond property. Lifting that diamond
(Priority 3) and transporting along `ReflTransGen commStep = ReflTransGen union`
yields confluence of the union closure. -/

section HindleyRosen

variable {α : Type u} {r s : α → α → Prop}

/-- The union relation `r ∪ s`, written so the headline reads `fun a b => r a b ∨ s a b`. -/
private def unionRel (r s : α → α → Prop) : α → α → Prop := fun a b => r a b ∨ s a b

/-- The composite bridge relation: one full `r`-reduction followed by one full
`s`-reduction. This is reflexive and tiles the union closure. -/
private def commStep (r s : α → α → Prop) : α → α → Prop :=
  fun a b => ∃ m, ReflTransGen r a m ∧ ReflTransGen s m b

/-- Confluence of a reflexive-transitive closure is the diamond property of that
closure: `Confluent (ReflTransGen r)` says peaks of `ReflTransGen r` join, after
collapsing the doubled closure. -/
private theorem closure_diamond_of_confluent (hcr : Confluent (ReflTransGen r))
    {a b c : α} (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) :
    ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d := by
  obtain ⟨d, hbd, hcd⟩ := hcr (ReflTransGen.single hab) (ReflTransGen.single hac)
  rw [reflTransGen_idem] at hbd hcd
  exact ⟨d, hbd, hcd⟩

/-- The bridge relation is reflexive: stay put in `r`, then stay put in `s`. -/
private theorem commStep_refl (a : α) : commStep r s a a :=
  ⟨a, ReflTransGen.refl, ReflTransGen.refl⟩

/-- A union step is a bridge step. An `r`-step is `r`-reduction then trivial
`s`-reduction; an `s`-step is trivial `r`-reduction then `s`-reduction. -/
private theorem commStep_of_union {a b : α} (h : unionRel r s a b) : commStep r s a b := by
  cases h with
  | inl hr => exact ⟨b, ReflTransGen.single hr, ReflTransGen.refl⟩
  | inr hs => exact ⟨a, ReflTransGen.refl, ReflTransGen.single hs⟩

/-- A bridge step is a union reduction: both legs embed into the union closure. -/
private theorem reflTransGen_union_of_commStep {a b : α} (h : commStep r s a b) :
    ReflTransGen (unionRel r s) a b := by
  obtain ⟨m, ham, hmb⟩ := h
  exact (ham.mono (fun _ _ hx => Or.inl hx)).trans (hmb.mono (fun _ _ hx => Or.inr hx))

/-- The union closure and the bridge closure coincide: the union is contained in the
bridge, the bridge is contained in the union closure, and reflexive-transitive
closure is monotone and idempotent. -/
private theorem reflTransGen_commStep_eq_union :
    ReflTransGen (commStep r s) = ReflTransGen (unionRel r s) := by
  apply le_antisymm
  · intro a b h
    have : ReflTransGen (ReflTransGen (unionRel r s)) a b :=
      h.mono (fun _ _ hx => reflTransGen_union_of_commStep hx)
    rwa [reflTransGen_idem] at this
  · intro a b h
    exact h.mono (fun _ _ hx => commStep_of_union hx)

/-- The bridge relation has the diamond property. Given two bridge steps out of `a`,
the `r`-legs meet by confluence of `r`; commutation slides each `s`-leg across that
meet; and the two resulting `s`-reductions meet by confluence of `s`. The common
bridge reduct is the `r`-leg into the commuted point followed by the final
`s`-reduction. -/
private theorem commStep_diamond
    (hcr : Confluent (ReflTransGen r)) (hcs : Confluent (ReflTransGen s))
    (hcomm : Commute (ReflTransGen r) (ReflTransGen s)) :
    Diamond (commStep r s) := by
  rintro a b₁ b₂ ⟨m₁, ham₁, hm₁b₁⟩ ⟨m₂, ham₂, hm₂b₂⟩
  -- the two `r`-legs meet at `p`
  obtain ⟨p, hm₁p, hm₂p⟩ := closure_diamond_of_confluent hcr ham₁ ham₂
  -- slide each `s`-leg across the `r`-reduction into `p`
  obtain ⟨q₁, hb₁q₁, hpq₁⟩ := hcomm hm₁b₁ hm₁p
  obtain ⟨q₂, hb₂q₂, hpq₂⟩ := hcomm hm₂b₂ hm₂p
  -- the two `s`-reductions out of `p` meet at `e`
  obtain ⟨e, hq₁e, hq₂e⟩ := closure_diamond_of_confluent hcs hpq₁ hpq₂
  refine ⟨e, ⟨q₁, hb₁q₁, hq₁e⟩, ⟨q₂, hb₂q₂, hq₂e⟩⟩

/-- The Hindley-Rosen theorem: if the reflexive-transitive closures of `r` and `s`
commute, and each is confluent, then the closure of their union `r ∪ s` is confluent.
The bridge relation `commStep` has the diamond property, its closure is the union
closure, and the diamond lemma lifts that to confluence. -/
theorem commute_imp_union_confluent
    (hcomm : Commute (ReflTransGen r) (ReflTransGen s))
    (hcr : Confluent (ReflTransGen r)) (hcs : Confluent (ReflTransGen s)) :
    Confluent (ReflTransGen (fun a b => r a b ∨ s a b)) := by
  have hd : Diamond (commStep r s) := commStep_diamond hcr hcs hcomm
  have hconf : Confluent (ReflTransGen (commStep r s)) := diamond_imp_confluent hd
  -- transport along the equality of closures
  have heq : ReflTransGen (commStep r s) = ReflTransGen (unionRel r s) :=
    reflTransGen_commStep_eq_union
  intro a b c hab hac
  rw [show (fun a b => r a b ∨ s a b) = unionRel r s from rfl, ← heq] at hab hac ⊢
  exact hconf hab hac

end HindleyRosen

/-! ## Priority 5: specialization to the library rewrite relation

The abstract diamond lemma instantiates at the one-step rewrite relation `Step R`:
if `Step R` has the diamond property then `StepStar R` (its reflexive-transitive
closure) is confluent. `StepStar R` is definitionally `ReflTransGen (Step R)`, so
`diamond_imp_confluent` applies directly. -/

section Library

universe w x

variable {sigma : Type w} {nu : Type x}

/-- If the one-step rewrite relation `Step R` has the diamond property, then the
reflexive-transitive rewrite relation `StepStar R` is confluent: every rewrite peak
`b ↞ a ↠ c` joins at a common reduct. This is the diamond lemma specialized to the
library relation, with `StepStar R` unfolded to `ReflTransGen (Step R)`. -/
theorem stepStar_confluent_of_diamond {R : TRS sigma nu}
    (hd : Diamond (Step R)) :
    ∀ ⦃a b c : Term sigma nu⦄, StepStar R a b → StepStar R a c → joinable R b c := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := diamond_imp_confluent_base hd hab hac
  exact ⟨d, hbd, hcd⟩

end Library

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @Diamond
open OperatorKO7.Meta.Rewriting in
#check @Confluent
open OperatorKO7.Meta.Rewriting in
#check @ChurchRosser
open OperatorKO7.Meta.Rewriting in
#check @Commute
open OperatorKO7.Meta.Rewriting in
#check @churchRosser_iff_confluent
open OperatorKO7.Meta.Rewriting in
#check @diamond_imp_confluent
open OperatorKO7.Meta.Rewriting in
#check @diamond_imp_confluent_base
open OperatorKO7.Meta.Rewriting in
#check @commute_imp_union_confluent
open OperatorKO7.Meta.Rewriting in
#check @stepStar_confluent_of_diamond

#print axioms OperatorKO7.Meta.Rewriting.diamond_eq
#print axioms OperatorKO7.Meta.Rewriting.confluent_eq
#print axioms OperatorKO7.Meta.Rewriting.commute_eq
#print axioms OperatorKO7.Meta.Rewriting.churchRosser_iff_confluent
#print axioms OperatorKO7.Meta.Rewriting.diamond_imp_confluent
#print axioms OperatorKO7.Meta.Rewriting.commute_imp_union_confluent
#print axioms OperatorKO7.Meta.Rewriting.stepStar_confluent_of_diamond
