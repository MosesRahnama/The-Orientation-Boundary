/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.ProofSearchBoundary
import Mathlib.Tactic

/-!
# Grounded support and the support-substitution identity

Two independent pieces of the unsupported-promotion theory.

## Unfounded components

`HornDeriv facts rules` is grounded finite derivability in a Horn calculus:
a fact is derivable, and a rule fires when every premise is derivable.  A set
`U` is an *unfounded component* when no fact lands in `U` and every rule
concluding in `U` requires at least one premise inside `U`.  The theorem
`unfounded_component_never_derivable` shows such a component never enters the
grounded closure: grounded derivability selects the least fixed point, and a
self-supporting equation has both fixed points.  The iterated-finset form
`hornClosure` (`K 0 = facts`, `K (n+1) = K n ∪ {q | P ⊆ K n}`) proves the same
exclusion at every finite stage.

This concerns proof support only: a cyclic rational-tree description can
still be legitimate mathematical data.  Nothing here forbids coinduction or
cyclic proof systems with separate soundness conditions.

## Support substitution

For explicit proof syntax with named assumption leaves, substituting a
candidate `d` with support `D` for an assumption `h` with `h ∈ S` gives

`Supp(p[d/h]) = (S ∖ {h}) ∪ D`,

with cardinality

`|Supp(p[d/h])| = |S| - 1 + |D ∖ S| + [h ∈ D]`,

equivalently `Δ|Supp| = |D ∖ S| - [h ∉ D]`.  The advertised gain is removing
`h`; the actual cost is the replacement's dependencies, including whether `h`
returns.  The circular replacement `D = {h}` changes the support size by
zero.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

universe u

namespace OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport

/-! ## Horn derivability -/

/-- Grounded finite derivability in a Horn calculus with finset premise
sets. -/
inductive HornDeriv {α : Type u}
    (facts : α → Prop) (rules : Finset α → α → Prop) : α → Prop where
  | fact {q : α} : facts q → HornDeriv facts rules q
  | rule {P : Finset α} {q : α} :
      rules P q → (∀ p ∈ P, HornDeriv facts rules p) →
        HornDeriv facts rules q

/-- An unfounded component never enters the grounded closure: no derivation
concludes inside it. -/
theorem unfounded_component_never_derivable {α : Type u}
    {facts : α → Prop} {rules : Finset α → α → Prop} {U : α → Prop}
    (hnofact : ∀ q, U q → ¬ facts q)
    (hclosed : ∀ P q, rules P q → U q → ∃ p ∈ P, U p) :
    ∀ q, HornDeriv facts rules q → ¬ U q := by
  intro q hder
  induction hder with
  | fact hf =>
      intro hu
      exact hnofact _ hu hf
  | rule hrule _ ih =>
      intro hu
      obtain ⟨p, hpP, hpU⟩ := hclosed _ _ hrule hu
      exact ih p hpP hpU

/-! ## Iterated finite closure -/

/-- One closure step: add the conclusions of all rules whose premises are
already present. -/
def hornStep {α : Type u} [DecidableEq α]
    (rules : List (Finset α × α)) (K : Finset α) : Finset α :=
  K ∪ (rules.filterMap fun ⟨P, q⟩ => if P ⊆ K then some q else none).toFinset

/-- The iterated closure: `K 0 = facts`,
`K (n+1) = K n ∪ {q | (P, q) ∈ rules, P ⊆ K n}`. -/
def hornClosure {α : Type u} [DecidableEq α]
    (facts : Finset α) (rules : List (Finset α × α)) : ℕ → Finset α
  | 0 => facts
  | n + 1 => hornStep rules (hornClosure facts rules n)

/-- The iterated form of the unfounded-component property: at every finite
stage, no member of an unfounded component is present. -/
theorem unfounded_component_disjoint_hornClosure {α : Type u} [DecidableEq α]
    {facts : Finset α} {rules : List (Finset α × α)} {U : α → Prop}
    (hnofact : ∀ q ∈ facts, ¬ U q)
    (hclosed : ∀ P q, (P, q) ∈ rules → U q → ∃ p ∈ P, U p) :
    ∀ n q, q ∈ hornClosure facts rules n → ¬ U q := by
  intro n
  induction n with
  | zero =>
      intro q hq hu
      exact hnofact q hq hu
  | succ n ih =>
      intro q hq hu
      simp only [hornClosure, hornStep, Finset.mem_union,
        List.mem_toFinset, List.mem_filterMap] at hq
      rcases hq with hqn | ⟨⟨P, q'⟩, hPQ, hsome⟩
      · exact ih q hqn hu
      · split at hsome
        · next hsub =>
            have hqq : q' = q := Option.some.inj hsome
            subst hqq
            obtain ⟨p, hpP, hpU⟩ := hclosed P q' hPQ hu
            exact ih p (hsub hpP) hpU
        · cases hsome

/-! ## Support substitution -/

/-- Substitution support is erase-then-union:
`Supp(p[d/h]) = (S ∖ {h}) ∪ D`. -/
theorem support_substitution_set {α : Type u} [DecidableEq α]
    (S D : Finset α) (h : α) :
    (S.erase h) ∪ D = (S \ {h}) ∪ D := by
  rw [Finset.sdiff_singleton_eq_erase]

/-- The support-substitution cardinality identity: for `h ∈ S`,

`|(S ∖ {h}) ∪ D| = |S| - 1 + |D ∖ S| + [h ∈ D]`. -/
theorem support_substitution_card {α : Type u} [DecidableEq α]
    (S D : Finset α) (h : α) (hh : h ∈ S) :
    ((S.erase h) ∪ D).card =
      S.card - 1 + (D \ S).card + (if h ∈ D then 1 else 0) := by
  have hU := Finset.card_union_add_card_inter (S.erase h) D
  have hE := Finset.card_erase_of_mem hh
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨h, hh⟩
  have hI : (S.erase h) ∩ D = (S ∩ D).erase h := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have hDS : (D \ S).card + (S ∩ D).card = D.card := by
    have h := Finset.card_sdiff_add_card_inter D S
    rwa [Finset.inter_comm] at h
  rw [hI] at hU
  by_cases hd : h ∈ D
  · have hhI : h ∈ S ∩ D := Finset.mem_inter.mpr ⟨hh, hd⟩
    have hIc := Finset.card_erase_of_mem hhI
    have hIpos : 0 < (S ∩ D).card := Finset.card_pos.mpr ⟨h, hhI⟩
    simp only [hd, if_true]
    omega
  · have hhI : h ∉ S ∩ D := fun hm => hd (Finset.mem_inter.mp hm).2
    have hIc : ((S ∩ D).erase h).card = (S ∩ D).card := by
      rw [Finset.card_erase_eq_ite, if_neg hhI]
    simp only [hd, if_false]
    omega

/-- The dependency-cost form: `Δ|Supp| = |D ∖ S| - [h ∉ D]`. -/
theorem support_substitution_delta {α : Type u} [DecidableEq α]
    (S D : Finset α) (h : α) (hh : h ∈ S) :
    (((S.erase h) ∪ D).card : ℤ) - (S.card : ℤ) =
      ((D \ S).card : ℤ) - (if h ∈ D then (0 : ℤ) else 1) := by
  have hcard := support_substitution_card S D h hh
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨h, hh⟩
  by_cases hd : h ∈ D
  · simp only [hd, if_true] at hcard ⊢
    omega
  · simp only [hd, if_false] at hcard ⊢
    omega

/-- The circular replacement changes support size by zero: substituting a
candidate that still needs `h` for `h` itself returns the original support
cardinality. -/
theorem support_substitution_circular {α : Type u} [DecidableEq α]
    (S : Finset α) (h : α) (hh : h ∈ S) :
    ((S.erase h) ∪ {h}).card = S.card := by
  rw [Finset.union_singleton, Finset.insert_erase hh]

/-- A grounded replacement strictly removes the assumption: if `D ⊆ S` and
`h ∉ D`, the support size strictly drops. -/
theorem support_substitution_grounded_drop {α : Type u} [DecidableEq α]
    (S D : Finset α) (h : α) (hh : h ∈ S)
    (hsub : D ⊆ S) (hhd : h ∉ D) :
    ((S.erase h) ∪ D).card < S.card := by
  have hcard := support_substitution_card S D h hh
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨h, hh⟩
  have hD : D \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  simp only [hD, Finset.card_empty] at hcard
  simp only [hhd, if_false] at hcard
  omega

/-! ## Proof expressions (Proposition 5.2 on proof syntax)

The theorems above are set identities.  This section adds the proof syntax the
manuscript's Proposition 5.2 speaks about: expressions with named assumption
leaves, closed axiom leaves, and binary inference nodes (an n-ary node is a
nesting of binary ones), the support of an expression, and substitution of a
proof for every leaf of one assumption. -/

/-- Proof expressions with named assumption leaves. -/
inductive ProofExpr (α : Type u) where
  | assm (a : α)
  | axiomLeaf
  | infer (left right : ProofExpr α)

namespace ProofExpr

variable {α : Type u} [DecidableEq α]

/-- The undischarged assumption labels of a proof expression. -/
def supp : ProofExpr α → Finset α
  | assm a => {a}
  | axiomLeaf => ∅
  | infer l r => supp l ∪ supp r

/-- Replace every leaf `assm h` by the proof `d`. -/
def subst (h : α) (d : ProofExpr α) : ProofExpr α → ProofExpr α
  | assm a => if a = h then d else assm a
  | axiomLeaf => axiomLeaf
  | infer l r => infer (subst h d l) (subst h d r)

/-- Support under substitution, for any expression. -/
theorem supp_subst (h : α) (d p : ProofExpr α) :
    supp (subst h d p) =
      (supp p).erase h ∪ (if h ∈ supp p then supp d else ∅) := by
  induction p with
  | assm a =>
      by_cases ha : a = h
      · subst ha
        ext x
        simp [subst, supp]
      · have hh : h ∉ ({a} : Finset α) := by
          rw [Finset.mem_singleton]
          exact fun he => ha he.symm
        rw [show subst h d (assm a) = assm a from if_neg ha]
        simp only [supp, if_neg hh, Finset.union_empty]
        exact (Finset.erase_eq_of_notMem hh).symm
  | axiomLeaf =>
      simp [subst, supp]
  | infer l r ihl ihr =>
      simp only [subst, supp, ihl, ihr]
      ext x
      by_cases hxh : x = h
      · subst hxh
        by_cases hl : x ∈ supp l <;> by_cases hr : x ∈ supp r <;>
          simp [hl, hr, Finset.mem_union, Finset.mem_erase]
      · by_cases hl : h ∈ supp l <;> by_cases hr : h ∈ supp r <;>
          simp [hl, hr, hxh, Finset.mem_union, Finset.mem_erase] <;> tauto

/-- Proposition 5.2, first equation: for `h ∈ Supp p`,
`Supp(p[d/h]) = (Supp p ∖ {h}) ∪ Supp d`. -/
theorem supp_subst_of_mem (h : α) (d p : ProofExpr α) (hh : h ∈ supp p) :
    supp (subst h d p) = (supp p \ {h}) ∪ supp d := by
  rw [supp_subst, if_pos hh, Finset.sdiff_singleton_eq_erase]

/-- Proposition 5.2, second equation, in the manuscript's form:
`|Supp(p[d/h])| = |Supp p| - 1 + |Supp d ∖ (Supp p ∖ {h})|`. -/
theorem supp_subst_card (h : α) (d p : ProofExpr α) (hh : h ∈ supp p) :
    (supp (subst h d p)).card =
      (supp p).card - 1 + (supp d \ (supp p \ {h})).card := by
  rw [supp_subst_of_mem h d p hh]
  have hU := Finset.card_union_add_card_inter (supp p \ {h}) (supp d)
  have hD := Finset.card_sdiff_add_card_inter (supp d) (supp p \ {h})
  have hE : (supp p \ {h}).card = (supp p).card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hh]
  rw [Finset.inter_comm] at hD
  omega

/-- The manuscript's remark after Proposition 5.2: substituting a proof whose
support is `{h}` for `h` leaves the support unchanged. -/
theorem supp_subst_circular (h : α) (p : ProofExpr α) (hh : h ∈ supp p) :
    supp (subst h (assm h) p) = supp p := by
  rw [supp_subst_of_mem h (assm h) p hh]
  ext x
  simp only [supp, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (⟨hx, -⟩ | rfl)
    · exact hx
    · exact hh
  · intro hx
    by_cases hxh : x = h
    · exact Or.inr hxh
    · exact Or.inl ⟨hx, hxh⟩

end ProofExpr

end OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport
