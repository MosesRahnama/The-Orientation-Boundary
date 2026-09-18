/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.UniqueNormalization.Coalgebra
import OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport

/-!
# `DownOn` is the least Horn fixed point

The relativized invariant `DownOn A R` of Definition 40 is defined
impredicatively as the intersection of every closed relation.  This module
gives the predicative reading: `DownOn A R a b` holds exactly when the pair
`(a, b)` is derivable in the Horn calculus whose

* facts are the diagonal pairs on `A` (`downFacts`), and
* rules are the one-step unfoldings of the operator, with premise set the
  finite relation the step quantifies over (`downRule`).

Soundness (`hornDeriv_downOn`) is induction on the derivation; completeness
(`downOn_hornDeriv`) is induction over the impredicative fixed point, with
each operator case discharged by one Horn rule over an explicitly computed
finite premise set.

## Consequences

* `downOn_least_closed`: the fixed point is simultaneously closed and least.
* `downOn_excludes_unfounded`: any unfounded component of the Horn reading
  is disjoint from `DownOn`.
* `downOn_not_self_certified`: a pair off the diagonal whose every
  supporting step cites the pair itself is never in `DownOn`.  This is the
  coalgebraic face of the self-application gap.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false
-- `hornDeriv_downOn` and `downOn_least_closed` never build a finset.
set_option linter.unusedSectionVars false

namespace OperatorKO7.Meta.ProofSearchBoundary.DownLeast

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport

universe u v w w'

variable {sigma : Type u} {nu : Type v}
  [DecidableEq (Term (sigma ⊕ sigma) nu)]

/-- The carrier of the Horn reading: ordered pairs of terms. -/
abbrev DownPair (sigma : Type u) (nu : Type v) :=
  Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu

/-- The Horn facts: diagonal pairs on the coalgebra. -/
def downFacts (A : List (Term (sigma ⊕ sigma) nu)) : DownPair sigma nu → Prop :=
  fun p => p.1 = p.2 ∧ p.1 ∈ A

/-- The Horn rules: `q` follows from the finite premise set `P` when one
unfolding of the Definition-40 operator at `q` cites only pairs in `P`. -/
def downRule (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (P : Finset (DownPair sigma nu)) (q : DownPair sigma nu) : Prop :=
  DownStepOn A R (fun a b => (a, b) ∈ P) q.1 q.2

/-! ## Zip helpers -/

/-- Every member of the zip of a `Forall₂`-related pair of lists is
related. -/
theorem forall₂_mem_zip {α : Type w} {β : Type w'} {r : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ r l₁ l₂) :
    ∀ p ∈ l₁.zip l₂, r p.1 p.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | cons hab _ ih =>
      intro p hp
      rw [List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hab
      · exact ih _ hp'

/-- A `Forall₂`-related pair of lists is related by membership in the
finset of its zip. -/
theorem forall₂_zip_toFinset {α : Type w} {β : Type w'}
    [DecidableEq α] [DecidableEq β] {r : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ r l₁ l₂) :
    List.Forall₂ (fun a b => (a, b) ∈ (l₁.zip l₂).toFinset) l₁ l₂ := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
      refine List.Forall₂.cons ?_ (forall₂_mono (fun a b hab' => ?_) ih)
      · rw [List.zip_cons_cons, List.toFinset_cons]
        exact Finset.mem_insert_self _ _
      · rw [List.zip_cons_cons, List.toFinset_cons]
        exact Finset.mem_insert_of_mem hab'

/-! ## Soundness and completeness -/

/-- Every Horn-derivable pair is in the invariant. -/
theorem hornDeriv_downOn {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {p : DownPair sigma nu}
    (h : HornDeriv (downFacts A) (downRule A R) p) : DownOn A R p.1 p.2 := by
  induction h with
  | fact hf =>
      obtain ⟨heq, hmem⟩ := hf
      rw [heq] at hmem ⊢
      exact DownOn.refl hmem
  | rule hrule _ ih =>
      exact DownOn.closed _ _ (DownStepOn_mono (fun a b hab => ih (a, b) hab) hrule)

/-- Every pair in the invariant is Horn-derivable. -/
theorem downOn_hornDeriv {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : DownOn A R a b) :
    HornDeriv (downFacts A) (downRule A R) (a, b) := by
  refine DownOn.induction
    (P := fun x y => HornDeriv (downFacts A) (downRule A R) (x, y)) ?_ h
  intro p q hpq
  obtain ⟨hpA, hqA, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hcA, hroot, hcb⟩ |
    ⟨d, as, cs, hpdef, hall, hmem, hcb⟩ | hhat | hbar
  · exact HornDeriv.fact ⟨heq, hpA⟩
  · exact HornDeriv.rule (P := {(q, p)})
      ⟨hpA, hqA, Or.inr (Or.inl (Finset.mem_singleton_self _))⟩
      (fun x hx => by
        obtain rfl := Finset.mem_singleton.mp hx
        exact hinv.2)
  · exact HornDeriv.rule (P := {(c, q)})
      ⟨hpA, hqA, Or.inr (Or.inr (Or.inl
        ⟨c, hcA, hroot, Finset.mem_singleton_self _⟩))⟩
      (fun x hx => by
        obtain rfl := Finset.mem_singleton.mp hx
        exact hcb.2)
  · have hallH :
        List.Forall₂
          (fun x y => HornDeriv (downFacts A) (downRule A R) (x, y)) as cs :=
      forall₂_mono (fun a b hab => hab.2) hall
    have hallZ :
        List.Forall₂ (fun a b => (a, b) ∈ (as.zip cs).toFinset) as cs :=
      forall₂_zip_toFinset hallH
    refine HornDeriv.rule
      (P := (as.zip cs).toFinset ∪ {(.app (Sum.inr d) cs, q)})
      ⟨hpA, hqA, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, as, cs, hpdef,
          forall₂_mono (fun a b hab => Finset.mem_union_left _ hab) hallZ,
          hmem, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩)))⟩
      (fun x hx => by
        rcases Finset.mem_union.mp hx with hx | hx
        · exact forall₂_mem_zip hallH x (List.mem_toFinset.mp hx)
        · obtain rfl := Finset.mem_singleton.mp hx
          exact hcb.2)
  · obtain ⟨f, as, bs, ⟨c, hfc⟩, hpdef, hqdef, hall⟩ := hhat
    have hallH :
        List.Forall₂
          (fun x y => HornDeriv (downFacts A) (downRule A R) (x, y)) as bs :=
      forall₂_mono (fun a b hab => hab.2) hall
    have hallZ :
        List.Forall₂ (fun a b => (a, b) ∈ (as.zip bs).toFinset) as bs :=
      forall₂_zip_toFinset hallH
    exact HornDeriv.rule (P := (as.zip bs).toFinset)
      ⟨hpA, hqA, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨f, as, bs, ⟨c, hfc⟩, hpdef, hqdef, hallZ⟩))))⟩
      (fun x hx => forall₂_mem_zip hallH x (List.mem_toFinset.mp hx))
  · obtain ⟨f, as, bs, ⟨d, hfd⟩, hpdef, hqdef, hall⟩ := hbar
    have hallH :
        List.Forall₂
          (fun x y => HornDeriv (downFacts A) (downRule A R) (x, y)) as bs :=
      forall₂_mono (fun a b hab => hab.2) hall
    have hallZ :
        List.Forall₂ (fun a b => (a, b) ∈ (as.zip bs).toFinset) as bs :=
      forall₂_zip_toFinset hallH
    exact HornDeriv.rule (P := (as.zip bs).toFinset)
      ⟨hpA, hqA, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨f, as, bs, ⟨d, hfd⟩, hpdef, hqdef, hallZ⟩))))⟩
      (fun x hx => forall₂_mem_zip hallH x (List.mem_toFinset.mp hx))

/-- The invariant is exactly the Horn least fixed point. -/
theorem downOn_iff_hornDeriv {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    DownOn A R a b ↔ HornDeriv (downFacts A) (downRule A R) (a, b) :=
  ⟨downOn_hornDeriv, hornDeriv_downOn⟩

/-- The fixed point is closed and least, in one statement. -/
theorem downOn_least_closed {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {E : CRel sigma nu}
    (hE : ∀ p q, DownStepOn A R E p q → E p q)
    {a b : Term (sigma ⊕ sigma) nu}
    (h : DownStepOn A R (DownOn A R) a b) : E a b :=
  DownOn.least hE (DownOn.closed a b h)

/-! ## Unfounded and self-certified pairs -/

/-- Any unfounded component of the Horn reading is disjoint from the
invariant. -/
theorem downOn_excludes_unfounded {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {U : DownPair sigma nu → Prop}
    (hnofact : ∀ q, U q → ¬ downFacts A q)
    (hclosed : ∀ P q, downRule A R P q → U q → ∃ p ∈ P, U p)
    {a b : Term (sigma ⊕ sigma) nu} (h : DownOn A R a b) : ¬ U (a, b) :=
  unfounded_component_never_derivable hnofact hclosed (a, b)
    (downOn_hornDeriv h)

/-- A pair off the diagonal whose every supporting step cites the pair itself
is never in the invariant.  Inside the carrier the hypothesis never holds:
symmetry always supplies a step citing the reversed pair
(`selfCertified_hypothesis_fails_in_carrier`), so the theorem only covers pairs
outside the carrier.  The carrier-internal form of the self-application gap is
`mutual_citation_locally_justified_not_derivable`. -/
theorem downOn_not_self_certified {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {t u : Term (sigma ⊕ sigma) nu}
    (hne : t ≠ u)
    (hself : ∀ P : Finset (DownPair sigma nu),
      downRule A R P (t, u) → (t, u) ∈ P) :
    ¬ DownOn A R t u :=
  fun h => downOn_excludes_unfounded (U := fun p => p = (t, u))
    (fun q hq hfact => by
      subst hq
      exact hne hfact.1)
    (fun P q hrule hq => by
      subst hq
      exact ⟨(t, u), hself P hrule, rfl⟩)
    h rfl

/-- Inside the carrier the self-citation hypothesis of
`downOn_not_self_certified` fails: symmetry supplies a supporting step that
cites the reversed pair. -/
theorem selfCertified_hypothesis_fails_in_carrier
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {t u : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) (hu : u ∈ A) (hne : t ≠ u) :
    ¬ (∀ P : Finset (DownPair sigma nu), downRule A R P (t, u) → (t, u) ∈ P) := by
  intro hself
  have h := hself {(u, t)} ⟨ht, hu, Or.inr (Or.inl (Finset.mem_singleton_self _))⟩
  rw [Finset.mem_singleton] at h
  exact hne (Prod.mk.inj h).1

end OperatorKO7.Meta.ProofSearchBoundary.DownLeast

/-! ## Mutual citation in the empty system

Two distinct variables in the empty rewrite system: each of the pairs
`(x, y)` and `(y, x)` has a one-step justification citing the other, and
neither pair is in the invariant.  Local justification by mutual citation does
not ground a pair. -/

namespace OperatorKO7.Meta.ProofSearchBoundary.DownLeast.MutualCitation

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open OperatorKO7.Meta.ProofSearchBoundary.DownLeast

/-- The empty rewrite system over a doubled one-symbol signature. -/
def emptyTRS : TRS (Unit ⊕ Unit) Nat := []

/-- The first variable. -/
def varX : Term (Unit ⊕ Unit) Nat := .var 0

/-- The second variable. -/
def varY : Term (Unit ⊕ Unit) Nat := .var 1

/-- The two-term carrier. -/
def xyCarrier : List (Term (Unit ⊕ Unit) Nat) := [varX, varY]

/-- Each pair has a one-step justification citing the other. -/
theorem xy_mutual_local_justification :
    downRule xyCarrier emptyTRS {(varY, varX)} (varX, varY) ∧
      downRule xyCarrier emptyTRS {(varX, varY)} (varY, varX) :=
  ⟨⟨by simp [xyCarrier], by simp [xyCarrier],
      Or.inr (Or.inl (Finset.mem_singleton_self _))⟩,
    ⟨by simp [xyCarrier], by simp [xyCarrier],
      Or.inr (Or.inl (Finset.mem_singleton_self _))⟩⟩

/-- The component `{(x, y), (y, x)}` is unfounded, so neither pair is in the
invariant. -/
theorem xy_not_downOn :
    ¬ DownOn xyCarrier emptyTRS varX varY ∧
      ¬ DownOn xyCarrier emptyTRS varY varX := by
  have hU : ∀ a b, DownOn xyCarrier emptyTRS a b →
      ¬ ((a, b) = (varX, varY) ∨ (a, b) = (varY, varX)) := by
    intro a b h
    refine downOn_excludes_unfounded
      (U := fun p => p = (varX, varY) ∨ p = (varY, varX)) ?_ ?_ h
    · rintro q (rfl | rfl) ⟨heq, -⟩ <;> simp [varX, varY] at heq
    · rintro P q ⟨-, -, hbody⟩ (rfl | rfl)
      · rcases hbody with heq | hinv | ⟨c, -, hroot, -⟩ |
          ⟨d, as, cs, hpdef, -⟩ | ⟨f, as, bs, -, hpdef, -⟩ |
          ⟨f, as, bs, -, hpdef, -⟩
        · simp [varX, varY] at heq
        · exact ⟨(varY, varX), hinv, Or.inr rfl⟩
        · obtain ⟨rule, hmem, -⟩ := hroot
          simp [emptyTRS] at hmem
        · simp [varX] at hpdef
        · simp [varX] at hpdef
        · simp [varX] at hpdef
      · rcases hbody with heq | hinv | ⟨c, -, hroot, -⟩ |
          ⟨d, as, cs, hpdef, -⟩ | ⟨f, as, bs, -, hpdef, -⟩ |
          ⟨f, as, bs, -, hpdef, -⟩
        · simp [varX, varY] at heq
        · exact ⟨(varX, varY), hinv, Or.inl rfl⟩
        · obtain ⟨rule, hmem, -⟩ := hroot
          simp [emptyTRS] at hmem
        · simp [varY] at hpdef
        · simp [varY] at hpdef
        · simp [varY] at hpdef
  exact ⟨fun h => hU _ _ h (Or.inl rfl), fun h => hU _ _ h (Or.inr rfl)⟩

/-- Mutual citation justifies each pair locally and grounds neither. -/
theorem mutual_citation_locally_justified_not_derivable :
    (downRule xyCarrier emptyTRS {(varY, varX)} (varX, varY) ∧
      downRule xyCarrier emptyTRS {(varX, varY)} (varY, varX)) ∧
      ¬ DownOn xyCarrier emptyTRS varX varY ∧
      ¬ DownOn xyCarrier emptyTRS varY varX :=
  ⟨xy_mutual_local_justification, xy_not_downOn⟩

end OperatorKO7.Meta.ProofSearchBoundary.DownLeast.MutualCitation
