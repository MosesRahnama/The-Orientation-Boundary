import OperatorKO7.Kernel
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

/-!
# Observer expressivity: two lower bounds on defining the distinction observer

Manuscript anchors: the definability-boundary section of
`Rahnama_The_Distinction_Boundary` (the generic companion to the
seven-constructor inexpressibility theorem).

## What this module proves

* **T-E (generic clone no-go).** Over any carrier with a collapse point,
  a binary operation that is natural under an endomorphism which merges two
  distinct points and reflects the collapse point fails to be a sound and
  complete disequality discriminator. Term operations of a signature are
  natural under every endomorphism of the algebra, so no single term
  operation discriminates disequality on such an algebra.
* **T-FS (finite-state boundary).** Over the kernel carrier, which is
  infinite, a bottom-up observer with a finite state set and a parent
  decision reading only the two child states fails to recognise the diagonal
  exactly. An observer carrying an equality test decides it.

Together these place the exact distinction observer outside two observer
classes and inside a third, which is the hierarchy the manuscript states.

## Claim boundaries

* T-E is stated for one binary operation. It bounds a single term operation
  of a clone; multi-term programs, normalizers, and external decision
  procedures lie outside its scope, and the manuscript says so.
* The reflection hypothesis `h z = nil → z = nil` is load carrying and
  explicit. `endomorphismHypotheses_nonvacuous` exhibits a carrier and an
  endomorphism satisfying every hypothesis, so the class is inhabited.
* The finite-state statement is a background lemma in the automata sense.
  Tree automata with equality and disequality constraints are classical; the
  contribution here is the link to the confluence repair, which lives in the
  manuscript rather than in this module.

Relation: not applicable (carrier-level observations). Closure: not
applicable. Strategy: not applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

open OperatorKO7 Trace

/-! ## T-E. The generic term-clone no-go -/

section Clone

variable {A : Type*}

/-- A binary operation is a sound and complete disequality discriminator for a
collapse point when the operation leaves the collapse point exactly on
distinct arguments. -/
def IsDiscriminator (nil : A) (t : A → A → A) : Prop :=
  ∀ a b, t a b ≠ nil ↔ a ≠ b

/-- Naturality of a binary operation under a map. Every term operation of a
signature satisfies this for every endomorphism of the algebra, which is the
instance the manuscript uses. -/
def NaturalUnder (h : A → A) (t : A → A → A) : Prop :=
  ∀ x y, h (t x y) = t (h x) (h y)

/-- **T-E.** A binary operation natural under an endomorphism that merges two
distinct points and reflects the collapse point fails to discriminate
disequality. -/
theorem not_discriminator_of_natural_under_noninjective
    (nil : A) (h : A → A) (t : A → A → A)
    (hrefl : ∀ z, h z = nil → z = nil)
    (x y : A) (hxy : x ≠ y) (hmerge : h x = h y)
    (hnat : NaturalUnder h t) :
    ¬ IsDiscriminator nil t := by
  intro hdisc
  have hne : t x y ≠ nil := (hdisc x y).mpr hxy
  have hdiag : t (h x) (h y) = nil := by
    have hyy : t (h y) (h y) = nil := by
      by_contra hc
      exact ((hdisc (h y) (h y)).mp hc) rfl
    rw [hmerge]
    exact hyy
  have hcollapse : h (t x y) = nil := by
    rw [hnat x y]
    exact hdiag
  exact hne (hrefl _ hcollapse)

/-- The contrapositive reading: a carrier carrying a discriminator natural
under `h` forces `h` to separate every pair it is asked about. -/
theorem discriminator_forces_injective_on_pair
    (nil : A) (h : A → A) (t : A → A → A)
    (hrefl : ∀ z, h z = nil → z = nil)
    (hnat : NaturalUnder h t) (hdisc : IsDiscriminator nil t)
    (x y : A) (hmerge : h x = h y) : x = y := by
  by_contra hxy
  exact not_discriminator_of_natural_under_noninjective nil h t hrefl x y hxy hmerge hnat hdisc

end Clone

/-- R5 non-vacuity for T-E: the hypothesis class is inhabited. On a
three-point carrier with collapse point `0`, the map merging `2` into `1`
fixes `0`, reflects `0`, and merges two distinct points. -/
theorem endomorphismHypotheses_nonvacuous :
    ∃ (h : Fin 3 → Fin 3) (x y : Fin 3),
      (∀ z, h z = 0 → z = 0) ∧ x ≠ y ∧ h x = h y := by
  refine ⟨fun i => if i = 2 then 1 else i, 1, 2, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ## T-FS. The finite-state boundary -/

/-- Iterated `delta` over `void`, the injective copy of the naturals inside the
kernel carrier. -/
def dpow : ℕ → Trace
  | 0 => void
  | (n + 1) => delta (dpow n)

theorem dpow_injective : Function.Injective dpow := by
  intro m
  induction m with
  | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ k => exact absurd h (by simp [dpow])
  | succ k ih =>
      intro n h
      cases n with
      | zero => exact absurd h (by simp [dpow])
      | succ l =>
          have h' : dpow k = dpow l := by
            simp only [dpow, delta.injEq] at h
            exact h
          exact congrArg Nat.succ (ih h')

/-- A bottom-up observer with a finite state set: `state` folds a term into a
state, and `parent` decides the comparison node from the two child states
alone. -/
structure FiniteStateObserver (Q : Type*) where
  state : Trace → Q
  parent : Q → Q → Bool

/-- An observer recognises the diagonal exactly when its parent decision holds
of a pair if and only if the two terms coincide. -/
def RecognisesDiagonal {Q : Type*} (O : FiniteStateObserver Q) : Prop :=
  ∀ a b : Trace, O.parent (O.state a) (O.state b) = true ↔ a = b

/-- **T-FS.** No finite-state bottom-up observer recognises the diagonal of the
kernel carrier. Two distinct terms share a state, and the parent decision then
returns the same verdict on a diagonal pair and an off-diagonal pair. -/
theorem no_finiteState_observer_recognises_diagonal
    {Q : Type*} [Fintype Q] (O : FiniteStateObserver Q) :
    ¬ RecognisesDiagonal O := by
  intro hrec
  obtain ⟨i, j, hij, hstate⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card Q + 1) => O.state (dpow (i : ℕ)))
      (by simp)
  set u := dpow (i : ℕ) with hu
  set v := dpow (j : ℕ) with hv
  have huv : u ≠ v := by
    intro h
    exact hij (Fin.val_injective (dpow_injective h))
  have h1 : O.parent (O.state u) (O.state u) = true := (hrec u u).mpr rfl
  have h2 : O.parent (O.state u) (O.state v) = true := by
    rw [← hstate]
    exact h1
  exact huv ((hrec u v).mp h2)

/-- The positive comparison class: an observer carrying an equality test on the
carrier decides the diagonal. This is the classical equality-constrained
observer, recorded here as a background fact. -/
theorem equalityTest_decides_diagonal (a b : Trace) :
    (decide (a = b) = true) ↔ a = b :=
  decide_eq_true_iff

/-- Non-triviality for T-FS: the obstruction is about the finite state set
rather than about the parent decision, since the equality test above decides
the same predicate once the observer may compare the terms themselves. -/
theorem finiteState_boundary_is_about_state_finiteness :
    (∀ (Q : Type) [Fintype Q] (O : FiniteStateObserver Q), ¬ RecognisesDiagonal O) ∧
      (∀ a b : Trace, (decide (a = b) = true) ↔ a = b) := by
  refine ⟨?_, equalityTest_decides_diagonal⟩
  intro Q _ O
  exact no_finiteState_observer_recognises_diagonal O

end OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
