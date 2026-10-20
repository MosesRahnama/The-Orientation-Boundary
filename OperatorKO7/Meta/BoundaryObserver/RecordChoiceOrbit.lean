import OperatorKO7.Meta.BoundaryObserver.NoReturn
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

set_option autoImplicit false

/-!
# Record choices of an observer, one orbit of the invisible group

An observer `q : X → Q` is an action on the states and, in Landau's vocabulary, a phase
transition: the symmetry group of `X` changes from the trivial group to the invisible group
`licenseStabilizer q`, the permutations `σ` with `q ∘ σ = q`. The observation is the partition
of `X` that the action leaves, the kernel of `q`. A state transition is a map from states to
states. The observer is one only through a record choice `u`, one state for each record, and
the composite `e = recordChoice q u` of `NoReturn.lean`, an idempotent map, up to the invisible
group, as the theorems below state.

The theorems state the sentence after Proposition `prop:idempotent` of
`Rahnama_The_Boundary_Theorem_Math.tex`:

* `recordChoice_merges_iff`: `e` merges the pairs that `q` merges and no others;
* `recordChoice_eq_iff`: distinct choices give distinct composites;
* `recordChoice_conj`: two choices `u`, `u'` differ by the invisible involution `fiberExchange`,
  the exchange of `u y` and `u' y` inside each fiber that fixes every other state, and
  `e' = σ e σ⁻¹`;
* `recordChoice_conj_closed`: conjugation by an invisible permutation sends a record choice to a
  record choice, so with `recordChoice_conj` the record choices form one orbit of the invisible
  group under conjugation;
* `recordChoice_stabilizer_iff`: the stabilizer of `e` in the invisible group is the subgroup
  that fixes every chosen state `u y`;
* `recordChoice_conj_free_iff`: that stabilizer is trivial if and only if every fiber holds at
  most one state besides the chosen one, so the orbit is free if and only if no fiber has three
  or more states.

The observer is therefore a state transition up to the invisible group and no further, and
`phase transition` stays the name of the action.

Proof graph: `Audit/ledgers/boundary-theorem/WAVE6-PROOF-GRAPH.md`, node N25.

Relation: none. Trust: kernel-only, with `Classical.choice` for the decidability of equality
on `X` in `fiberExchange` and `observerSwap`. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.RecordChoiceOrbit

open OperatorKO7.Meta.BoundaryObserver.NoReturn
open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! ## Merges of a record choice -/

/--
Proves: the composite `recordChoice q u` of an observer with a record choice merges two states
if and only if `q` merges them.
Trust: kernel-only.
-/
theorem recordChoice_merges_iff {X Q : Type*} (q : X → Q) (u : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y) (x x' : X) :
    recordChoice q u x = recordChoice q u x' ↔ q x = q x' := by
  have hq := (recordChoice_idempotent q u hu).2.1
  constructor
  · intro h
    calc q x = q (recordChoice q u x) := (hq x).symm
      _ = q (recordChoice q u x') := by rw [h]
      _ = q x' := hq x'
  · intro h
    have hf : Set.rangeFactorization q x = Set.rangeFactorization q x' := Subtype.ext h
    show u (Set.rangeFactorization q x) = u (Set.rangeFactorization q x')
    rw [hf]

/--
Proves: two record choices give the same composite if and only if they are the same choice.
The statement holds for every pair of maps `Set.range q → X`, sections or not.
Trust: kernel-only.
-/
theorem recordChoice_eq_iff {X Q : Type*} (q : X → Q) (u u' : Set.range q → X) :
    recordChoice q u = recordChoice q u' ↔ u = u' := by
  constructor
  · intro h
    funext y
    obtain ⟨x, hx⟩ := y.2
    have hy : Set.rangeFactorization q x = y := Subtype.ext hx
    subst hy
    exact congrFun h x
  · rintro rfl
    rfl

/-! ## The exchange of two record choices -/

open Classical in
/-- The map that exchanges `u y` and `u' y` inside the fiber of each record `y` and fixes every
other state. -/
noncomputable def fiberExchange {X Q : Type*} (q : X → Q) (u u' : Set.range q → X) (x : X) : X :=
  if x = u (Set.rangeFactorization q x) then u' (Set.rangeFactorization q x)
  else if x = u' (Set.rangeFactorization q x) then u (Set.rangeFactorization q x) else x

private theorem fiberExchange_of_eq {X Q : Type*} (q : X → Q) (u u' : Set.range q → X) (x : X)
    (h : x = u (Set.rangeFactorization q x)) :
    fiberExchange q u u' x = u' (Set.rangeFactorization q x) := by
  unfold fiberExchange
  rw [if_pos h]

private theorem fiberExchange_of_ne_of_eq {X Q : Type*} (q : X → Q) (u u' : Set.range q → X)
    (x : X) (h1 : x ≠ u (Set.rangeFactorization q x))
    (h2 : x = u' (Set.rangeFactorization q x)) :
    fiberExchange q u u' x = u (Set.rangeFactorization q x) := by
  unfold fiberExchange
  rw [if_neg h1, if_pos h2]

private theorem fiberExchange_of_ne_of_ne {X Q : Type*} (q : X → Q) (u u' : Set.range q → X)
    (x : X) (h1 : x ≠ u (Set.rangeFactorization q x))
    (h2 : x ≠ u' (Set.rangeFactorization q x)) :
    fiberExchange q u u' x = x := by
  unfold fiberExchange
  rw [if_neg h1, if_neg h2]

/-- The exchange keeps the record of every state. -/
private theorem fiberExchange_rangeFactorization {X Q : Type*} (q : X → Q)
    (u u' : Set.range q → X) (hu : ∀ y, Set.rangeFactorization q (u y) = y)
    (hu' : ∀ y, Set.rangeFactorization q (u' y) = y) (x : X) :
    Set.rangeFactorization q (fiberExchange q u u' x) = Set.rangeFactorization q x := by
  by_cases h1 : x = u (Set.rangeFactorization q x)
  · rw [fiberExchange_of_eq q u u' x h1, hu']
  · by_cases h2 : x = u' (Set.rangeFactorization q x)
    · rw [fiberExchange_of_ne_of_eq q u u' x h1 h2, hu]
    · rw [fiberExchange_of_ne_of_ne q u u' x h1 h2]

/-- The exchange applied twice is the identity. -/
private theorem fiberExchange_involutive {X Q : Type*} (q : X → Q) (u u' : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y)
    (hu' : ∀ y, Set.rangeFactorization q (u' y) = y) :
    Function.Involutive (fiberExchange q u u') := by
  intro x
  by_cases h1 : x = u (Set.rangeFactorization q x)
  · rw [fiberExchange_of_eq q u u' x h1]
    by_cases h2 : u' (Set.rangeFactorization q x) = u (Set.rangeFactorization q x)
    · rw [fiberExchange_of_eq q u u' (u' (Set.rangeFactorization q x)) (by rw [hu']; exact h2),
        hu', h2]
      exact h1.symm
    · rw [fiberExchange_of_ne_of_eq q u u' (u' (Set.rangeFactorization q x))
        (by rw [hu']; exact h2) (by rw [hu']), hu']
      exact h1.symm
  · by_cases h2 : x = u' (Set.rangeFactorization q x)
    · rw [fiberExchange_of_ne_of_eq q u u' x h1 h2,
        fiberExchange_of_eq q u u' (u (Set.rangeFactorization q x)) (by rw [hu]), hu]
      exact h2.symm
    · rw [fiberExchange_of_ne_of_ne q u u' x h1 h2, fiberExchange_of_ne_of_ne q u u' x h1 h2]

/--
Proves: two record choices `u`, `u'` of an observer differ by an invisible permutation `σ`, the
exchange of `u y` and `u' y` inside each fiber, an involution that fixes every other state, and
`recordChoice q u' = σ ∘ recordChoice q u ∘ σ⁻¹`.
Trust: kernel-only, with `Classical.choice`.
-/
theorem recordChoice_conj {X Q : Type*} (q : X → Q) (u u' : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y)
    (hu' : ∀ y, Set.rangeFactorization q (u' y) = y) :
    ∃ σ : Equiv.Perm X, (∀ x, q (σ x) = q x) ∧ (∀ y, σ (u y) = u' y) ∧ σ.symm = σ ∧
      (∀ x, x ≠ u (Set.rangeFactorization q x) → x ≠ u' (Set.rangeFactorization q x) →
        σ x = x) ∧
      ∀ x, recordChoice q u' x = σ (recordChoice q u (σ.symm x)) := by
  have hinv := fiberExchange_involutive q u u' hu hu'
  have hrf := fiberExchange_rangeFactorization q u u' hu hu'
  refine ⟨hinv.toPerm _, ?_, ?_, Function.Involutive.toPerm_symm hinv, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (hrf x)
  · intro y
    show fiberExchange q u u' (u y) = u' y
    rw [fiberExchange_of_eq q u u' (u y) (by rw [hu]), hu]
  · intro x h1 h2
    exact fiberExchange_of_ne_of_ne q u u' x h1 h2
  · intro x
    show u' (Set.rangeFactorization q x) =
      fiberExchange q u u' (u (Set.rangeFactorization q (fiberExchange q u u' x)))
    rw [hrf x, fiberExchange_of_eq q u u' (u (Set.rangeFactorization q x)) (by rw [hu]), hu]

/-- An invisible permutation keeps the record of the inverse image of every state. -/
private theorem rangeFactorization_symm_apply {X Q : Type*} (q : X → Q) (σ : Equiv.Perm X)
    (hσ : ∀ x, q (σ x) = q x) (x : X) :
    Set.rangeFactorization q (σ.symm x) = Set.rangeFactorization q x := by
  apply Subtype.ext
  have h := hσ (σ.symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/--
Proves: conjugation by an invisible permutation `σ` sends the record choice `u` to the record
choice `σ ∘ u`: `σ ∘ u` is again a section of the records, and
`σ ∘ recordChoice q u ∘ σ⁻¹ = recordChoice q (σ ∘ u)`. With `recordChoice_conj`, the record
choices of `q` form one orbit of the invisible group under conjugation.
Trust: kernel-only.
-/
theorem recordChoice_conj_closed {X Q : Type*} (q : X → Q) (u : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y) (σ : Equiv.Perm X)
    (hσ : ∀ x, q (σ x) = q x) :
    (∀ y, Set.rangeFactorization q (σ (u y)) = y) ∧
      ∀ x, σ (recordChoice q u (σ.symm x)) = recordChoice q (fun y => σ (u y)) x := by
  refine ⟨fun y => ?_, fun x => ?_⟩
  · have h1 : Set.rangeFactorization q (σ (u y)) = Set.rangeFactorization q (u y) :=
      Subtype.ext (hσ (u y))
    exact h1.trans (hu y)
  · show σ (u (Set.rangeFactorization q (σ.symm x))) = σ (u (Set.rangeFactorization q x))
    rw [rangeFactorization_symm_apply q σ hσ x]

/-! ## The stabilizer of a record choice -/

/--
Proves: an invisible permutation `σ` fixes `recordChoice q u` under conjugation if and only if
it fixes every chosen state `u y`.
Trust: kernel-only.
-/
theorem recordChoice_stabilizer_iff {X Q : Type*} (q : X → Q) (u : Set.range q → X)
    (σ : Equiv.Perm X) (hσ : ∀ x, q (σ x) = q x) :
    (∀ x, σ (recordChoice q u (σ.symm x)) = recordChoice q u x) ↔ ∀ y, σ (u y) = u y := by
  have hrf := rangeFactorization_symm_apply q σ hσ
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := y.2
    have hy : Set.rangeFactorization q x = y := Subtype.ext hx
    subst hy
    have hx' := h x
    unfold recordChoice at hx'
    rw [hrf] at hx'
    exact hx'
  · intro h x
    show σ (u (Set.rangeFactorization q (σ.symm x))) = u (Set.rangeFactorization q x)
    rw [hrf]
    exact h _

/--
Proves: the stabilizer of `recordChoice q u` in the invisible group is trivial if and only if
every fiber of `q` holds at most one state besides the chosen one, that is, no fiber has three
or more states.
Trust: kernel-only, with `Classical.choice` through `observerSwap`.
-/
theorem recordChoice_conj_free_iff {X Q : Type*} (q : X → Q) (u : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y) :
    (∀ σ : Equiv.Perm X, (∀ x, q (σ x) = q x) → (∀ y, σ (u y) = u y) → σ = 1) ↔
      ∀ a b : X, q a = q b → a ≠ u (Set.rangeFactorization q a) →
        b ≠ u (Set.rangeFactorization q a) → a = b := by
  constructor
  · intro hfree a b hab ha hb
    by_contra hne
    have hσ : observerSwap a b ∈ licenseStabilizer q := swap_mem_licenseStabilizer_of_eq q hab
    have hfix : ∀ y, observerSwap a b (u y) = u y := by
      intro y
      classical
      have hya : u y ≠ a := by
        intro h
        apply ha
        have hra : Set.rangeFactorization q a = y := by rw [← h]; exact hu y
        rw [hra, h]
      have hyb : u y ≠ b := by
        intro h
        apply hb
        have hrb : Set.rangeFactorization q b = y := by rw [← h]; exact hu y
        have hrab : Set.rangeFactorization q a = Set.rangeFactorization q b := Subtype.ext hab
        rw [hrab, hrb, h]
      rw [observerSwap, Equiv.swap_apply_of_ne_of_ne hya hyb]
    have h1 := hfree (observerSwap a b) hσ hfix
    have h2 : b = a := by
      simpa [observerSwap] using congrArg (fun τ : Equiv.Perm X => τ a) h1
    exact hne h2.symm
  · intro h σ hσ hfix
    apply Equiv.ext
    intro x
    rw [Equiv.Perm.one_apply]
    have hr : Set.rangeFactorization q (σ x) = Set.rangeFactorization q x := Subtype.ext (hσ x)
    by_cases hx : x = u (Set.rangeFactorization q x)
    · have hfx := hfix (Set.rangeFactorization q x)
      rw [← hx] at hfx
      exact hfx
    · apply h (σ x) x (hσ x)
      · rw [hr]
        intro hσx
        apply hx
        apply σ.injective
        rw [hσx, hfix]
      · rw [hr]
        exact hx

end OperatorKO7.Meta.BoundaryObserver.RecordChoiceOrbit
