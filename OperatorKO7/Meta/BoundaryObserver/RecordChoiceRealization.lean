import OperatorKO7.Meta.BoundaryObserver.RecordChoiceOrbit
import OperatorKO7.Meta.UniqueNormalization.NormalizerForests

set_option autoImplicit false

/-!
# Realizations of a record choice and the freeness of the conjugation action

`prop:record-choice-orbit` (v) and (vi) of the source manuscript (ledger row 04-003).
For an observer `q : X → Q` with a record choice `u` (one state per record, `q ∘ u = id`) the state
transition `e = u ∘ q` (`NoReturn.recordChoice`) is an idempotent, and the classification of the
realizations of an idempotent (`Normalization.realizes_iff`, `exists_leastRealizes_iff` of the
normal-forms development) reads on `e` as follows.

* `realizes_recordChoice_iff`: a relation realizes `e` iff its steps leave an unchosen state for a
  state with the same record and every state reaches its chosen state.
* `realizes_recordChoice_conv_iff`: the conversion of every realization is the kernel of `q`.
* `maxRel_recordChoice_realizes`, `realizes_recordChoice_subrel_maxRel`: the relation of all such
  steps realizes `e` and contains every realization.
* `leastRealization_iff_conjugation_free`: `e` has a least realization iff the identity is the only
  invisible permutation fixing every chosen state (clause (v)) iff no fiber of `q` has three
  states. The two conditions of clauses (v) and (vi) are one condition.

Relation: arbitrary relations `R` on `X`, their reflexive-transitive closure `Star` and
conversion `Conv`. Trust: kernel-only, with `Classical.choice` through the imported decidability
of equality. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.RecordChoiceRealization

open OperatorKO7.Meta.BoundaryObserver.NoReturn
open OperatorKO7.Meta.BoundaryObserver.RecordChoiceOrbit
open OperatorKO7.Meta.UniqueNormalization.Normalization

universe u v

variable {X : Type u} {Q : Type v}

/-- The record choice of a section is idempotent. -/
theorem recordChoice_idem (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) (x : X) :
    recordChoice q uc (recordChoice q uc x) = recordChoice q uc x :=
  (recordChoice_idempotent q uc hu).1 x

/--
Proves: the greatest compatible relation `M_e` of `e = recordChoice q u` relates `x` to `x'` iff
`x` is not the chosen state of its record and `q x = q x'`.
Scope: `prop:record-choice-orbit` (vi), the set `M_e`; row 04-003. Trust: kernel-only.
-/
theorem maxRel_recordChoice_iff (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) (x x' : X) :
    MaxRel (recordChoice q uc) x x' ↔
      x ≠ uc (Set.rangeFactorization q x) ∧ q x = q x' := by
  unfold MaxRel
  exact and_congr Iff.rfl (recordChoice_merges_iff q uc hu x x')

/--
Proves: a relation `R` realizes `e = recordChoice q u` (confluent, every state reaches `e x`, and
`e x` is normal) iff every step of `R` leaves an unchosen state for a state with the same record and
every state reaches its chosen state.
Relation: `R`, its reflexive-transitive closure `Star R`. Scope: `prop:record-choice-orbit` (vi);
row 04-003. Trust: kernel-only.
-/
theorem realizes_recordChoice_iff (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) (R : X → X → Prop) :
    Realizes R (recordChoice q uc) ↔
      (∀ x x', R x x' → x ≠ uc (Set.rangeFactorization q x) ∧ q x = q x') ∧
        ∀ x, Star R x (uc (Set.rangeFactorization q x)) := by
  rw [realizes_iff]
  constructor
  · rintro ⟨hs, hr⟩
    exact ⟨fun x x' h => (maxRel_recordChoice_iff q uc hu x x').mp (hs h), hr⟩
  · rintro ⟨hs, hr⟩
    exact ⟨fun x x' h => (maxRel_recordChoice_iff q uc hu x x').mpr (hs x x' h), hr⟩

/--
Proves: the conversion of every realization of `e = recordChoice q u` is the kernel of `q`.
Relation: `Conv R`, the equivalence closure of `R`. Scope: `prop:record-choice-orbit` (vi);
row 04-003. Trust: kernel-only.
-/
theorem realizes_recordChoice_conv_iff (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) {R : X → X → Prop}
    (hR : Realizes R (recordChoice q uc)) (x x' : X) :
    Conv R x x' ↔ q x = q x' :=
  hR.conv_iff.trans (recordChoice_merges_iff q uc hu x x')

/--
Proves: `M_e` realizes `e = recordChoice q u`.
Scope: `prop:record-choice-orbit` (vi); row 04-003. Trust: kernel-only.
-/
theorem maxRel_recordChoice_realizes (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) :
    Realizes (MaxRel (recordChoice q uc)) (recordChoice q uc) :=
  maxRel_realizes (recordChoice_idem q uc hu)

/--
Proves: every realization of `e` lies inside `M_e`, so `M_e` is the greatest realization.
Scope: `prop:record-choice-orbit` (vi); row 04-003. Trust: kernel-only.
-/
theorem realizes_recordChoice_subrel_maxRel (q : X → Q) (uc : Set.range q → X)
    {R : X → X → Prop} (hR : Realizes R (recordChoice q uc)) :
    Subrel R (MaxRel (recordChoice q uc)) :=
  hR.subrel_maxRel

/--
Proves: the fibers of `e = recordChoice q u` hold at most two states iff every fiber of `q` holds
at most one state besides the chosen one.
Scope: the bridge between `FibersAtMostTwo` and the condition of `recordChoice_conj_free_iff`;
row 04-003. Trust: kernel-only, with `Classical.choice`.
-/
theorem fibersAtMostTwo_recordChoice_iff_unchosen (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) :
    FibersAtMostTwo (recordChoice q uc) ↔
      ∀ a b : X, q a = q b → a ≠ uc (Set.rangeFactorization q a) →
        b ≠ uc (Set.rangeFactorization q a) → a = b := by
  classical
  rw [fibersAtMostTwo_iff (recordChoice_idem q uc hu)]
  constructor
  · intro h a b hab ha hb
    have hrf : Set.rangeFactorization q b = Set.rangeFactorization q a := Subtype.ext hab.symm
    have hab' : recordChoice q uc a = recordChoice q uc b :=
      (recordChoice_merges_iff q uc hu a b).mpr hab
    rcases h a b hab' with h1 | h2 | h3
    · exact absurd h1 ha
    · exact absurd (show b = uc (Set.rangeFactorization q a) by rw [← hrf]; exact h2) hb
    · exact h3
  · intro h x y hxy
    have hq : q x = q y := (recordChoice_merges_iff q uc hu x y).mp hxy
    have hrf : Set.rangeFactorization q y = Set.rangeFactorization q x := Subtype.ext hq.symm
    by_cases hx : x = recordChoice q uc x
    · exact Or.inl hx
    · by_cases hy : y = recordChoice q uc y
      · exact Or.inr (Or.inl hy)
      · refine Or.inr (Or.inr (h x y hq hx ?_))
        intro hy'
        apply hy
        show y = uc (Set.rangeFactorization q y)
        rw [hrf]
        exact hy'

/--
Proves: the fibers of `e = recordChoice q u` hold at most two states iff no fiber of `q` has three
distinct states.
Scope: `prop:record-choice-orbit` (v), (vi); row 04-003. Trust: kernel-only.
-/
theorem fibersAtMostTwo_recordChoice_iff_three (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) :
    FibersAtMostTwo (recordChoice q uc) ↔
      ∀ a b c : X, q a = q b → q a = q c → a = b ∨ a = c ∨ b = c := by
  constructor
  · intro h a b c hab hac
    exact h (recordChoice q uc a) a b c rfl
      ((recordChoice_merges_iff q uc hu b a).mpr hab.symm)
      ((recordChoice_merges_iff q uc hu c a).mpr hac.symm)
  · intro h r x y z hx hy hz
    have hxy : q x = q y := (recordChoice_merges_iff q uc hu x y).mp (hx.trans hy.symm)
    have hxz : q x = q z := (recordChoice_merges_iff q uc hu x z).mp (hx.trans hz.symm)
    exact h x y z hxy hxz

/--
`prop:record-choice-orbit`, clauses (v) and (vi) joined.

Proves: for a record choice `u` of `q`, the state transition `e = u ∘ q` has a least realization
iff the identity is the only invisible permutation that fixes every chosen state `u y`; and it has
a least realization iff no fiber of `q` has three distinct states.
Relation: arbitrary realizing relations of `e` with `Star` and `Conv`. Scope: row 04-003, the Lean
name the ledger asks for. Trust: kernel-only, with `Classical.choice`.
-/
theorem leastRealization_iff_conjugation_free (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) :
    ((∃ R : X → X → Prop, LeastRealizes R (recordChoice q uc)) ↔
        ∀ σ : Equiv.Perm X, (∀ x, q (σ x) = q x) → (∀ y, σ (uc y) = uc y) → σ = 1) ∧
      ((∃ R : X → X → Prop, LeastRealizes R (recordChoice q uc)) ↔
        ∀ a b c : X, q a = q b → q a = q c → a = b ∨ a = c ∨ b = c) := by
  have hidem := recordChoice_idem q uc hu
  have hleast : (∃ R : X → X → Prop, LeastRealizes R (recordChoice q uc)) ↔
      FibersAtMostTwo (recordChoice q uc) := by
    rw [exists_leastRealizes_iff]
    exact ⟨fun h => h.2, fun h => ⟨hidem, h⟩⟩
  refine ⟨?_, hleast.trans (fibersAtMostTwo_recordChoice_iff_three q uc hu)⟩
  rw [hleast, fibersAtMostTwo_recordChoice_iff_unchosen q uc hu]
  exact (recordChoice_conj_free_iff q uc hu).symm

/--
Proves: when `e = recordChoice q u` has a least realization, that realization is the relation
`RootStar e` that sends every unchosen state directly to its chosen state.
Scope: row 04-003. Trust: kernel-only.
-/
theorem leastRealization_eq_rootStar (q : X → Q) (uc : Set.range q → X)
    {R : X → X → Prop} (hR : LeastRealizes R (recordChoice q uc)) :
    R = RootStar (recordChoice q uc) :=
  (leastRealizes_iff.mp hR).2.2

/--
Proves: two distinct unchosen states with one record exclude a least realization of
`e = recordChoice q u`.
Scope: the counterexample that forces the bound of `leastRealization_iff_conjugation_free`;
row 04-003. Trust: kernel-only.
-/
theorem no_leastRealization_of_two_unchosen (q : X → Q) (uc : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (uc y) = y) {a b : X} (hab : q a = q b)
    (ha : a ≠ uc (Set.rangeFactorization q a)) (hb : b ≠ uc (Set.rangeFactorization q a))
    (hne : a ≠ b) :
    ¬ ∃ R : X → X → Prop, LeastRealizes R (recordChoice q uc) := by
  intro h
  have hfree := (leastRealization_iff_conjugation_free q uc hu).1.mp h
  have hf := (recordChoice_conj_free_iff q uc hu).mp hfree
  exact hne (hf a b hab ha hb)

/-! ## Non-vacuity -/

/-- The constant observer on `Bool` with the record choice `false`. -/
def boolChoice : Set.range (fun _ : Bool => ()) → Bool := fun _ => false

theorem boolChoice_section :
    ∀ y, Set.rangeFactorization (fun _ : Bool => ()) (boolChoice y) = y := by
  intro y
  exact Subtype.ext rfl

/-- One fiber of two states: a least realization exists. -/
theorem bool_leastRealization :
    ∃ R : Bool → Bool → Prop, LeastRealizes R (recordChoice (fun _ : Bool => ()) boolChoice) := by
  refine (leastRealization_iff_conjugation_free _ boolChoice boolChoice_section).2.mpr ?_
  intro a b c _ _
  cases a <;> cases b <;> cases c <;> simp

/-- The constant observer on `Fin 3` with the record choice `0`. -/
def fin3Choice : Set.range (fun _ : Fin 3 => ()) → Fin 3 := fun _ => 0

theorem fin3Choice_section :
    ∀ y, Set.rangeFactorization (fun _ : Fin 3 => ()) (fin3Choice y) = y := by
  intro y
  exact Subtype.ext rfl

/-- One fiber of three states: no least realization, and the conjugation action is not free. -/
theorem fin3_no_leastRealization :
    ¬ ∃ R : Fin 3 → Fin 3 → Prop,
      LeastRealizes R (recordChoice (fun _ : Fin 3 => ()) fin3Choice) :=
  no_leastRealization_of_two_unchosen (fun _ : Fin 3 => ()) fin3Choice fin3Choice_section
    (a := 1) (b := 2) rfl (by decide) (by decide) (by decide)

end OperatorKO7.Meta.BoundaryObserver.RecordChoiceRealization
