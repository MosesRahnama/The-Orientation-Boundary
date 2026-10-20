import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.ContextClosed_SN_Full

set_option autoImplicit false

/-!
# Merges, records and steps without return

Section 6 of the observation-principle manuscript. An observer that merges two states has no
left inverse, and the least record that inverts it has the size of its largest class
(Proposition 6.1(i), (ii)). The composite of an observer with a choice of one state per record is
idempotent, and it is injective only when the observer is (Proposition 6.2). A relation without
an infinite sequence has no return, and a return gives an infinite sequence (Proposition 6.3);
the successor relation shows that the converse of the first statement fails, and on a finite
type the two properties coincide. The last three theorems apply the proposition to the calculus.

Proposition 6.1(iii) is `condEntropy_uniform_eq_log_card_iff` of `BitDivision.lean`.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M5.

Relation: `Step` at the root and `MetaSN_KO7.StepCtxFull` (a rule at any position) in the last
three theorems; arbitrary relations before them.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.BoundaryObserver.NoReturn

/-! ## Proposition 6.1: inverting an observer -/

/-- Proposition 6.1(i): a map from the records back to the states that undoes `q` exists if and
only if `q` is injective. -/
theorem left_inverse_iff_injective {X Q : Type*} (q : X → Q) :
    (∃ r : Set.range q → X, ∀ x, r (Set.rangeFactorization q x) = x) ↔ Function.Injective q := by
  constructor
  · rintro ⟨r, hr⟩ a b hab
    have h : Set.rangeFactorization q a = Set.rangeFactorization q b := Subtype.ext hab
    calc a = r (Set.rangeFactorization q a) := (hr a).symm
      _ = r (Set.rangeFactorization q b) := by rw [h]
      _ = b := hr b
  · intro hinj
    refine ⟨fun y => Classical.choose y.2, ?_⟩
    intro x
    exact hinj (Classical.choose_spec (Set.rangeFactorization q x).2)

/--
Proposition 6.1(ii).

Proves: a side map `s` with `n` values such that the record `(q, s)` can be inverted exists if
and only if every class of `q` is finite with at most `n` elements.
Does not prove: a bound on the bits of `s`; that count is Proposition 6.1(iii).
Relation: none. Trust: kernel-only, with `Classical.choice`.
-/
theorem exists_inverting_record_iff {X Q : Type*} (q : X → Q) (n : ℕ) :
    (∃ s : X → Fin n, ∃ r : Set.range (fun x => (q x, s x)) → X,
        ∀ x, r (Set.rangeFactorization (fun x => (q x, s x)) x) = x) ↔
      ∀ y : Q, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n := by
  rw [← PlaceCoordinates.exists_place_coordinate_iff]
  exact exists_congr fun s => left_inverse_iff_injective (fun x => (q x, s x))

/-! ## Proposition 6.2: observing twice -/

/-- The composite of `q` with a choice `u` of one state for each record. -/
def recordChoice {X Q : Type*} (q : X → Q) (u : Set.range q → X) : X → X :=
  fun x => u (Set.rangeFactorization q x)

/-- Proposition 6.2: when `u` chooses a state with the given record, the composite is idempotent,
keeps every record, and is injective if and only if `q` is. -/
theorem recordChoice_idempotent {X Q : Type*} (q : X → Q) (u : Set.range q → X)
    (hu : ∀ y, Set.rangeFactorization q (u y) = y) :
    (∀ x, recordChoice q u (recordChoice q u x) = recordChoice q u x) ∧
      (∀ x, q (recordChoice q u x) = q x) ∧
      (Function.Injective (recordChoice q u) ↔ Function.Injective q) := by
  have hq : ∀ x, q (recordChoice q u x) = q x := by
    intro x
    exact congrArg Subtype.val (hu (Set.rangeFactorization q x))
  refine ⟨?_, hq, ?_⟩
  · intro x
    show u (Set.rangeFactorization q (u (Set.rangeFactorization q x))) =
      u (Set.rangeFactorization q x)
    rw [hu]
  · constructor
    · intro h a b hab
      apply h
      have hf : Set.rangeFactorization q a = Set.rangeFactorization q b := Subtype.ext hab
      show u (Set.rangeFactorization q a) = u (Set.rangeFactorization q b)
      rw [hf]
    · intro h a b hab
      apply h
      calc q a = q (recordChoice q u a) := (hq a).symm
        _ = q (recordChoice q u b) := by rw [hab]
        _ = q b := hq b

/-- Non-vacuity of the hypothesis of `recordChoice_idempotent`: every observer has a choice of
one state for each record. -/
theorem exists_record_section {X Q : Type*} (q : X → Q) :
    ∃ u : Set.range q → X, ∀ y, Set.rangeFactorization q (u y) = y :=
  ⟨fun y => Classical.choose y.2, fun y => Subtype.ext (Classical.choose_spec y.2)⟩

/-- Proposition 6.2, last sentence: an idempotent map that is injective is the identity. -/
theorem injective_idempotent_eq_id {X : Type*} (e : X → X) (hid : ∀ x, e (e x) = e x)
    (hinj : Function.Injective e) : e = id :=
  funext fun x => hinj (hid x)

/-- The non-disturbing instrument of `q` reads the record `q x` and leaves the state `x` as it
was. Its retained output `(q x, x)` is injective for every observer `q`: an instrument that keeps
the state merges no two states, whatever the record map merges. -/
theorem nondisturbing_joint_injective {X Q : Type*} (q : X → Q) :
    Function.Injective (fun x => (q x, x)) :=
  fun _ _ h => congrArg Prod.snd h

/-- The instrument of `q` that moves the state to the chosen state `recordChoice q u x` of its
record retains the pair `(q x, recordChoice q u x)`. Two states give the same retained pair if and
only if `q` gives them the same record: the instrument merges the pairs that `q` merges and no
others. The equivalence holds for every choice `u`, in particular for every `u` with the section
hypothesis of `recordChoice_idempotent`. -/
theorem recordChoice_joint_eq_iff {X Q : Type*} (q : X → Q) (u : Set.range q → X) (x x' : X) :
    (q x, recordChoice q u x) = (q x', recordChoice q u x') ↔ q x = q x' := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    have hf : Set.rangeFactorization q x = Set.rangeFactorization q x' := Subtype.ext h
    have hc : recordChoice q u x = recordChoice q u x' := by
      show u (Set.rangeFactorization q x) = u (Set.rangeFactorization q x')
      rw [hf]
    rw [h, hc]

/-! ## Proposition 6.3: termination excludes return -/

/--
Proposition 6.3, second statement.

Proves: a return `t →⁺ t` of a relation gives an infinite sequence of steps of that relation.
Does not prove: that the sequence is periodic.
Relation: an arbitrary relation `r`; closure: transitive. Trust: kernel-only, with
`Classical.choice` for the choice of a successor.
-/
theorem infinite_seq_of_return {T : Type*} (r : T → T → Prop) {t : T}
    (h : Relation.TransGen r t t) : ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1)) := by
  classical
  have hstep : ∀ a : {a : T // Relation.ReflTransGen r a t},
      ∃ b : {a : T // Relation.ReflTransGen r a t}, r a.1 b.1 := by
    rintro ⟨a, ha⟩
    rcases Relation.ReflTransGen.cases_head ha with hat | ⟨c, hac, hct⟩
    · obtain ⟨b, hab, hbt⟩ := Relation.TransGen.head'_iff.mp h
      exact ⟨⟨b, hbt⟩, hat.symm ▸ hab⟩
    · exact ⟨⟨c, hct⟩, hac⟩
  choose next hnext using hstep
  refine ⟨fun n => (next^[n] ⟨t, Relation.ReflTransGen.refl⟩).1, fun n => ?_⟩
  show r (next^[n] ⟨t, Relation.ReflTransGen.refl⟩).1
    (next^[n + 1] ⟨t, Relation.ReflTransGen.refl⟩).1
  rw [Function.iterate_succ_apply']
  exact hnext _

/-- Proposition 6.3, first statement: a relation without an infinite sequence has no return. -/
theorem no_return_of_no_infinite_seq {T : Type*} (r : T → T → Prop)
    (h : ¬ ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1))) (t : T) : ¬ Relation.TransGen r t t :=
  fun ht => h (infinite_seq_of_return r ht)

/-- Proposition 6.3, "in particular": in a relation without an infinite sequence, no sequence of
later steps leads from the result of a step back to its source. -/
theorem step_not_undone_of_no_infinite_seq {T : Type*} (r : T → T → Prop)
    (h : ¬ ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1))) {a b : T} (hab : r a b) :
    ¬ Relation.ReflTransGen r b a :=
  fun hba => no_return_of_no_infinite_seq r h a (Relation.TransGen.head' hab hba)

/-- The remark after Proposition 6.3: the successor relation on the natural numbers has no
return and has an infinite sequence, so the absence of return does not give termination. -/
theorem succ_no_return_and_infinite :
    (∀ n : ℕ, ¬ Relation.TransGen (fun a b : ℕ => b = a + 1) n n) ∧
      ∃ f : ℕ → ℕ, ∀ n, f (n + 1) = f n + 1 := by
  refine ⟨?_, ⟨id, fun n => rfl⟩⟩
  have hlt : ∀ a b : ℕ, Relation.TransGen (fun a b : ℕ => b = a + 1) a b → a < b := by
    intro a b h
    induction h with
    | single h => omega
    | tail _ h ih => omega
  intro n hn
  exact lt_irrefl n (hlt n n hn)

/-- The remark after Proposition 6.3: on a finite type a relation has a return if and only if it
has an infinite sequence. -/
theorem return_iff_infinite_seq_of_finite {T : Type*} [Finite T] (r : T → T → Prop) :
    (∃ t, Relation.TransGen r t t) ↔ ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1)) := by
  constructor
  · rintro ⟨t, ht⟩
    exact infinite_seq_of_return r ht
  · rintro ⟨f, hf⟩
    have hchain : ∀ i k : ℕ, Relation.TransGen r (f i) (f (i + k + 1)) := by
      intro i k
      induction k with
      | zero => exact Relation.TransGen.single (hf i)
      | succ k ih => exact Relation.TransGen.tail ih (hf (i + k + 1))
    obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
      have hc := hchain i k
      rw [← hk, ← hfij] at hc
      exact ⟨f i, hc⟩
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
      have hc := hchain j k
      rw [← hk, hfij] at hc
      exact ⟨f j, hc⟩

/-! ## The calculus -/

/--
Termination of rewriting inside terms, in sequence form.

Proves: no infinite sequence of steps of `StepCtxFull`, the eight rules applied at any position.
Does not prove: a bound on the length of a sequence beyond the measure `W` of its first term.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, one step; strategy: full.
Trust: kernel-only. The measure is `PolyInterpretation.W` with `W_orients_stepCtxFull`.
-/
theorem stepCtxFull_no_infinite_seq :
    ¬ ∃ f : ℕ → Trace, ∀ n, MetaSN_KO7.StepCtxFull (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  have hW : ∀ n, PolyInterpretation.W (f n) + n ≤ PolyInterpretation.W (f 0) := by
    intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
      have hdec := MetaSN_KO7.W_orients_stepCtxFull (hf n)
      omega
  have hbad := hW (PolyInterpretation.W (f 0) + 1)
  omega

/-- Section 7.5: a step of `StepCtxFull` is not undone by any sequence of later steps.
Relation: `MetaSN_KO7.StepCtxFull`; closure: context, reflexive-transitive on the way back. -/
theorem stepCtxFull_not_undone {a b : Trace} (h : MetaSN_KO7.StepCtxFull a b) :
    ¬ Relation.ReflTransGen MetaSN_KO7.StepCtxFull b a :=
  step_not_undone_of_no_infinite_seq _ stepCtxFull_no_infinite_seq h

/-- Section 7.5: a step at the root is not undone by any sequence of later root steps.
Relation: `Step`; closure: root, reflexive-transitive on the way back. -/
theorem step_not_undone {a b : Trace} (h : Step a b) : ¬ Relation.ReflTransGen Step b a :=
  fun hba => stepCtxFull_not_undone (MetaSN_KO7.StepCtxFull.root h)
    (hba.mono fun _ _ hs => MetaSN_KO7.StepCtxFull.root hs)

end OperatorKO7.Meta.BoundaryObserver.NoReturn
