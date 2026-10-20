import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.BitDivision

set_option autoImplicit false

/-!
# Decidability of a self-referential recursor

Section 21 of the observation-principle manuscript. The definition of 2021, `O(R) = R` if `R` is
observed and `O(R) = O(R)` otherwise, is a step relation with a step from a state to itself. Read on
its own run it has an infinite sequence and its state observer determines only constant tests, so no
test that takes two values on the run, the counterpart `[n = 0]` of the observed test among them, is
decided from the state. The counted recursor
`O R s k = recΔ R s (numeral k)` of Theorem 8.1 replaces the self step by a pass that lowers the
counter by one and fixes the content. On the model states `T × ℕ` for any content type and any universe:

* the pass relation has no infinite sequence and no return, so it is well founded;
* the counter orients every pass, and every orienting measure separates `(R, 1)` from `(R, 0)`,
  so no orienting measure is determined by the content; the content is constant along a pass;
* the test "observed", `[k = 0]`, is determined by the counter and by no content observer, and the
  recursor returns `R` in one root step exactly at counter zero; a chain of passes from counter `k`
  to counter `0` has length `k`;
* over the passes `0, …, n` of one content the counter is a place coordinate of least size `n + 1`,
  and under the uniform law the content observer leaves `log (n + 1)` while the counter leaves
  nothing; for one pass that is one bit.


Relation: the kernel root relation `Step` at the recursor rules; `Pass` is a relation on the model
states, not a term relation.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
open OperatorKO7.Meta.BoundaryObserver.BitDivision

/-! ## The uncounted definition: a step from a state to itself -/

/-- The relation of the second clause of the 2021 definition read without a counter: one step, from
the state `t` to the state `t`. -/
def selfLoop {T : Type*} (t : T) : T → T → Prop := fun a b => a = t ∧ b = t

/-- The self step is a return in one step. -/
theorem selfLoop_return {T : Type*} (t : T) : Relation.TransGen (selfLoop t) t t :=
  Relation.TransGen.single ⟨rfl, rfl⟩

/-- Proposition 6.3 applied to the self step: the uncounted definition has an infinite sequence. -/
theorem selfLoop_infinite_seq {T : Type*} (t : T) :
    ∃ f : ℕ → T, ∀ n, selfLoop t (f n) (f (n + 1)) :=
  ⟨fun _ => t, fun _ => ⟨rfl, rfl⟩⟩

/-- The run of the uncounted definition: the state at every pass is `t`. -/
def constantRun {T : Type*} (t : T) : ℕ → T := fun _ => t

/-- Each pass of the run is a self step. -/
theorem constantRun_pass {T : Type*} (t : T) (n : ℕ) :
    selfLoop t (constantRun t n) (constantRun t (n + 1)) :=
  ⟨rfl, rfl⟩

/-- Non-vacuity: passes `0` and `1` of the run are a merged pair of the state observer. -/
theorem constantRun_merged_pair {T : Type*} (t : T) : IsMergedPair (constantRun t) 0 1 :=
  ⟨Nat.zero_ne_one, rfl⟩

/--
The state of the uncounted run separates no two passes.

Proves: a target on the passes that the state observer of the uncounted run determines is
constant.
Does not prove: anything about a run whose state changes.
Relation: none. Trust: kernel-only.
-/
theorem constantRun_determines_only_constants {T V : Type*} (t : T) (P : ℕ → V)
    (h : Determines (constantRun t) P) (n m : ℕ) : P n = P m :=
  h n m rfl

/-- The test `[n = 0]`, the counterpart on the run of the test `[k = 0]` of the counted model, is not
determined by the state of the uncounted run. -/
theorem constantRun_observed_not_determined {T : Type*} (t : T) :
    ¬ Determines (constantRun t) (fun n : ℕ => decide (n = 0)) := by
  intro h
  have h01 := constantRun_determines_only_constants t _ h 0 1
  simp at h01

/-! ## The counted recursor: the pass relation on the model states -/

/-- The content observer on counted states of any carrier and any universe. -/
abbrev content {T : Type*} : T × ℕ → T := fun p => p.1

/-- The count of passes left on any carrier. -/
abbrev counter {T : Type*} : T × ℕ → ℕ := fun p => p.2

/-- The observed test is true exactly at count zero. -/
abbrev observed {T : Type*} : T × ℕ → Bool := fun p => decide (p.2 = 0)

/-- One pass preserves content and lowers the count by one. -/
def Pass {T : Type*} : T × ℕ → T × ℕ → Prop :=
  fun x y => x.1 = y.1 ∧ x.2 = y.2 + 1

/-- Deciding one pass requires only decidable equality of the content. -/
instance decidablePass {T : Type*} [DecidableEq T] : DecidableRel (Pass (T := T)) :=
  fun x y => inferInstanceAs (Decidable (x.1 = y.1 ∧ x.2 = y.2 + 1))

/-- The step that raises the count by one and keeps the content is injective: a pass from a
positive count is the inverse of an injection and loses nothing. -/
theorem pass_step_injective {T : Type*} :
    Function.Injective (fun p : T × ℕ => (p.1, p.2 + 1)) := by
  intro a b h
  have h' : (a.1, a.2 + 1) = (b.1, b.2 + 1) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  exact Prod.ext h1 (Nat.add_right_cancel h2)

/-- Every state is reached by one pass from the state with the same content and one more count. -/
theorem pass_of_step {T : Type*} (p : T × ℕ) : Pass (p.1, p.2 + 1) p :=
  ⟨rfl, rfl⟩

/-- The saturating pass keeps the content and lowers the count by one in natural subtraction, so
that `(R, 0)` and `(R, 1)` both go to `(R, 0)`. -/
def satPass {T : Type*} : T × ℕ → T × ℕ := fun p => (p.1, p.2 - 1)

/-- The saturating pass, read as an observer of the counted states, merges two distinct states
exactly when they share the content and carry the counts `0` and `1`: its boundary is the set of
pairs `(R, 0), (R, 1)`. -/
theorem satPass_merged_iff {T : Type*} (p p' : T × ℕ) :
    satPass p = satPass p' ∧ p ≠ p' ↔
      p.1 = p'.1 ∧ ((p.2 = 0 ∧ p'.2 = 1) ∨ (p.2 = 1 ∧ p'.2 = 0)) := by
  obtain ⟨a, m⟩ := p
  obtain ⟨b, n⟩ := p'
  simp only [satPass, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hab, hmn⟩, hne⟩
    have hmn' : m ≠ n := fun h => hne ⟨hab, h⟩
    exact ⟨hab, by omega⟩
  · rintro ⟨hab, h⟩
    refine ⟨⟨hab, by omega⟩, fun h' => ?_⟩
    have := h'.2
    omega

/-- The counter falls at every pass. -/
theorem counter_decreases {T : Type*} {x y : T × ℕ} (h : Pass x y) : counter y < counter x := by
  show y.2 < x.2
  rw [h.2]
  exact Nat.lt_succ_self _

/-- Along a chain of passes the counter falls by one per pass. -/
theorem pass_chain_counter {T : Type*} (f : ℕ → T × ℕ) (n : ℕ) (h : ∀ i, i < n → Pass (f i) (f (i + 1))) :
    counter (f 0) = counter (f n) + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : counter (f 0) = counter (f n) + n := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hstep : counter (f n) = counter (f (n + 1)) + 1 := (h n (Nat.lt_succ_self n)).2
    omega

/--
Termination of the counted recursor by its counter.

Proves: the pass relation has no infinite sequence.
Does not prove: termination of the contextual relation on terms, which is the orientation paper's
theorem.
Relation: `Pass` on the model states. Trust: kernel-only.
-/
theorem pass_no_infinite_seq {T : Type*} :
    ¬ ∃ f : ℕ → T × ℕ, ∀ n, Pass (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  have h := pass_chain_counter f (counter (f 0) + 1) fun i _ => hf i
  omega

/-- Every nonempty finite chain of passes strictly decreases the counter. -/
theorem pass_transGen_counter {T : Type*} {x y : T × ℕ}
    (h : Relation.TransGen (Pass (T := T)) x y) : counter y < counter x := by
  induction h with
  | single hxy => exact counter_decreases hxy
  | tail _ hyz ih => exact lt_trans (counter_decreases hyz) ih

/-- No counted state returns to itself by a positive number of passes. -/
theorem pass_no_return {T : Type*} (x : T × ℕ) :
    ¬ Relation.TransGen (Pass (T := T)) x x := by
  intro h
  exact (Nat.lt_irrefl (counter x)) (pass_transGen_counter h)

/-- The pass relation is well founded on every content carrier. -/
theorem pass_wellFounded {T : Type*} :
    WellFounded (fun y x : T × ℕ => Pass x y) := by
  refine Subrelation.wf ?_ (measure (counter (T := T))).wf
  intro _ _ h
  exact counter_decreases h

/-! ## Deciders: the counter decides, the content does not -/

/-- The content is constant along a pass. -/
theorem content_constant_along_pass {T : Type*} {x y : T × ℕ} (h : Pass x y) : content x = content y :=
  h.1

/-- Every measure that reads only the content is constant along a pass. -/
theorem content_measure_constant {α : Type*} {T : Type*} (g : T → α) {x y : T × ℕ} (h : Pass x y) :
    g (content x) = g (content y) := by
  rw [content_constant_along_pass h]

/-- The counter orients every pass. -/
theorem counter_orients {T : Type*} (x y : T × ℕ) (h : Pass x y) : counter y < counter x :=
  counter_decreases h

/--
The orientation boundary in the model: orienting measures read the counter.

Proves: a measure that falls at every pass is determined by no content observer.
Does not prove: the classification of the orienting measures of the term relation by their
grammar, which is the orientation paper's theorem.
Relation: `Pass`. Trust: kernel-only.
-/
theorem orienting_measure_not_content_determined {T : Type*} [Nonempty T]
    (M : T × ℕ → ℕ) (hM : ∀ x y, Pass x y → M y < M x) :
    ¬ Determines content M := by
  intro h
  obtain ⟨t⟩ := ‹Nonempty T›
  have hlt : M (t, 0) < M (t, 1) := hM (t, 1) (t, 0) ⟨rfl, rfl⟩
  have heq : M (t, 1) = M (t, 0) := h (t, 1) (t, 0) rfl
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The counter is not determined by content on any inhabited carrier. -/
theorem counter_not_content_determined {T : Type*} [Nonempty T] :
    ¬ Determines (content (T := T)) (counter (T := T)) :=
  orienting_measure_not_content_determined counter counter_orients

/-- The observed test factors through the counter on every carrier. -/
theorem observed_determined_by_counter {T : Type*} :
    Determines (counter (T := T)) (observed (T := T)) := by
  intro x y h
  show decide (x.2 = 0) = decide (y.2 = 0)
  rw [show x.2 = y.2 from h]

/-- Equal observed values are exactly equal zero-status tests on the counter. -/
theorem observed_eq_iff_zero_iff {T : Type*} (R : T) (j k : ℕ) :
    observed (R, j) = observed (R, k) ↔ (j = 0 ↔ k = 0) := by
  cases j <;> cases k <;> simp [observed]

/-- The observed test is not determined by constant content on an inhabited carrier. -/
theorem observed_not_content_determined {T : Type*} [Nonempty T] :
    ¬ Determines (content (T := T)) (observed (T := T)) := by
  intro h
  obtain ⟨t⟩ := ‹Nonempty T›
  have h01 : observed (t, 0) = observed (t, 1) := h (t, 0) (t, 1) rfl
  simp [observed] at h01

/-- From counter `k` the passes reach counter `0`. -/
theorem passes_reach_zero {T : Type*} (R : T) (k : ℕ) :
    Relation.ReflTransGen (Pass (T := T)) (R, k) (R, 0) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    exact Relation.ReflTransGen.head
      (show Pass (R, k + 1) (R, k) from ⟨rfl, rfl⟩) ih

/-- A run of counted passes from `k` to zero has exactly `k` steps. -/
theorem run_length_eq_counter {T : Type*} (f : ℕ → T × ℕ) (n k : ℕ) (R : T)
    (h : ∀ i, i < n → Pass (f i) (f (i + 1)))
    (h0 : f 0 = (R, k)) (hn : f n = (R, 0)) : n = k := by
  have hc := pass_chain_counter f n h
  rw [h0, hn] at hc
  have hk : k = 0 + n := hc
  omega

/-! ## The cost of the coordinate -/

/-- Theorem 3.3(i) for the passes `0, …, n` of one content: a coordinate with `m` values completes
the constant record if and only if `n + 1 ≤ m`; the counter is such a coordinate at `m = n + 1`. -/
theorem counter_least_coordinate (n m : ℕ) :
    (∃ p : Fin (n + 1) → Fin m, Function.Injective (fun i => ((), p i))) ↔ n + 1 ≤ m := by
  rw [exists_place_coordinate_iff (fun _ : Fin (n + 1) => ()) m]
  have hpre : (fun _ : Fin (n + 1) => ()) ⁻¹' {()} = Set.univ :=
    Set.preimage_const_of_mem (Set.mem_singleton ())
  constructor
  · intro h
    have := (h ()).2
    rw [hpre, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  · intro h y
    cases y
    rw [hpre, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact ⟨Set.finite_univ, h⟩

/-- The counter is a place coordinate of the constant record over the passes. -/
theorem counter_is_coordinate (n : ℕ) :
    Function.Injective (fun i : Fin (n + 1) => ((), i)) := by
  intro a b h
  exact congrArg Prod.snd h

/-- The entropy an observer leaves under the uniform law, as Proposition 6.1(iii) writes it: the
right side of `condEntropy_uniform`. -/
noncomputable def leftEntropy {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q] (q : X → Q) :
    ℝ :=
  ∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
    Real.log ((Finset.univ.filter (fun x => q x = y)).card)

/-- `leftEntropy` is the conditional entropy of the uniform law given the record. -/
theorem leftEntropy_eq {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty X]
    (q : X → Q) :
    entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
        entropy (fun y : Q =>
          ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) =
      leftEntropy q :=
  condEntropy_uniform q

/--
Proposition 6.1(iii) for the passes: the content observer leaves the whole count.

Proves: under the uniform law on the passes `0, …, n` of one content, the constant record leaves
`log (n + 1)`.
Does not prove: the same for other laws on the passes.
Relation: none. Trust: kernel-only.
-/
theorem content_leaves_log (n : ℕ) :
    leftEntropy (fun _ : Fin (n + 1) => ()) = Real.log (n + 1) := by
  refine ((condEntropy_uniform_eq_log_card_iff (fun _ : Fin (n + 1) => ())).mpr
    (fun _ _ => rfl)).trans ?_
  simp

/-- The counter leaves nothing: it is injective on the passes. -/
theorem counter_leaves_zero (n : ℕ) : leftEntropy (fun i : Fin (n + 1) => i) = 0 :=
  (condEntropy_uniform_eq_zero_iff (fun i : Fin (n + 1) => i)).mpr (fun _ _ h => h)

/-- One pass, one bit: for the pair of passes `0, 1` the content observer leaves `log 2`, the bit of
Theorem 4.1(7). -/
theorem one_pass_one_bit : leftEntropy (fun _ : Fin 2 => ()) = Real.log 2 := by
  have h := content_leaves_log 1
  norm_num at h
  exact h

/-- A specific side encoder separates all passes precisely if that encoder is injective.
The size of its alphabet alone does not certify a given map. -/
theorem counter_side_encoder_injective_iff (n m : ℕ)
    (p : Fin (n + 1) → Fin m) :
    Function.Injective (fun i : Fin (n + 1) => ((), p i)) ↔
      Function.Injective p := by
  constructor
  · intro h i j hp
    exact h (congrArg (fun v : Fin m => ((), v)) hp)
  · intro h i j hij
    exact h (congrArg Prod.snd hij)

/-- A separating finite side encoder exists precisely when the output alphabet
contains at least n+1 values, with no claim that every encoder works. -/
theorem counter_side_encoder_exists_iff (n m : ℕ) :
    (∃ p : Fin (n + 1) → Fin m, Function.Injective p) ↔ n + 1 ≤ m := by
  constructor
  · rintro ⟨p, hp⟩
    exact (counter_least_coordinate n m).mp
      ⟨p, (counter_side_encoder_injective_iff n m p).2 hp⟩
  · intro h
    obtain ⟨p, hp⟩ := (counter_least_coordinate n m).mpr h
    exact ⟨p, (counter_side_encoder_injective_iff n m p).1 hp⟩

/-- Even an alphabet of the required size can be used by a noninjective side map. -/
theorem counter_side_encoder_size_not_sufficient_for_given_map :
    ∃ p : Fin 2 → Fin 2, 2 ≤ 2 ∧ ¬ Function.Injective p := by
  refine ⟨fun _ => 0, by omega, ?_⟩
  intro hp
  have h01 : (0 : Fin 2) = 1 :=
    hp (show (fun _ : Fin 2 => (0 : Fin 2)) 0 =
      (fun _ : Fin 2 => (0 : Fin 2)) 1 from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- The observed bit records only whether the pass counter is zero. -/
def zeroTestOnPasses (n : ℕ) : Fin (n + 1) → Bool :=
  fun i => decide (i.val = 0)

/-- The zero-test's true fiber consists only of the terminal count zero. -/
theorem zeroTest_true_fiber_card (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n + 1) =>
      zeroTestOnPasses n i = true)).card = 1 := by
  classical
  have hset :
      Finset.univ.filter (fun i : Fin (n + 1) =>
        zeroTestOnPasses n i = true) = {(0 : Fin (n + 1))} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      zeroTestOnPasses, decide_eq_true_eq]
    exact Fin.val_eq_zero_iff
  rw [hset]
  simp

/-- The zero-test's false fiber holds the n strictly positive counter values. -/
theorem zeroTest_false_fiber_card (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n + 1) =>
      zeroTestOnPasses n i = false)).card = n := by
  classical
  have hset :
      Finset.univ.filter (fun i : Fin (n + 1) =>
        zeroTestOnPasses n i = false) =
        Finset.univ.erase (0 : Fin (n + 1)) := by
    ext i
    by_cases hi : i.val = 0
    · have hzero : i = 0 := Fin.ext hi
      subst i
      simp [zeroTestOnPasses]
    · have hzero : i ≠ (0 : Fin (n + 1)) := by
        intro h
        exact hi (by simpa using congrArg Fin.val h)
      simp [zeroTestOnPasses, hzero]
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- A zero-test leaves the uncertainty over the n positive counts; it is not
the full counter. The units are natural logarithms, not base-two bits. -/
theorem zeroTest_conditional_entropy (n : ℕ) :
    leftEntropy (zeroTestOnPasses n) =
      ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) * Real.log n := by
  classical
  simp [leftEntropy, zeroTest_false_fiber_card,
    zeroTest_true_fiber_card, Fintype.card_fin]

/-- With one remaining pass, the zero-test determines the full two-value counter. -/
theorem zeroTest_one_pass_entropy_zero :
    leftEntropy (zeroTestOnPasses 1) = 0 := by
  rw [zeroTest_conditional_entropy]
  norm_num

/-- For two or more remaining passes, the zero-test leaves strictly positive
entropy even though the full counter leaves zero. -/
theorem zeroTest_many_passes_entropy_positive (n : ℕ) (hn : 2 ≤ n) :
    0 < leftEntropy (zeroTestOnPasses n) := by
  rw [zeroTest_conditional_entropy]
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hone : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  exact mul_pos (div_pos hpos hden) (Real.log_pos hone)

/-- The uniform full-counter entropy splits into the zero-test's binary
information and the positive-count information it leaves. An injective full
counter leaves zero entropy, whereas the zero-test generally does not. -/
theorem zeroTest_fullCounter_entropy_split (n : ℕ) (hn : 0 < n) :
    (leftEntropy (fun _ : Fin (n + 1) => ()) =
      Real.binEntropy (1 / ((n + 1 : ℕ) : ℝ)) +
        leftEntropy (zeroTestOnPasses n)) ∧
    leftEntropy (fun i : Fin (n + 1) => i) = 0 := by
  have hdecomp := log_eq_binEntropy_add (n + 1) (by omega : 2 ≤ n + 1)
  have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by
    push_cast
    ring
  rw [hcast] at hdecomp
  constructor
  · rw [content_leaves_log, zeroTest_conditional_entropy]
    simpa only [Nat.cast_add, Nat.cast_one] using hdecomp
  · exact counter_leaves_zero n

end OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
