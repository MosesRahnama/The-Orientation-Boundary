import OperatorKO7.Meta.BoundaryObserver.MergedPair
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

/-!
# Least observer under allowed actions

For an observation `q` and total action functions, `futureRecord` records `q` after every finite action word; `FutureEq` equates states with identical records. The quotient carries read and update operations, and every surjective sufficient updateable monitor maps uniquely to it. Adaptive experiments have the same separating power as finite words.

On a connected state space, a continuous map to a discrete set cannot separate a pair already merged by `q`. For finite candidates, at most `n-1` independent equality tests identify an input; each test starts from a fresh copy, and word length is unrestricted. For a finite state set, a finite bank reproduces the kernel of the complete behavioral record.

Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation

/-- Execute a word of permitted actions, in the order in which they are listed. -/
def run {X A : Type*} (step : A → X → X) : List A → X → X
  | [], x => x
  | a :: w, x => run step w (step a x)

/-- The record of every finite permitted experiment, including the empty experiment. -/
def futureRecord {X A Q : Type*} (q : X → Q) (step : A → X → X) (x : X) : List A → Q :=
  fun w => q (run step w x)

/-- States are indistinguishable if every permitted finite experiment gives the same record. -/
def FutureEq {X A Q : Type*} (q : X → Q) (step : A → X → X) (x y : X) : Prop :=
  futureRecord q step x = futureRecord q step y

/-- Composition of experiments. -/
theorem run_append {X A : Type*} (step : A → X → X) (u v : List A) (x : X) :
    run step (u ++ v) x = run step v (run step u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (step a x)

/-- The empty experiment contains the original observation. -/
theorem futureEq_observation {X A Q : Type*} {q : X → Q} {step : A → X → X}
    {x y : X} (h : FutureEq q step x y) : q x = q y :=
  congrFun h []

/-- Indistinguishability survives every permitted action. -/
theorem futureEq_step {X A Q : Type*} {q : X → Q} {step : A → X → X}
    {x y : X} (h : FutureEq q step x y) (a : A) :
    FutureEq q step (step a x) (step a y) := by
  funext w
  exact congrFun h (a :: w)

/-- Any relation that preserves the record and is stable under each action preserves all
finite experiments. No equivalence hypothesis on this relation is needed. -/
theorem relation_le_futureEq {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (R : X → X → Prop) (hread : ∀ x y, R x y → q x = q y)
    (hstep : ∀ a x y, R x y → R (step a x) (step a y)) :
    ∀ x y, R x y → FutureEq q step x y := by
  intro x y hxy
  funext w
  change q (run step w x) = q (run step w y)
  have hrun : ∀ x y, R x y → R (run step w x) (run step w y) := by
    induction w with
    | nil => exact fun _ _ h => h
    | cons a w ih => exact fun x y h => ih _ _ (hstep a x y h)
  exact hread _ _ (hrun x y hxy)

/-- The kernel of all experiments is the greatest stable relation within the current-record
kernel, and not merely one sufficient relation. -/
theorem futureEq_greatest {X A Q : Type*} (q : X → Q) (step : A → X → X) :
    (∀ x y, FutureEq q step x y → q x = q y) ∧
      (∀ a x y, FutureEq q step x y → FutureEq q step (step a x) (step a y)) ∧
      ∀ R : X → X → Prop, (∀ x y, R x y → q x = q y) →
        (∀ a x y, R x y → R (step a x) (step a y)) →
          ∀ x y, R x y → FutureEq q step x y :=
  ⟨fun _ _ h => futureEq_observation h, fun a _ _ h => futureEq_step h a,
    relation_le_futureEq q step⟩

/-- The equivalence relation of permitted finite experiments. -/
def futureSetoid {X A Q : Type*} (q : X → Q) (step : A → X → X) : Setoid X where
  r := FutureEq q step
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- The least updateable state description identifies exactly experimentally indistinguishable
states. -/
abbrev MinimalState {X A Q : Type*} (q : X → Q) (step : A → X → X) :=
  Quotient (futureSetoid q step)

/-- The map from an original state to its least updateable description. -/
def minimalRecord {X A Q : Type*} (q : X → Q) (step : A → X → X) (x : X) :
    MinimalState q step := Quotient.mk (futureSetoid q step) x

/-- Read the current observation from the least updateable description. -/
def minimalRead {X A Q : Type*} (q : X → Q) (step : A → X → X) : MinimalState q step → Q :=
  Quotient.lift q (fun _ _ h => futureEq_observation h)

/-- Apply an allowed action directly to the least updateable description. -/
def minimalStep {X A Q : Type*} (q : X → Q) (step : A → X → X) (a : A) :
    MinimalState q step → MinimalState q step :=
  Quotient.map (step a) (fun _ _ h => futureEq_step h a)

/-- The least observer has the exact experimental kernel. -/
theorem minimalRecord_eq_iff {X A Q : Type*} (q : X → Q) (step : A → X → X) (x y : X) :
    minimalRecord q step x = minimalRecord q step y ↔ FutureEq q step x y :=
  Quotient.eq

/-- Reading the least record agrees with reading the original state. -/
theorem minimalRead_record {X A Q : Type*} (q : X → Q) (step : A → X → X) (x : X) :
    minimalRead q step (minimalRecord q step x) = q x := rfl

/-- Updating the least record agrees with updating the original state. -/
theorem minimalStep_record {X A Q : Type*} (q : X → Q) (step : A → X → X) (a : A) (x : X) :
    minimalStep q step a (minimalRecord q step x) = minimalRecord q step (step a x) := rfl

/-- Every sufficient, updateable monitor distinguishes all distinctions of the least observer. -/
theorem monitor_kernel_le_futureEq {X A Q M : Type*} (q : X → Q) (step : A → X → X)
    (m : X → M) (hread : ∀ x y, m x = m y → q x = q y)
    (hstep : ∀ a x y, m x = m y → m (step a x) = m (step a y)) :
    ∀ x y, m x = m y → FutureEq q step x y :=
  relation_le_futureEq q step (fun x y => m x = m y) hread hstep

/-- Every surjective sufficient, updateable monitor has one and only one map to the least
observer commuting with the original state map. Surjectivity means that only realized records
are counted. -/
theorem minimal_observer_universal {X A Q M : Type*} (q : X → Q) (step : A → X → X)
    (m : X → M) (hm : Function.Surjective m)
    (hread : ∀ x y, m x = m y → q x = q y)
    (hstep : ∀ a x y, m x = m y → m (step a x) = m (step a y)) :
    ∃! f : M → MinimalState q step, ∀ x, f (m x) = minimalRecord q step x := by
  classical
  let f : M → MinimalState q step := fun r => minimalRecord q step (Classical.choose (hm r))
  have hf : ∀ x, f (m x) = minimalRecord q step x := by
    intro x
    exact Quotient.sound (monitor_kernel_le_futureEq q step m hread hstep _ _
      (Classical.choose_spec (hm (m x))))
  refine ⟨f, hf, ?_⟩
  intro g hg
  funext r
  obtain ⟨x, rfl⟩ := hm r
  exact (hg x).trans (hf x).symm

/-- The map supplied by the universal property is surjective. -/
theorem minimal_factor_surjective {X A Q M : Type*} (q : X → Q) (step : A → X → X)
    (m : X → M) (f : M → MinimalState q step)
    (hf : ∀ x, f (m x) = minimalRecord q step x) : Function.Surjective f := by
  intro z
  induction z using Quotient.inductionOn with
  | h x => exact ⟨m x, hf x⟩

/-- If the original observation already updates without ambiguity, experiments add no new
state distinctions. -/
theorem futureEq_eq_current_of_compatible {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (hstep : ∀ a x y, q x = q y → q (step a x) = q (step a y)) (x y : X) :
    FutureEq q step x y ↔ q x = q y :=
  ⟨futureEq_observation, relation_le_futureEq q step (fun x y => q x = q y)
    (fun _ _ h => h) hstep x y⟩

/-- A connected carrier has no continuous discrete repair of any merged pair. This is an
admissibility obstruction, even when unrestricted labels separate the pair. -/
theorem no_continuous_discrete_repair {X Q S : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [TopologicalSpace S] [DiscreteTopology S]
    (q : X → Q) {x y : X} (hne : x ≠ y) (hq : q x = q y)
    (s : X → S) (hs : Continuous s) : ¬ Function.Injective (fun z => (q z, s z)) := by
  intro hinj
  have he : s x = s y := PreconnectedSpace.constant inferInstance hs
  exact hne (hinj (Prod.ext hq he))

/-- The square and the sign jointly identify a real number. The side alphabet has two values. -/
theorem square_sign_injective : Function.Injective
    (fun x : ℝ => (x ^ 2, decide (0 ≤ x))) := by
  intro x y h
  have hsq : x ^ 2 = y ^ 2 := congrArg Prod.fst h
  have hsign : (0 ≤ x ↔ 0 ≤ y) := by
    have hb : decide (0 ≤ x) = decide (0 ≤ y) := congrArg Prod.snd h
    constructor
    · intro hx
      exact of_decide_eq_true (hb.symm.trans (decide_eq_true hx))
    · intro hy
      exact of_decide_eq_true (hb.trans (decide_eq_true hy))
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hxy | hxy
  · exact hxy
  · by_cases hx : 0 ≤ x
    · have hy := hsign.mp hx
      linarith
    · have hy : ¬ 0 ≤ y := fun hy => hx (hsign.mpr hy)
      linarith

/-- No continuous discrete side label can do what the unrestricted sign label does. -/
theorem square_no_continuous_discrete_label {S : Type*} [TopologicalSpace S] [DiscreteTopology S]
    (s : ℝ → S) (hs : Continuous s) : ¬ Function.Injective (fun x : ℝ => (x ^ 2, s x)) :=
  no_continuous_discrete_repair (fun x : ℝ => x ^ 2) (x := 1) (y := -1)
    (by norm_num) (by norm_num) s hs

/-! ## Adaptive observation events -/

/-- A well-founded adaptive experiment either reports a function of the current observation,
or chooses an allowed action and a continuation from that observation. -/
inductive Experiment (A Q V : Type*) where
  | finish : (Q → V) → Experiment A Q V
  | next : (Q → A) → (Q → Experiment A Q V) → Experiment A Q V

/-- Run an adaptive experiment on the object state. -/
def evaluate {X A Q V : Type*} (q : X → Q) (step : A → X → X) :
    Experiment A Q V → X → V
  | .finish out, x => out (q x)
  | .next choose after, x =>
      evaluate q step (after (q x)) (step (choose (q x)) x)

/-- Adaptive choices cannot distinguish states that every permitted word identifies. -/
theorem evaluate_eq_of_futureEq {X A Q V : Type*} (q : X → Q) (step : A → X → X)
    (e : Experiment A Q V) : ∀ x y, FutureEq q step x y →
      evaluate q step e x = evaluate q step e y := by
  induction e with
  | finish out =>
    intro x y h
    exact congrArg out (futureEq_observation h)
  | next choose after ih =>
    intro x y h
    have hq := futureEq_observation h
    dsimp only [evaluate]
    rw [hq]
    exact ih (q y) _ _ (futureEq_step h (choose (q y)))

/-- A fixed action word is also an adaptive experiment with constant choices. -/
def wordExperiment {A Q : Type*} : List A → Experiment A Q Q
  | [] => .finish id
  | a :: w => .next (fun _ => a) (fun _ => wordExperiment w)

/-- The adaptive evaluator agrees with the action-word semantics on fixed experiments. -/
theorem evaluate_word {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (w : List A) (x : X) : evaluate q step (wordExperiment w) x = q (run step w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact ih (step a x)

/-- Fixed-word indistinguishability and adaptive indistinguishability coincide exactly.
This does not give a bound on experiment length or on the computation used to choose an action. -/
theorem futureEq_iff_all_adaptive {X A Q : Type*} (q : X → Q) (step : A → X → X) (x y : X) :
    FutureEq q step x y ↔
      ∀ e : Experiment A Q Q, evaluate q step e x = evaluate q step e y := by
  constructor
  · intro h e
    exact evaluate_eq_of_futureEq q step e x y h
  · intro h
    funext w
    simpa only [evaluate_word] using h (wordExperiment w)

/-- Experimental distinction has a finite witnessing word. -/
theorem not_futureEq_iff_word {X A Q : Type*} (q : X → Q) (step : A → X → X) (x y : X) :
    ¬ FutureEq q step x y ↔ ∃ w : List A, q (run step w x) ≠ q (run step w y) := by
  classical
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (funext hn)
  · rintro ⟨w, hw⟩ h
    exact hw (congrFun h w)

/-- If an adaptive event separates two states with the same current record, some nonempty
allowed experiment already witnesses a distinction outside the current-record kernel. -/
theorem resolving_event_requires_new_distinction {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (e : Experiment A Q V) {x y : X}
    (hcurrent : q x = q y) (hnew : evaluate q step e x ≠ evaluate q step e y) :
    ∃ w : List A, w ≠ [] ∧ q (run step w x) ≠ q (run step w y) := by
  have hn : ¬ FutureEq q step x y :=
    fun h => hnew (evaluate_eq_of_futureEq q step e x y h)
  obtain ⟨w, hw⟩ := (not_futureEq_iff_word q step x y).mp hn
  refine ⟨w, ?_, hw⟩
  intro he
  subst w
  exact hw hcurrent

/-- A realized monitor-to-minimal-observer map automatically preserves actions whenever the
monitor itself faithfully updates the object state. -/
theorem minimal_factor_commutes {X A Q M : Type*} (q : X → Q) (step : A → X → X)
    (m : X → M) (hm : Function.Surjective m) (update : A → M → M)
    (hupdate : ∀ a x, update a (m x) = m (step a x))
    (f : M → MinimalState q step) (hf : ∀ x, f (m x) = minimalRecord q step x)
    (a : A) (r : M) : f (update a r) = minimalStep q step a (f r) := by
  obtain ⟨x, rfl⟩ := hm r
  rw [hupdate, hf, hf, minimalStep_record]

/-- With no action that separates a current observation class, even an adaptive observer cannot
produce a new distinction between states in that class. -/
theorem no_new_distinction_of_closed_record {X A Q V : Type*}
    (q : X → Q) (step : A → X → X)
    (hstep : ∀ a x y, q x = q y → q (step a x) = q (step a y))
    (e : Experiment A Q V) {x y : X} (hq : q x = q y) :
    evaluate q step e x = evaluate q step e y :=
  evaluate_eq_of_futureEq q step e x y
    ((futureEq_eq_current_of_compatible q step hstep x y).mpr hq)

/-- A distinguishing action word contains a precise event at which previously equal records
become different. The prefix and remaining suffix are returned as witnesses. -/
theorem distinguishing_word_has_boundary_event {X A Q : Type*}
    (q : X → Q) (step : A → X → X) (w : List A) :
    ∀ x y, q x = q y → q (run step w x) ≠ q (run step w y) →
      ∃ (before : List A) (a : A) (after : List A),
        w = before ++ a :: after ∧
        q (run step before x) = q (run step before y) ∧
        q (step a (run step before x)) ≠ q (step a (run step before y)) := by
  classical
  induction w with
  | nil =>
    intro x y hq hn
    exact False.elim (hn hq)
  | cons a w ih =>
    intro x y hq hn
    by_cases he : q (step a x) = q (step a y)
    · obtain ⟨before, b, after, hw, hbefore, hcross⟩ := ih _ _ he hn
      exact ⟨a :: before, b, after, by simp [hw], hbefore, hcross⟩
    · exact ⟨[], a, w, rfl, hq, he⟩

/-- Every adaptive resolution of a current merged pair has an actual reachable separating
step. This is the event-level necessary condition for a boundary mechanism. -/
theorem adaptive_resolution_has_boundary_event {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (e : Experiment A Q V) {x y : X}
    (hcurrent : q x = q y) (hnew : evaluate q step e x ≠ evaluate q step e y) :
    ∃ (before : List A) (a : A), q (run step before x) = q (run step before y) ∧
      q (step a (run step before x)) ≠ q (step a (run step before y)) := by
  obtain ⟨w, _, hw⟩ := resolving_event_requires_new_distinction q step e hcurrent hnew
  obtain ⟨before, a, _, _, hb, ha⟩ :=
    distinguishing_word_has_boundary_event q step w x y hcurrent hw
  exact ⟨before, a, hb, ha⟩

/-- A target not determined by a record has no adaptive solver built entirely from operations
that preserve equality of that record. -/
theorem no_adaptive_solver_of_collision {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (target : X → V)
    (hstep : ∀ a x y, q x = q y → q (step a x) = q (step a y))
    {x y : X} (hq : q x = q y) (ht : target x ≠ target y) :
    ¬ ∃ e : Experiment A Q V, ∀ z, evaluate q step e z = target z := by
  rintro ⟨e, he⟩
  have h := no_new_distinction_of_closed_record q step hstep e hq
  rw [he, he] at h
  exact ht h

/-- Three initial alternatives and two absorbing report states. -/
abbrev DestructiveState := Fin 3 ⊕ Bool

/-- The initial alternatives have no individual label; an executed test leaves its Boolean
answer visible. -/
def destructiveRead : DestructiveState → Option Bool
  | .inl _ => none
  | .inr b => some b

/-- A test asks whether the initial alternative equals its index, then destroys the initial
state. Further tests cannot recover that state. -/
def destructiveStep (a : Fin 3) : DestructiveState → DestructiveState
  | .inl i => .inr (decide (i = a))
  | .inr b => .inr b

/-- Every pair of distinct initial states has a distinguishing permitted experiment. -/
theorem destructive_initials_distinguishable {i j : Fin 3} (hij : i ≠ j) :
    ¬ FutureEq destructiveRead destructiveStep (.inl i) (.inl j) := by
  apply (not_futureEq_iff_word destructiveRead destructiveStep (.inl i) (.inl j)).mpr
  refine ⟨[i], ?_⟩
  simp [run, destructiveStep, destructiveRead, hij.symm]

/-- Each test index omits two distinct initial alternatives. -/
theorem two_other_indices (a : Fin 3) :
    ∃ i j : Fin 3, i ≠ a ∧ j ≠ a ∧ i ≠ j := by
  fin_cases a
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- When the initial records agree and each first action makes some distinct alternatives
indistinguishable under all later experiments, no adaptive single run identifies every input.
The state and action types need not be finite. -/
theorem no_identifier_of_first_step_collision {X A Q I : Type*} [Nontrivial I]
    (q : X → Q) (step : A → X → X) (initial : I → X) (r : Q)
    (hread : ∀ i, q (initial i) = r)
    (hmerge : ∀ a, ∃ i j, i ≠ j ∧
      FutureEq q step (step a (initial i)) (step a (initial j))) :
    ¬ ∃ e : Experiment A Q I, ∀ i, evaluate q step e (initial i) = i := by
  rintro ⟨e, he⟩
  cases e with
  | finish out =>
    obtain ⟨i, j, hij⟩ := exists_pair_ne I
    have hi : out r = i := by simpa only [evaluate, hread] using he i
    have hj : out r = j := by simpa only [evaluate, hread] using he j
    exact hij (hi.symm.trans hj)
  | next choose after =>
    obtain ⟨i, j, hij, hfuture⟩ := hmerge (choose r)
    have h := evaluate_eq_of_futureEq q step (after r) _ _ hfuture
    have hi : evaluate q step (after r) (step (choose r) (initial i)) = i := by
      simpa only [evaluate, hread] using he i
    have hj : evaluate q step (after r) (step (choose r) (initial j)) = j := by
      simpa only [evaluate, hread] using he j
    exact hij (hi.symm.trans (h.trans hj))

/-- No single adaptive experiment identifies all three initial states, even though each pair
can be separated. The first test merges the two alternatives it did not select. -/
theorem destructive_no_single_run_identifier :
    ¬ ∃ e : Experiment (Fin 3) (Option Bool) (Fin 3),
      ∀ i : Fin 3, evaluate destructiveRead destructiveStep e (.inl i) = i := by
  apply no_identifier_of_first_step_collision destructiveRead destructiveStep
    Sum.inl none (fun _ => rfl)
  intro a
  obtain ⟨i, j, hi, hj, hij⟩ := two_other_indices a
  refine ⟨i, j, hij, ?_⟩
  simp only [destructiveStep, decide_eq_false hi, decide_eq_false hj]
  rfl

/-- The results of tests performed on independent copies of the same initial alternative. -/
def trialRecord (i : Fin 3) (a : Fin 3) : Option Bool :=
  destructiveRead (run destructiveStep [a] (.inl i))

/-- Independent trials supply the information that one destructive run cannot retain. -/
theorem independent_trials_identify : Function.Injective trialRecord := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  have hji : j ≠ i := fun hji => hij hji.symm
  simp [trialRecord, destructiveRead, destructiveStep, run, hji] at hh

/-- The minimal behavioral observer distinguishes all initial states in this example, despite
being unattainable by a single adaptive run. -/
theorem destructive_minimal_record_injective : Function.Injective
    (fun i : Fin 3 => minimalRecord destructiveRead destructiveStep (.inl i)) := by
  intro i j h
  by_contra hij
  exact destructive_initials_distinguishable hij
    ((minimalRecord_eq_iff destructiveRead destructiveStep (.inl i) (.inl j)).mp h)

/-- The finite action sequence actually selected by an adaptive experiment on one input. -/
def executedTrace {X A Q V : Type*} (q : X → Q) (step : A → X → X) :
    Experiment A Q V → X → List A
  | .finish _, _ => []
  | .next choose after, x =>
      choose (q x) :: executedTrace q step (after (q x)) (step (choose (q x)) x)

/-- An adaptive resolution has a separating event along the executions it actually performs
on the two inputs. Both executions share every action through that event. The remaining
suffixes may differ after the new distinction is read. -/
theorem actual_resolution_has_boundary_event {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (e : Experiment A Q V) :
    ∀ x y, q x = q y → evaluate q step e x ≠ evaluate q step e y →
      ∃ (before : List A) (a : A) (afterX afterY : List A),
        executedTrace q step e x = before ++ a :: afterX ∧
        executedTrace q step e y = before ++ a :: afterY ∧
        q (run step before x) = q (run step before y) ∧
        q (step a (run step before x)) ≠ q (step a (run step before y)) := by
  classical
  induction e with
  | finish out =>
    intro x y hq hnew
    exact False.elim (hnew (congrArg out hq))
  | next choose after ih =>
    intro x y hq hnew
    have hout : evaluate q step (after (q x)) (step (choose (q x)) x) ≠
        evaluate q step (after (q x)) (step (choose (q x)) y) := by
      simpa only [evaluate, ← hq] using hnew
    by_cases hs : q (step (choose (q x)) x) = q (step (choose (q x)) y)
    · obtain ⟨before, a, afterX, afterY, hx, hy, hb, ha⟩ :=
        ih (q x) _ _ hs hout
      refine ⟨choose (q x) :: before, a, afterX, afterY, ?_, ?_, hb, ha⟩
      · simpa only [executedTrace, List.cons_append] using congrArg (List.cons (choose (q x))) hx
      · simpa only [executedTrace, ← hq, List.cons_append] using
          congrArg (List.cons (choose (q x))) hy
    · refine ⟨[], choose (q x),
        executedTrace q step (after (q x)) (step (choose (q x)) x),
        executedTrace q step (after (q x)) (step (choose (q x)) y), rfl, ?_, hq, hs⟩
      simp only [executedTrace, ← hq, List.nil_append]

/-- If all permitted observations agree, the same adaptive experiment selects the same
finite action sequence on both inputs, not merely the same final answer. -/
theorem executedTrace_eq_of_futureEq {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (e : Experiment A Q V) :
    ∀ x y, FutureEq q step x y → executedTrace q step e x = executedTrace q step e y := by
  induction e with
  | finish _ => intro x y h; rfl
  | next choose after ih =>
    intro x y h
    have hq := futureEq_observation h
    simp only [executedTrace, ← hq]
    exact congrArg (List.cons (choose (q x)))
      (ih (q x) _ _ (futureEq_step h (choose (q x))))

/-! ## Size of independent equality-test banks
Each test uses a fresh copy of the initial input. The results count tests, not their word lengths.
-/

/-- The Boolean reports of independent equality trials at the selected labels. -/
def equalityTrials {X : Type*} [DecidableEq X] (tests : Finset X) (x : X) : tests → Bool :=
  fun a => decide (x = a.1)

/-- Two inputs have the same reports exactly when they agree, or both were left untested. -/
theorem equalityTrials_eq_iff {X : Type*} [DecidableEq X]
    (tests : Finset X) (x y : X) :
    equalityTrials tests x = equalityTrials tests y ↔ x = y ∨ (x ∉ tests ∧ y ∉ tests) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      constructor
      · intro hx
        have hb := congrFun h ⟨x, hx⟩
        have hyx : y ≠ x := fun he => hxy he.symm
        simp [equalityTrials, hyx] at hb
      · intro hy
        have hb := congrFun h ⟨y, hy⟩
        simp [equalityTrials, hxy] at hb
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · funext a
      have hxa : x ≠ a.1 := fun h => hx (h.symm ▸ a.2)
      have hya : y ≠ a.1 := fun h => hy (h.symm ▸ a.2)
      simp [equalityTrials, hxa, hya]

/-- Independent equality trials identify all inputs exactly when at most one input is untested. -/
theorem equalityTrials_injective_iff {X : Type*} [DecidableEq X] (tests : Finset X) :
    Function.Injective (equalityTrials tests) ↔ Set.Subsingleton {x | x ∉ tests} := by
  constructor
  · intro h x hx y hy
    exact h ((equalityTrials_eq_iff tests x y).mpr (Or.inr ⟨hx, hy⟩))
  · intro h x y he
    rcases (equalityTrials_eq_iff tests x y).mp he with hxy | ⟨hx, hy⟩
    · exact hxy
    · exact h hx hy

/-- On a finite carrier of size n, independent equality trials identify the input precisely
when at least n - 1 distinct labels are tested. The formula also covers the empty carrier. -/
theorem equalityTrials_injective_iff_card {X : Type*} [Fintype X] [DecidableEq X]
    (tests : Finset X) :
    Function.Injective (equalityTrials tests) ↔ Fintype.card X - 1 ≤ tests.card := by
  rw [equalityTrials_injective_iff]
  have h : Set.Subsingleton {x | x ∉ tests} ↔ testsᶜ.card ≤ 1 := by
    rw [Finset.card_le_one]
    simp only [Finset.mem_compl, Set.Subsingleton, Set.mem_setOf_eq]
  rw [h, Finset.card_compl]
  omega

/-- Testing every label except one attains the lower bound, without an assumed decoder. -/
theorem equalityTrials_erase_identifies {X : Type*} [Fintype X] [DecidableEq X] (x : X) :
    Function.Injective (equalityTrials (Finset.univ.erase x)) ∧
      (Finset.univ.erase x).card = Fintype.card X - 1 := by
  have hc : (Finset.univ.erase x).card = Fintype.card X - 1 := by simp
  exact ⟨(equalityTrials_injective_iff_card _).mpr (by omega), hc⟩

/-- In the destructive three-alternative model, each actual independent trial is exactly an
ordinary equality trial with an optional-record wrapper. -/
theorem trialRecord_eq_equalityTrial (i a : Fin 3) :
    trialRecord i a = some (decide (i = a)) := rfl

/-- Two independent destructive tests identify the three alternatives; fewer than two selected
labels do not. This is a trial budget, distinct from the impossibility of a single adaptive run. -/
theorem destructive_independent_trial_threshold (tests : Finset (Fin 3)) :
    Function.Injective (fun i : Fin 3 => fun a : tests => trialRecord i a.1) ↔ 2 ≤ tests.card := by
  have h : Function.Injective (fun i : Fin 3 => fun a : tests => trialRecord i a.1) ↔
      Function.Injective (equalityTrials tests) := by
    constructor
    · intro hinj i j he
      apply hinj
      funext a
      change trialRecord i a.1 = trialRecord j a.1
      rw [trialRecord_eq_equalityTrial, trialRecord_eq_equalityTrial]
      exact congrArg some (congrFun he a)
    · intro hinj i j he
      apply hinj
      funext a
      exact Option.some.inj (congrFun he a)
  rw [h, equalityTrials_injective_iff_card]
  norm_num

/-- Any separating family of tests has a subfamily of at most n - 1 tests on n candidates.
No finiteness assumption is made on the set of available tests or their possible reports. -/
theorem finite_separating_tests {I T Q : Type*} (read : T → I → Q)
    (candidates : Finset I)
    (hsep : ∀ i ∈ candidates, ∀ j ∈ candidates, i ≠ j → ∃ t, read t i ≠ read t j) :
    ∃ tests : Finset T, tests.card ≤ candidates.card - 1 ∧
      ∀ i ∈ candidates, ∀ j ∈ candidates,
        (∀ t ∈ tests, read t i = read t j) → i = j := by
  classical
  revert hsep
  induction candidates using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, by simp, ?_⟩
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  | @insert a s ha ih =>
    intro hsep
    have hssep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ t, read t i ≠ read t j :=
      fun i hi j hj => hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    obtain ⟨tests, hcard, htests⟩ := ih hssep
    by_cases hs : s = ∅
    · subst s
      refine ⟨∅, by simp, ?_⟩
      intro i hi j hj _
      have hi' : i = a := by simpa using hi
      have hj' : j = a := by simpa using hj
      exact hi'.trans hj'.symm
    · have hspos : 0 < s.card := by
        have hn : s.card ≠ 0 := fun hz => hs (Finset.card_eq_zero.mp hz)
        omega
      by_cases hc : ∃ b ∈ s, ∀ t ∈ tests, read t a = read t b
      · obtain ⟨b, hb, hab⟩ := hc
        have hne : a ≠ b := fun h => ha (h.symm ▸ hb)
        obtain ⟨t, ht⟩ := hsep a (Finset.mem_insert_self _ _) b
          (Finset.mem_insert_of_mem hb) hne
        refine ⟨insert t tests, ?_, ?_⟩
        · have hle := Finset.card_insert_le t tests
          rw [Finset.card_insert_of_notMem ha]
          omega
        · intro i hi j hj hij
          have hold : ∀ u ∈ tests, read u i = read u j :=
            fun u hu => hij u (Finset.mem_insert_of_mem hu)
          rcases Finset.mem_insert.mp hi with hia | his
          · subst i
            rcases Finset.mem_insert.mp hj with hja | hjs
            · exact hja.symm
            · have hbj : b = j := htests b hb j hjs
                (fun u hu => (hab u hu).symm.trans (hold u hu))
              subst j
              exact False.elim (ht (hij t (Finset.mem_insert_self _ _)))
          · rcases Finset.mem_insert.mp hj with hja | hjs
            · subst j
              have hbi : b = i := htests b hb i his
                (fun u hu => (hab u hu).symm.trans (hold u hu).symm)
              subst i
              exact False.elim (ht (hij t (Finset.mem_insert_self _ _)).symm)
            · exact htests i his j hjs hold
      · refine ⟨tests, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem ha]
          omega
        · intro i hi j hj hij
          rcases Finset.mem_insert.mp hi with hia | his
          · subst i
            rcases Finset.mem_insert.mp hj with hja | hjs
            · exact hja.symm
            · exact False.elim (hc ⟨j, hjs, hij⟩)
          · rcases Finset.mem_insert.mp hj with hja | hjs
            · subst j
              exact False.elim (hc ⟨i, his, fun t ht => (hij t ht).symm⟩)
            · exact htests i his j hjs hij

/-- For `n` initial states, distinct behavioral records are equivalent to the existence of a separating bank of at most `n-1` independent experiments. Each experiment starts from a fresh initial copy; word length is not bounded here. -/
theorem finite_independent_bank_iff {X A Q I : Type*} [Fintype I]
    (q : X → Q) (step : A → X → X) (initial : I → X) :
    Function.Injective (fun i => futureRecord q step (initial i)) ↔
      ∃ tests : Finset (List A), tests.card ≤ Fintype.card I - 1 ∧
        Function.Injective (fun i => fun w : tests => q (run step w.1 (initial i))) := by
  classical
  constructor
  · intro hinj
    have hsep : ∀ i ∈ (Finset.univ : Finset I), ∀ j ∈ (Finset.univ : Finset I),
        i ≠ j → ∃ w : List A, q (run step w (initial i)) ≠ q (run step w (initial j)) := by
      intro i _ j _ hij
      exact (not_futureEq_iff_word q step _ _).mp (fun h => hij (hinj h))
    obtain ⟨tests, hcard, htests⟩ :=
      finite_separating_tests (fun w i => q (run step w (initial i))) Finset.univ hsep
    refine ⟨tests, by simpa using hcard, ?_⟩
    intro i j he
    exact htests i (Finset.mem_univ _) j (Finset.mem_univ _)
      (fun w hw => congrFun he ⟨w, hw⟩)
  · rintro ⟨tests, _, hinj⟩ i j he
    apply hinj
    funext w
    exact congrFun he w.1

/-- For a finite state set, a bank of independent finite words with size at most the number of distinct full records minus one has the same observation kernel as the complete behavioral record. -/
theorem finite_behavioral_record_realization {X A Q : Type*} [Fintype X]
    (q : X → Q) (step : A → X → X) :
    ∃ tests : Finset (List A),
      tests.card ≤ Nat.card (Set.range (futureRecord q step)) - 1 ∧
      ∀ x y, (∀ w ∈ tests, q (run step w x) = q (run step w y)) ↔ FutureEq q step x y := by
  classical
  let R := Set.range (futureRecord q step)
  letI : Fintype R := Fintype.ofFinite R
  let initial : R → X := fun r => Classical.choose r.2
  have hrecord (r : R) : futureRecord q step (initial r) = r.1 :=
    Classical.choose_spec r.2
  have hinj : Function.Injective (fun r : R => futureRecord q step (initial r)) := by
    intro r s hrs
    exact Subtype.ext ((hrecord r).symm.trans (hrs.trans (hrecord s)))
  obtain ⟨tests, hcard, htests⟩ := (finite_independent_bank_iff q step initial).mp hinj
  refine ⟨tests, ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hcard
  · intro x y
    constructor
    · intro hxy
      let rx : R := ⟨futureRecord q step x, x, rfl⟩
      let ry : R := ⟨futureRecord q step y, y, rfl⟩
      have he : (fun w : tests => q (run step w.1 (initial rx))) =
          (fun w : tests => q (run step w.1 (initial ry))) := by
        funext w
        exact (congrFun (hrecord rx) w.1).trans
          ((hxy w.1 w.2).trans (congrFun (hrecord ry) w.1).symm)
      exact congrArg Subtype.val (htests he)
    · intro h w _
      exact congrFun h w

end OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
