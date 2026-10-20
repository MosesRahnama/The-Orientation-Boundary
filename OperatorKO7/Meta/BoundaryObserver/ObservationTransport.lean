import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation

set_option autoImplicit false

/-!
# Exact transport of observation and action

Graph: `Audit/ledgers/operational-inexpressibility/OBSERVATION-TRANSPORT-PROOF-GRAPH.md`.
State, action and record equivalences preserve words, adaptive experiments, their actual traces
and the least stable observer. The commuting laws are explicit input obligations. The countdown
instance gives an exact finite observation cost; matching current records alone fails a control.
Relation: total deterministic actions and the existing `FutureEq`, without changing its meaning.
Trust: kernel-only. No claim that an unspecified pair of physical systems supplies these maps.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationTransport

open AdmissibleObservation

/-- An exact comparison of two observation systems, including their permitted actions. -/
structure ObservationIso {X Y A B Q R : Type*}
    (q : X → Q) (step : A → X → X) (q' : Y → R) (step' : B → Y → Y) where
  state : X ≃ Y
  action : A ≃ B
  record : Q ≃ R
  observation : ∀ x, q' (state x) = record (q x)
  transition : ∀ a x, step' (action a) (state x) = state (step a x)

namespace ObservationIso

variable {X Y Z A B C Q R S : Type*}
variable {q : X → Q} {step : A → X → X}
variable {q' : Y → R} {step' : B → Y → Y}
variable {q'' : Z → S} {step'' : C → Z → Z}

/-- The identity comparison. -/
def refl (q : X → Q) (step : A → X → X) : ObservationIso q step q step where
  state := Equiv.refl X
  action := Equiv.refl A
  record := Equiv.refl Q
  observation _ := rfl
  transition _ _ := rfl

/-- The inverse comparison preserves both laws, not just the carrier maps. -/
def symm (e : ObservationIso q step q' step') : ObservationIso q' step' q step where
  state := e.state.symm
  action := e.action.symm
  record := e.record.symm
  observation y := by
    apply e.record.injective
    simpa using (e.observation (e.state.symm y)).symm
  transition b y := by
    apply e.state.injective
    simpa using (e.transition (e.action.symm b) (e.state.symm y)).symm

/-- Comparisons compose with the same maps at every interface. -/
def trans (e : ObservationIso q step q' step') (f : ObservationIso q' step' q'' step'') :
    ObservationIso q step q'' step'' where
  state := e.state.trans f.state
  action := e.action.trans f.action
  record := e.record.trans f.record
  observation x := by
    change q'' (f.state (e.state x)) = f.record (e.record (q x))
    rw [f.observation, e.observation]
  transition a x := by
    change step'' (f.action (e.action a)) (f.state (e.state x)) =
      f.state (e.state (step a x))
    rw [f.transition, e.transition]

/-- Every finite word commutes with the state map. -/
theorem run_map (e : ObservationIso q step q' step') (w : List A) (x : X) :
    run step' (w.map e.action) (e.state x) = e.state (run step w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, run, e.transition]
    exact ih (step a x)

/-- Every observed word commutes with the record map. -/
theorem observation_run (e : ObservationIso q step q' step') (w : List A) (x : X) :
    q' (run step' (w.map e.action) (e.state x)) = e.record (q (run step w x)) := by
  rw [e.run_map, e.observation]

/-- The full experimental kernels are preserved and reflected. -/
theorem futureEq_iff (e : ObservationIso q step q' step') (x y : X) :
    FutureEq q' step' (e.state x) (e.state y) ↔ FutureEq q step x y := by
  constructor
  · intro h
    funext w
    apply e.record.injective
    change e.record (q (run step w x)) = e.record (q (run step w y))
    rw [← e.observation_run w x, ← e.observation_run w y]
    exact congrFun h (w.map e.action)
  · intro h
    funext w
    change q' (run step' w (e.state x)) = q' (run step' w (e.state y))
    have hw : (w.map e.action.symm).map e.action = w := by simp
    rw [← hw, e.observation_run, e.observation_run]
    exact congrArg e.record (congrFun h (w.map e.action.symm))

/-- The least stable observers have explicit inverse maps induced by the original state maps. -/
def minimalEquiv (e : ObservationIso q step q' step') :
    MinimalState q step ≃ MinimalState q' step' where
  toFun := Quotient.map e.state (fun x y h => (e.futureEq_iff x y).mpr h)
  invFun := Quotient.map e.state.symm (fun x y h => (e.symm.futureEq_iff x y).mpr h)
  left_inv z := by
    induction z using Quotient.inductionOn with
    | h x =>
      change minimalRecord q step (e.state.symm (e.state x)) = minimalRecord q step x
      rw [Equiv.symm_apply_apply]
  right_inv z := by
    induction z using Quotient.inductionOn with
    | h x =>
      change minimalRecord q' step' (e.state (e.state.symm x)) = minimalRecord q' step' x
      rw [Equiv.apply_symm_apply]

/-- The induced equivalence is bound to the original states. -/
theorem minimalEquiv_record (e : ObservationIso q step q' step') (x : X) :
    e.minimalEquiv (minimalRecord q step x) = minimalRecord q' step' (e.state x) := rfl

/-- Reading a minimal state commutes with transport. -/
theorem minimalEquiv_read (e : ObservationIso q step q' step') (z : MinimalState q step) :
    minimalRead q' step' (e.minimalEquiv z) = e.record (minimalRead q step z) := by
  induction z using Quotient.inductionOn with
  | h x => exact e.observation x

/-- Updating a minimal state commutes with the same transport. -/
theorem minimalEquiv_step (e : ObservationIso q step q' step') (a : A)
    (z : MinimalState q step) :
    e.minimalEquiv (minimalStep q step a z) =
      minimalStep q' step' (e.action a) (e.minimalEquiv z) := by
  induction z using Quotient.inductionOn with
  | h x => exact congrArg (minimalRecord q' step') (e.transition a x).symm

end ObservationIso

/-- Translate the entire adaptive experiment, including choices made from earlier records. -/
def translate {A B Q R V W : Type*} (action : A ≃ B) (record : Q ≃ R) (value : V ≃ W) :
    Experiment A Q V → Experiment B R W
  | .finish out => .finish (fun r => value (out (record.symm r)))
  | .next choose after => .next (fun r => action (choose (record.symm r)))
      (fun r => translate action record value (after (record.symm r)))

/-- Back-translation restores the actual experiment, not just its output. -/
theorem translate_inverse {A B Q R V W : Type*}
    (action : A ≃ B) (record : Q ≃ R) (value : V ≃ W) (e : Experiment A Q V) :
    translate action.symm record.symm value.symm (translate action record value e) = e := by
  induction e with
  | finish out => simp [translate]
  | next choose after ih =>
    simp only [translate, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    congr 1
    funext q
    exact ih q

/-- The languages of adaptive experiments are equivalent under all three relabellings. -/
def experimentEquiv {A B Q R V W : Type*}
    (action : A ≃ B) (record : Q ≃ R) (value : V ≃ W) :
    Experiment A Q V ≃ Experiment B R W where
  toFun := translate action record value
  invFun := translate action.symm record.symm value.symm
  left_inv := translate_inverse action record value
  right_inv e := by simpa using translate_inverse action.symm record.symm value.symm e

namespace ObservationIso

variable {X Y A B Q R V W : Type*}
variable {q : X → Q} {step : A → X → X}
variable {q' : Y → R} {step' : B → Y → Y}

/-- The output law of every adaptive experiment follows from the two system commuting laws. -/
theorem evaluate_translate (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) :
    evaluate q' step' (translate e.action e.record value test) (e.state x) =
      value (evaluate q step test x) := by
  induction test generalizing x with
  | finish out => simp only [translate, evaluate, e.observation, Equiv.symm_apply_apply]
  | next choose after ih =>
    simp only [translate, evaluate, e.observation, Equiv.symm_apply_apply, e.transition]
    exact ih (q x) (step (choose (q x)) x)

/-- Transport preserves the actual action sequence selected on the input. -/
theorem executedTrace_translate (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) :
    executedTrace q' step' (translate e.action e.record value test) (e.state x) =
      (executedTrace q step test x).map e.action := by
  induction test generalizing x with
  | finish out => rfl
  | next choose after ih =>
    simp only [translate, executedTrace, e.observation, Equiv.symm_apply_apply,
      e.transition, List.map_cons]
    exact congrArg (List.cons (e.action (choose (q x))))
      (ih (q x) (step (choose (q x)) x))

/-- The number of actions is unchanged, even when it depends on the observed input. -/
theorem action_count_preserved (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) :
    (executedTrace q' step' (translate e.action e.record value test) (e.state x)).length =
      (executedTrace q step test x).length := by
  rw [e.executedTrace_translate, List.length_map]

/-- Every additive action cost is preserved under its transported cost function. -/
theorem action_cost_preserved (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) (cost : A → ℕ) :
    ((executedTrace q' step' (translate e.action e.record value test) (e.state x)).map
      (fun b => cost (e.action.symm b))).sum =
      ((executedTrace q step test x).map cost).sum := by
  rw [e.executedTrace_translate]
  simp [List.map_map, Function.comp_def]

/-- A single executed experiment transports both its changed state and its readable answer. -/
theorem action_and_record_transport (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) :
    run step' (executedTrace q' step' (translate e.action e.record value test) (e.state x))
        (e.state x) = e.state (run step (executedTrace q step test x) x) ∧
      evaluate q' step' (translate e.action e.record value test) (e.state x) =
        value (evaluate q step test x) := by
  refine ⟨?_, e.evaluate_translate value test x⟩
  rw [e.executedTrace_translate, e.run_map]

end ObservationIso

/-- A finite action budget for separating two states. Zero counts a current-record test. -/
def SeparatesWithin {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (x y : X) (budget : ℕ) : Prop :=
  ∃ w : List A, w.length ≤ budget ∧ q (run step w x) ≠ q (run step w y)

/-- Every separating budget is preserved and reflected; therefore its least value is too. -/
theorem separatesWithin_transport {X Y A B Q R : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (x y : X) (budget : ℕ) :
    SeparatesWithin q' step' (e.state x) (e.state y) budget ↔
      SeparatesWithin q step x y budget := by
  constructor
  · rintro ⟨w, hw, hne⟩
    refine ⟨w.map e.action.symm, by simpa using hw, ?_⟩
    intro he
    apply hne
    have hmap : (w.map e.action.symm).map e.action = w := by simp
    rw [← hmap, e.observation_run, e.observation_run]
    exact congrArg e.record he
  · rintro ⟨w, hw, hne⟩
    refine ⟨w.map e.action, by simpa using hw, ?_⟩
    rw [e.observation_run, e.observation_run]
    exact fun he => hne (e.record.injective he)

/-- A solver is one adaptive experiment, with a uniform bound on its actual action count. -/
def SolvesWithin {X A Q V : Type*} (q : X → Q) (step : A → X → X)
    (target : X → V) (budget : ℕ) : Prop :=
  ∃ test : Experiment A Q V, (∀ x, evaluate q step test x = target x) ∧
    ∀ x, (executedTrace q step test x).length ≤ budget

/-- A solved task is transported by construction, without assuming a decoder on the target. -/
theorem transport_solver {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) (budget : ℕ)
    (h : SolvesWithin q step target budget) : SolvesWithin q' step' target' budget := by
  obtain ⟨test, htest, hbudget⟩ := h
  refine ⟨translate e.action e.record value test, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.state.surjective y
    rw [e.evaluate_translate, htest, htarget]
  · intro y
    obtain ⟨x, rfl⟩ := e.state.surjective y
    rw [e.action_count_preserved]
    exact hbudget x

/-- Exact solvability under every uniform finite budget is an invariant of the same maps. -/
theorem solvesWithin_transport_iff {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) (budget : ℕ) :
    SolvesWithin q' step' target' budget ↔ SolvesWithin q step target budget := by
  refine ⟨transport_solver e.symm value.symm target' target ?_ budget,
    transport_solver e value target target' htarget budget⟩
  intro y
  apply value.injective
  simpa using (htarget (e.state.symm y)).symm

/-! ## The unique first separating event -/

/-- The observations agree through n actions and differ after the next action of the word. -/
def FirstDistinction {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (w : List A) (x y : X) (n : ℕ) : Prop :=
  n < w.length ∧
    (∀ j ≤ n, q (run step (w.take j) x) = q (run step (w.take j) y)) ∧
    q (run step (w.take (n + 1)) x) ≠ q (run step (w.take (n + 1)) y)

/-- There is at most one first separating position along a fixed word. -/
theorem firstDistinction_unique {X A Q : Type*} {q : X → Q} {step : A → X → X}
    {w : List A} {x y : X} {n m : ℕ}
    (hn : FirstDistinction q step w x y n) (hm : FirstDistinction q step w x y m) : n = m := by
  have hnm : ¬ n < m := fun h => hn.2.2 (hm.2.1 (n + 1) (by omega))
  have hmn : ¬ m < n := fun h => hm.2.2 (hn.2.1 (m + 1) (by omega))
  omega

/-- A word that resolves a currently merged pair contains one unique first separating event.
Later observations can change again; uniqueness concerns the first event only. -/
theorem firstDistinction_existsUnique {X A Q : Type*} (q : X → Q) (step : A → X → X)
    (w : List A) {x y : X} (hcurrent : q x = q y)
    (hfinal : q (run step w x) ≠ q (run step w y)) :
    ∃! n, FirstDistinction q step w x y n := by
  classical
  let P : ℕ → Prop := fun j => q (run step (w.take j) x) ≠ q (run step (w.take j) y)
  have hp : ∃ j, P j := ⟨w.length, by simpa [P] using hfinal⟩
  let k := Nat.find hp
  have hk : P k := Nat.find_spec hp
  have hlen : k ≤ w.length := Nat.find_min' hp (by simpa [P] using hfinal)
  have hpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    have he : q x ≠ q y := by simpa [P, hz, run] using hk
    exact he hcurrent
  have hf : FirstDistinction q step w x y (k - 1) := by
    refine ⟨by omega, ?_, ?_⟩
    · intro j hj
      by_contra hn
      have hj' : k ≤ j := Nat.find_min' hp hn
      omega
    · have he : k - 1 + 1 = k := by omega
      simpa only [he] using hk
  exact ⟨k - 1, hf, fun m hm => firstDistinction_unique hm hf⟩

/-- The same maps preserve the exact first separating position, not just eventual separation. -/
theorem firstDistinction_transport {X Y A B Q R : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (w : List A) (x y : X) (n : ℕ) :
    FirstDistinction q' step' (w.map e.action) (e.state x) (e.state y) n ↔
      FirstDistinction q step w x y n := by
  have ht (j : ℕ) : (w.map e.action).take j = (w.take j).map e.action := by simp
  have hx (j : ℕ) : q' (run step' ((w.map e.action).take j) (e.state x)) =
      e.record (q (run step (w.take j) x)) := by rw [ht]; exact e.observation_run _ _
  have hy (j : ℕ) : q' (run step' ((w.map e.action).take j) (e.state y)) =
      e.record (q (run step (w.take j) y)) := by rw [ht]; exact e.observation_run _ _
  constructor
  · rintro ⟨hn, heq, hne⟩
    refine ⟨by simpa using hn, ?_, ?_⟩
    · intro j hj
      apply e.record.injective
      exact (hx j).symm.trans ((heq j hj).trans (hy j))
    · intro he
      exact hne ((hx (n + 1)).trans ((congrArg e.record he).trans (hy (n + 1)).symm))
  · rintro ⟨hn, heq, hne⟩
    refine ⟨by simpa using hn, ?_, ?_⟩
    · intro j hj
      exact (hx j).trans ((congrArg e.record (heq j hj)).trans (hy j).symm)
    · intro he
      exact hne (e.record.injective ((hx (n + 1)).symm.trans (he.trans (hy (n + 1)))))

/-! ## Exact observable structure under a noninvertible state projection -/

namespace Projection

variable {X Y A B Q R : Type*}
variable {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
variable (f : X → Y) (action : A ≃ B) (record : Q ≃ R)
variable (hread : ∀ x, q' (f x) = record (q x))
variable (hstep : ∀ a x, step' (action a) (f x) = f (step a x))

include hstep

/-- Commuting with each action suffices to commute with all words; f need not be injective. -/
theorem run_map (w : List A) (x : X) :
    run step' (w.map action) (f x) = f (run step w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, run, hstep]
    exact ih (step a x)

include hread

/-- The projected word has exactly the original record, with its declared relabelling. -/
theorem observation_run (w : List A) (x : X) :
    q' (run step' (w.map action) (f x)) = record (q (run step w x)) := by
  rw [run_map f action hstep, hread]

/-- Such a projection loses no observable distinction and manufactures none. -/
theorem futureEq_iff (x y : X) :
    FutureEq q' step' (f x) (f y) ↔ FutureEq q step x y := by
  constructor
  · intro h
    funext w
    apply record.injective
    change record (q (run step w x)) = record (q (run step w y))
    rw [← observation_run f action record hread hstep w x,
      ← observation_run f action record hread hstep w y]
    exact congrFun h (w.map action)
  · intro h
    funext w
    change q' (run step' w (f x)) = q' (run step' w (f y))
    have hw : (w.map action.symm).map action = w := by simp
    rw [← hw, observation_run f action record hread hstep,
      observation_run f action record hread hstep]
    exact congrArg record (congrFun h (w.map action.symm))

/-- A surjective projection gives inverse maps of the observable quotients even when its
raw-state map has no inverse. -/
noncomputable def quotientEquiv (hf : Function.Surjective f) :
    MinimalState q step ≃ MinimalState q' step' := by
  refine Equiv.ofBijective
    (Quotient.map f (fun x y h => (futureEq_iff f action record hread hstep x y).mpr h))
    ⟨?_, ?_⟩
  · intro u v huv
    induction u using Quotient.inductionOn with
    | h x =>
      induction v using Quotient.inductionOn with
      | h y =>
        exact Quotient.sound ((futureEq_iff f action record hread hstep x y).mp
          (Quotient.exact huv))
  · intro z
    induction z using Quotient.inductionOn with
    | h y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨minimalRecord q step x, rfl⟩

/-- The equivalence uses the given state projection, not a separate abstract bijection. -/
theorem quotientEquiv_record (hf : Function.Surjective f) (x : X) :
    quotientEquiv f action record hread hstep hf (minimalRecord q step x) =
      minimalRecord q' step' (f x) := rfl

/-- Its current readout uses the same record map. -/
theorem quotientEquiv_read (hf : Function.Surjective f) (z : MinimalState q step) :
    minimalRead q' step' (quotientEquiv f action record hread hstep hf z) =
      record (minimalRead q step z) := by
  induction z using Quotient.inductionOn with
  | h x => exact hread x

/-- Its next state uses the same action map. -/
theorem quotientEquiv_step (hf : Function.Surjective f) (a : A) (z : MinimalState q step) :
    quotientEquiv f action record hread hstep hf (minimalStep q step a z) =
      minimalStep q' step' (action a) (quotientEquiv f action record hread hstep hf z) := by
  induction z using Quotient.inductionOn with
  | h x => exact congrArg (minimalRecord q' step') (hstep a x).symm

/-- The least observable systems are isomorphic in the full action-and-record sense. -/
noncomputable def minimalSystemIso (hf : Function.Surjective f) :
    ObservationIso (minimalRead q step) (minimalStep q step)
      (minimalRead q' step') (minimalStep q' step') where
  state := quotientEquiv f action record hread hstep hf
  action := action
  record := record
  observation := quotientEquiv_read f action record hread hstep hf
  transition a z := (quotientEquiv_step f action record hread hstep hf a z).symm

end Projection

/-! ## The hidden countdown: exact finite resolution cost -/

/-- The observer only reports whether the countdown has stopped. -/
def countdownRead (n : ℕ) : Bool := decide (n = 0)

/-- A permitted clock step decreases the remaining count and holds at zero. -/
def countdownStep (_ : Unit) (n : ℕ) : ℕ := n - 1

/-- Waiting for a word subtracts its length, with natural subtraction at zero. -/
theorem countdown_run (w : List Unit) (n : ℕ) :
    run countdownStep w n = n - w.length := by
  induction w generalizing n with
  | nil => simp only [run, List.length_nil, Nat.sub_zero]
  | cons a w ih =>
    simp only [run, countdownStep, List.length_cons, ih]
    omega

/-- Waiting until n has stopped orders any state indistinguishable from n. -/
theorem countdown_le_of_futureEq {n m : ℕ}
    (h : FutureEq countdownRead countdownStep n m) : m ≤ n := by
  have he := congrFun h (List.replicate n ())
  change countdownRead (run countdownStep (List.replicate n ()) n) =
    countdownRead (run countdownStep (List.replicate n ()) m) at he
  simp only [countdown_run, List.length_replicate, countdownRead, Nat.sub_self,
    decide_true] at he
  exact Nat.sub_eq_zero_iff_le.mp (of_decide_eq_true he.symm)

/-- All finite waits distinguish exactly the initial counts, despite the single current bit. -/
theorem countdown_futureEq_iff (n m : ℕ) :
    FutureEq countdownRead countdownStep n m ↔ n = m := by
  constructor
  · intro h
    exact Nat.le_antisymm (countdown_le_of_futureEq h.symm) (countdown_le_of_futureEq h)
  · rintro rfl
    rfl

/-- Two unequal countdowns first become distinguishable when the smaller one reaches zero. -/
theorem countdown_exact_budget {n m budget : ℕ} (hnm : n < m) :
    SeparatesWithin countdownRead countdownStep n m budget ↔ n ≤ budget := by
  constructor
  · rintro ⟨w, hw, hne⟩
    by_contra hn
    have hn' : n - w.length ≠ 0 := by omega
    have hm' : m - w.length ≠ 0 := by omega
    exact hne (by simp only [countdown_run, countdownRead, hn', hm', decide_false])
  · intro hn
    refine ⟨List.replicate n (), by simpa using hn, ?_⟩
    have hm : m - n ≠ 0 := by omega
    simp [countdown_run, countdownRead, hm]

/-- No fixed finite waiting budget distinguishes all possible countdowns. -/
theorem bounded_wait_still_merges (budget : ℕ) :
    budget + 1 ≠ budget + 2 ∧
      ¬ SeparatesWithin countdownRead countdownStep (budget + 1) (budget + 2) budget := by
  constructor
  · omega
  · rw [countdown_exact_budget (by omega)]
    omega

/-- The least unrestricted countdown observer is the natural-number count itself. -/
def countdownMinimalEquiv : MinimalState countdownRead countdownStep ≃ ℕ where
  toFun := Quotient.lift id (fun n m h => (countdown_futureEq_iff n m).mp h)
  invFun := minimalRecord countdownRead countdownStep
  left_inv z := by
    induction z using Quotient.inductionOn with
    | h n => rfl
  right_inv _ := rfl

/-- Read the stopped/running bit while omitting all payload state. -/
def payloadRead {P : Type*} (x : ℕ × P) : Bool := countdownRead x.1

/-- The payload may undergo any supplied update while the counter is active. Both coordinates
hold once the counter reaches zero. No bound on the size or growth of P is imposed. -/
def payloadStep {P : Type*} (update : ℕ → P → P) (_ : Unit) : ℕ × P → ℕ × P
  | (0, p) => (0, p)
  | (n + 1, p) => (n, update n p)

/-- Counter independence is the precise local law licensing the payload projection. -/
theorem payload_counter_commutes {P : Type*} (update : ℕ → P → P) (a : Unit) (x : ℕ × P) :
    countdownStep a x.1 = (payloadStep update a x).1 := by
  rcases x with ⟨n, p⟩
  cases n <;> rfl

/-- All possible payload evolutions have the same experimental kernel: equality of the
remaining count. The claim concerns the specified countdown readout and action interface. -/
theorem payload_futureEq_iff {P : Type*} (update : ℕ → P → P) (n m : ℕ) (p r : P) :
    FutureEq payloadRead (payloadStep update) (n, p) (m, r) ↔ n = m := by
  have h := Projection.futureEq_iff
    (q := payloadRead) (step := payloadStep update) (q' := countdownRead) (step' := countdownStep)
    Prod.fst (Equiv.refl Unit) (Equiv.refl Bool) (fun _ => rfl)
    (payload_counter_commutes update) (n, p) (m, r)
  exact h.symm.trans (countdown_futureEq_iff n m)

/-- The least observer for an arbitrary hidden payload is exactly the remaining natural count. -/
noncomputable def payloadMinimalEquiv {P : Type*} [Nonempty P] (update : ℕ → P → P) :
    MinimalState payloadRead (payloadStep update) ≃ ℕ :=
  (Projection.quotientEquiv
    (q := payloadRead) (step := payloadStep update) (q' := countdownRead) (step' := countdownStep)
    Prod.fst (Equiv.refl Unit) (Equiv.refl Bool) (fun _ => rfl)
    (payload_counter_commutes update)
    (fun n => ⟨(n, Classical.choice inferInstance), rfl⟩)).trans countdownMinimalEquiv

/-- The exact equivalence returns the actual counter of the original state. -/
theorem payloadMinimalEquiv_record {P : Type*} [Nonempty P] (update : ℕ → P → P)
    (n : ℕ) (p : P) :
    payloadMinimalEquiv update (minimalRecord payloadRead (payloadStep update) (n, p)) = n := rfl

/-- The raw payload systems need not be isomorphic to the counter system, even though their
least observable systems are. Two payload choices at zero prove the distinction. -/
theorem no_raw_payload_iso (update : ℕ → Bool → Bool) :
    ¬ Nonempty (ObservationIso payloadRead (payloadStep update) countdownRead countdownStep) := by
  rintro ⟨e⟩
  have h := (payload_futureEq_iff update 0 0 false true).mpr rfl
  have he := (countdown_futureEq_iff _ _).mp ((e.futureEq_iff _ _).mpr h)
  have hp := e.state.injective he
  have hb : false = true := congrArg Prod.snd hp
  cases hb

/-- A nontrivial infinite system supplies an actual comparison on two different carriers. -/
def taggedCountdownIso : ObservationIso countdownRead countdownStep
    (fun p : ℕ × Unit => countdownRead p.1)
    (fun _ : Unit => fun p : ℕ × Unit => (p.1 - 1, ())) where
  state :=
    { toFun := fun n => (n, ())
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨n, u⟩; cases u; rfl }
  action := Equiv.refl Unit
  record := Equiv.refl Bool
  observation _ := rfl
  transition _ _ := rfl

/-- Identical current observers can have different experimental kernels when the actions
are changed. The transition law in ObservationIso is therefore necessary. -/
theorem same_record_different_future :
    FutureEq (Prod.fst : Bool × Bool → Bool) (fun _ : Unit => id)
      (false, false) (false, true) ∧
    ¬ FutureEq (Prod.fst : Bool × Bool → Bool)
      (fun _ : Unit => fun p : Bool × Bool => (p.2, p.1))
      (false, false) (false, true) := by
  constructor
  · funext w
    change (run (fun _ : Unit => id) w (false, false)).1 =
      (run (fun _ : Unit => id) w (false, true)).1
    induction w with
    | nil => rfl
    | cons _ _ ih => exact ih
  · intro h
    have he := congrFun h [()]
    change false = true at he
    cases he

/-! ## Resource singularity for adaptive observation -/

/-- A separating word remains within any larger action budget. -/
theorem separatesWithin_mono {X A Q : Type*} {q : X → Q} {step : A → X → X}
    {x y : X} {b c : ℕ} (h : SeparatesWithin q step x y b) (hbc : b ≤ c) :
    SeparatesWithin q step x y c := by
  obtain ⟨w, hw, hne⟩ := h
  exact ⟨w, hw.trans hbc, hne⟩

/-- Different adaptive outputs require a separating word no longer than the actual run on x.
The word is the shared executed prefix through an observation event, not an imagined probe. -/
theorem adaptive_distinction_has_bounded_word {X A Q V : Type*}
    (q : X → Q) (step : A → X → X) (test : Experiment A Q V) (x y : X)
    (hne : evaluate q step test x ≠ evaluate q step test y) :
    SeparatesWithin q step x y (executedTrace q step test x).length := by
  classical
  by_cases hq : q x = q y
  · obtain ⟨before, a, afterX, afterY, hx, _hy, _hb, ha⟩ :=
      actual_resolution_has_boundary_event q step test x y hq hne
    refine ⟨before ++ [a], ?_, ?_⟩
    · rw [hx]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simpa only [run_append, run] using ha
  · exact ⟨[], Nat.zero_le _, hq⟩

/-- A correct bounded adaptive solver separates every pair with different requested answers. -/
theorem solvesWithin_separates_targets {X A Q V : Type*}
    {q : X → Q} {step : A → X → X} {target : X → V} {budget : ℕ}
    (h : SolvesWithin q step target budget) {x y : X} (hne : target x ≠ target y) :
    SeparatesWithin q step x y budget := by
  obtain ⟨test, hcorrect, hbudget⟩ := h
  have hout : evaluate q step test x ≠ evaluate q step test y := by
    rw [hcorrect, hcorrect]
    exact hne
  exact separatesWithin_mono
    (adaptive_distinction_has_bounded_word q step test x y hout) (hbudget x)

/-- Every finite observation budget leaves some pair with different target values unresolved.
This quantifies over all permitted words, not just one chosen test or algorithm. -/
def ResolutionSingularity {X A Q V : Type*} (q : X → Q) (step : A → X → X)
    (target : X → V) : Prop :=
  ∀ budget : ℕ, ∃ x y, target x ≠ target y ∧ ¬ SeparatesWithin q step x y budget

/-- No well-founded adaptive experiment solves the whole task within a uniform finite budget. -/
def UniformBudgetObstruction {X A Q V : Type*} (q : X → Q) (step : A → X → X)
    (target : X → V) : Prop := ∀ budget : ℕ, ¬ SolvesWithin q step target budget

/-- Pairwise budget failure rules out every bounded adaptive solver.
The converse is not asserted: destructive tests can obstruct joint identification separately. -/
theorem resolutionSingularity_blocks_adaptive {X A Q V : Type*}
    {q : X → Q} {step : A → X → X} {target : X → V}
    (h : ResolutionSingularity q step target) : UniformBudgetObstruction q step target := by
  intro budget hsolver
  obtain ⟨x, y, hne, hbad⟩ := h budget
  exact hbad (solvesWithin_separates_targets hsolver hne)

/-- The exact state, action, record and answer translations preserve resource singularity. -/
theorem resolutionSingularity_transport_iff {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) :
    ResolutionSingularity q' step' target' ↔ ResolutionSingularity q step target := by
  constructor
  · intro h budget
    obtain ⟨y, z, hne, hbad⟩ := h budget
    obtain ⟨x, rfl⟩ := e.state.surjective y
    obtain ⟨x', rfl⟩ := e.state.surjective z
    refine ⟨x, x', ?_, ?_⟩
    · intro he
      exact hne ((htarget x).trans ((congrArg value he).trans (htarget x').symm))
    · intro hsep
      exact hbad ((separatesWithin_transport e x x' budget).mpr hsep)
  · intro h budget
    obtain ⟨x, x', hne, hbad⟩ := h budget
    refine ⟨e.state x, e.state x', ?_, ?_⟩
    · intro he
      exact hne (value.injective ((htarget x).symm.trans (he.trans (htarget x'))))
    · intro hsep
      exact hbad ((separatesWithin_transport e x x' budget).mp hsep)

/-- The uniform adaptive impossibility is also preserved and reflected without a pairwise premise. -/
theorem uniformBudgetObstruction_transport_iff {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) :
    UniformBudgetObstruction q' step' target' ↔ UniformBudgetObstruction q step target := by
  constructor
  · intro h budget hs
    exact h budget ((solvesWithin_transport_iff e value target target' htarget budget).mpr hs)
  · intro h budget hs
    exact h budget ((solvesWithin_transport_iff e value target target' htarget budget).mp hs)

/-- A positive control: reading the current record is always solvable with no action. -/
theorem current_record_solver {X A Q : Type*} (q : X → Q) (step : A → X → X) :
    SolvesWithin q step q 0 :=
  ⟨.finish id, fun _ => rfl, fun _ => Nat.le_refl 0⟩

/-- Each countdown is finite and all counts are distinguishable, yet every finite budget
misses larger counts. This is a uniform resource obstruction, not nontermination. -/
theorem countdown_resolution_singularity :
    ResolutionSingularity countdownRead countdownStep id := by
  intro budget
  exact ⟨budget + 1, budget + 2, (bounded_wait_still_merges budget).1,
    (bounded_wait_still_merges budget).2⟩

/-- No bounded adaptive procedure identifies all hidden countdowns. -/
theorem countdown_no_uniform_solver :
    UniformBudgetObstruction countdownRead countdownStep id :=
  resolutionSingularity_blocks_adaptive countdown_resolution_singularity

/-- The countdown boundary survives every explicitly supplied observation-system isomorphism. -/
theorem countdown_singularity_transport {Y B R W : Type*}
    {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso countdownRead countdownStep q' step') (value : ℕ ≃ W)
    (target' : Y → W) (htarget : ∀ n, target' (e.state n) = value n) :
    ResolutionSingularity q' step' target' ∧ UniformBudgetObstruction q' step' target' := by
  have hs := (resolutionSingularity_transport_iff e value id target' htarget).mpr
    countdown_resolution_singularity
  exact ⟨hs, resolutionSingularity_blocks_adaptive hs⟩

end OperatorKO7.Meta.BoundaryObserver.ObservationTransport
