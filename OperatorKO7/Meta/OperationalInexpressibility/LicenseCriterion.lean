import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.SchemaCanonicalTrace
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-!
# Recursor instances of the observer-target license criterion

The generic license and refinement theory lives in `LicenseCore.lean`. This file supplies the
step-duplicating recursor instances, erased-payload executions, and payload-loop controls.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w u'

/-! ## The recursor instance -/

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- The counter observer on the live stages of a trace of depth `k`. -/
def counterObserver (k : Nat) (i : Fin (k + 1)) : Nat := trace_ctr k i.val

/-- Residual work from stage `i`: the counter plus the final base step. -/
def residualWork (k : Nat) (i : Fin (k + 1)) : Nat := trace_ctr k i.val + 1

/-- The payload-multiplicity coordinate at stage `i`. -/
def payloadCoordinate (k : Nat) (i : Fin (k + 1)) : Nat := trace_pay i.val

/-- **Positive instance.** The counter projection is licensed for the residual-work verdict:
residual work is constant on the fibers of the counter. -/
theorem counter_licensed_for_residualWork (k : Nat) :
    Licensed (counterObserver k) (residualWork k) := by
  intro x y hxy
  unfold residualWork
  unfold counterObserver at hxy
  rw [hxy]

/-- The payload coordinate is not constant on the fibers of the constant observer once the
trace has a live stage, so the constant observer is unlicensed for the payload count. -/
theorem constant_observer_unlicensed_for_payload {k : Nat} (hk : 0 < k) :
    ¬ Licensed (fun _ : Fin (k + 1) => ()) (payloadCoordinate k) := by
  intro h
  have := h ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
  simp [payloadCoordinate, trace_pay] at this

/-- The corresponding collision, as the operational-inexpressibility witness. -/
theorem constant_observer_payload_collision {k : Nat} (hk : 0 < k) :
    OperationallyInexpressibleAt (fun _ : Fin (k + 1) => ()) (payloadCoordinate k)
      ⟨0, by omega⟩ ⟨1, by omega⟩ :=
  ⟨rfl, by simp [payloadCoordinate, trace_pay]⟩


/-- On one fixed finite trace, the counter already identifies the stage. -/
theorem counterObserver_injective (k : Nat) :
    Function.Injective (counterObserver k) := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [counterObserver, trace_ctr] at hij
  omega

theorem counterObserver_licenses_every_target
    {V : Type w} (k : Nat) (P : Fin (k + 1) → V) :
    Licensed (counterObserver k) P :=
  licensed_of_injective (counterObserver_injective k) P

/-! ## Erased payloads and actual dependency-pair executions -/

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-- The rank computes the number of transitions of the dependency-pair machine. -/
theorem freeRecursor_dp_cost_eq_rank (t : RecursorTerm) :
    dpMachine.cost t = dpRank t := by
  cases t with
  | recR b s n => exact freeRecursor_dp_length b s n
  | _ => exact dpMachine.cost_terminal rfl

theorem freeRecursor_counter_licensed_for_dp_cost :
    Licensed dpRank dpMachine.cost := by
  intro x y hxy
  rw [freeRecursor_dp_cost_eq_rank, freeRecursor_dp_cost_eq_rank, hxy]

/-- The step count and final state belong to the same execution. -/
theorem freeRecursor_dp_execution (b s n : RecursorTerm) :
    dpMachine.Steps (deltaPrefix n) (.recR b s n) (.recR b s (stripDelta n)) := by
  simpa only [freeRecursor_dp_length, freeRecursor_dp_normalize] using
    dpMachine.normalizing_steps (.recR b s n)

theorem freeRecursor_dp_cost_payload_independent (b b' s s' n : RecursorTerm) :
    dpMachine.cost (.recR b s n) = dpMachine.cost (.recR b' s' n) := by
  rw [freeRecursor_dp_length, freeRecursor_dp_length]

/-- The payload is read from the term, independently of the rank observer. -/
def freeRecursorPayload : RecursorTerm → Option RecursorTerm
  | .recR _ s _ => some s
  | _ => none

theorem freeRecursor_rank_not_injective : ¬ Function.Injective dpRank := by
  intro hinj
  have h := hinj (show dpRank (.recR .void .void (.delta .void)) =
      dpRank (.recR .void (.delta .void) (.delta .void)) from rfl)
  cases h

theorem freeRecursor_counter_unlicensed_for_payload :
    ¬ Licensed dpRank freeRecursorPayload := by
  intro hlic
  have h := hlic (.recR .void .void (.delta .void))
    (.recR .void (.delta .void) (.delta .void)) rfl
  simp [freeRecursorPayload] at h

/-- Different payloads have equal positive execution costs and actual next calls. -/
theorem freeRecursor_erased_payload_execution_pair (b n : RecursorTerm) :
    (.recR b .void (.delta n) : RecursorTerm) ≠
        .recR b (.delta .void) (.delta n) ∧
      dpRank (.recR b .void (.delta n)) =
        dpRank (.recR b (.delta .void) (.delta n)) ∧
      dpMachine.cost (.recR b .void (.delta n)) = deltaPrefix n + 1 ∧
      dpMachine.cost (.recR b (.delta .void) (.delta n)) = deltaPrefix n + 1 ∧
      FreeRecursorDPPair (.recR b .void (.delta n)) (.recR b .void n) ∧
      FreeRecursorDPPair (.recR b (.delta .void) (.delta n))
        (.recR b (.delta .void) n) ∧
      dpMachine.Steps (deltaPrefix n + 1) (.recR b .void (.delta n))
        (.recR b .void (stripDelta n)) ∧
      dpMachine.Steps (deltaPrefix n + 1) (.recR b (.delta .void) (.delta n))
        (.recR b (.delta .void) (stripDelta n)) := by
  have hne : (.recR b .void (.delta n) : RecursorTerm) ≠
      .recR b (.delta .void) (.delta n) := by
    intro h
    cases h
  exact ⟨hne, rfl, freeRecursor_dp_length _ _ _, freeRecursor_dp_length _ _ _,
    .succ _ _ _, .succ _ _ _, freeRecursor_dp_execution b .void (.delta n),
    freeRecursor_dp_execution b (.delta .void) (.delta n)⟩

/-- A noninjective observer licenses actual call counts but not the erased payload. -/
theorem freeRecursor_lossy_execution_license :
    ¬ Function.Injective dpRank ∧ Licensed dpRank dpMachine.cost ∧
      ¬ Licensed dpRank freeRecursorPayload :=
  ⟨freeRecursor_rank_not_injective, freeRecursor_counter_licensed_for_dp_cost,
    freeRecursor_counter_unlicensed_for_payload⟩


/-! ## Actual termination under arbitrary payload-governed loop extensions -/

/-- The original calls remain, with self-loops on the payloads selected by P. -/
inductive PayloadLoopStep (P : RecursorTerm → Prop) : RecursorTerm → RecursorTerm → Prop
  | call {a b : RecursorTerm} : FreeRecursorDPPair a b → PayloadLoopStep P a b
  | payloadLoop (b s n : RecursorTerm) : P s →
      PayloadLoopStep P (.recR b s n) (.recR b s n)

def PayloadLoopBad (P : RecursorTerm → Prop) : RecursorTerm → Prop
  | .recR _ s _ => P s
  | _ => False

/-- Accessibility of the reversed actual transition relation. -/
def PayloadLoopTerminates (P : RecursorTerm → Prop) (t : RecursorTerm) : Prop :=
  Acc (fun a b => PayloadLoopStep P b a) t

theorem payloadLoop_bad_dp_iff {P : RecursorTerm → Prop} {a b : RecursorTerm}
    (h : FreeRecursorDPPair a b) : PayloadLoopBad P a ↔ PayloadLoopBad P b := by
  cases h
  rfl

theorem payloadLoop_self_of_bad {P : RecursorTerm → Prop} {t : RecursorTerm}
    (h : PayloadLoopBad P t) : PayloadLoopStep P t t := by
  cases t with
  | recR b s n => exact .payloadLoop b s n h
  | _ => exact False.elim h

theorem not_accessible_of_self_step {X : Type u} {R : X → X → Prop} {x : X}
    (h : R x x) : ¬ Acc (fun a b => R b a) x := by
  have hno : ∀ t, Acc (fun a b => R b a) t → ¬ R t t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hself
      exact ih t hself hself
  intro hx
  exact hno x hx h

theorem payloadLoop_terminates_of_not_bad (P : RecursorTerm → Prop) :
    ∀ t, ¬ PayloadLoopBad P t → PayloadLoopTerminates P t := by
  have aux : ∀ n : Nat, ∀ t, dpRank t = n → ¬ PayloadLoopBad P t →
      PayloadLoopTerminates P t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t hrank hsafe
      change Acc (fun a b => PayloadLoopStep P b a) t
      refine Acc.intro t ?_
      intro u hu
      cases hu with
      | call hdp =>
        have hlt : dpRank u < n := by
          have hdecrease := freeRecursor_dp_rank_decreases hdp
          omega
        apply ih (dpRank u) hlt u rfl
        exact fun hbad => hsafe ((payloadLoop_bad_dp_iff hdp).mpr hbad)
      | payloadLoop b s counter hP =>
        exact (hsafe hP).elim
  intro t hsafe
  exact aux (dpRank t) t rfl hsafe

/-- Every state either avoids all added loops or is itself an actual self-loop. -/
theorem payloadLoop_terminates_iff (P : RecursorTerm → Prop) (t : RecursorTerm) :
    PayloadLoopTerminates P t ↔ ¬ PayloadLoopBad P t := by
  constructor
  · intro hterm hbad
    exact not_accessible_of_self_step (payloadLoop_self_of_bad hbad) hterm
  · exact payloadLoop_terminates_of_not_bad P t

theorem payloadLoop_infinite_run {P : RecursorTerm → Prop} {t : RecursorTerm}
    (hbad : PayloadLoopBad P t) :
    ∃ run : Nat → RecursorTerm, run 0 = t ∧
      ∀ n, PayloadLoopStep P (run n) (run (n + 1)) :=
  ⟨fun _ => t, rfl, fun _ => payloadLoop_self_of_bad hbad⟩

/-- On all terms, rank licenses termination exactly when no payload acquires a loop. -/
theorem payloadLoop_licensed_iff_empty (P : RecursorTerm → Prop) :
    Licensed dpRank (PayloadLoopTerminates P) ↔ ∀ s, ¬ P s := by
  constructor
  · intro hlic s hs
    have hvoid : PayloadLoopTerminates P .void :=
      (payloadLoop_terminates_iff P .void).mpr (fun h => h)
    have heq : PayloadLoopTerminates P .void =
        PayloadLoopTerminates P (.recR .void s .void) :=
      hlic .void (.recR .void s .void) rfl
    have hrec : PayloadLoopTerminates P (.recR .void s .void) := Eq.mp heq hvoid
    exact ((payloadLoop_terminates_iff P _).mp hrec) hs
  · intro hnone
    have hall : ∀ t, PayloadLoopTerminates P t := by
      intro t
      apply (payloadLoop_terminates_iff P t).mpr
      cases t with
      | recR b s n => exact hnone s
      | _ => exact fun h => h
    intro x y _
    exact propext ⟨fun _ => hall y, fun _ => hall x⟩

/-- The ordinary rank-zero state terminates even when every payload acquires a loop. -/
theorem universal_payload_loops_rank_zero_collision :
    dpRank .void = dpRank (.recR .void .void .void) ∧
      PayloadLoopTerminates (fun _ => True) .void ∧
      ¬ PayloadLoopTerminates (fun _ => True) (.recR .void .void .void) := by
  refine ⟨rfl, (payloadLoop_terminates_iff _ _).mpr (fun h => h), ?_⟩
  intro h
  exact ((payloadLoop_terminates_iff _ _).mp h) True.intro

/-- Two recursor states share a positive counter and have opposite termination results. -/
theorem payloadSensitive_termination_collision (b n : RecursorTerm) :
    OperationallyInexpressibleAt dpRank
      (PayloadLoopTerminates (fun s => s = .delta .void))
      (.recR b .void (.delta n)) (.recR b (.delta .void) (.delta n)) := by
  have hleft : PayloadLoopTerminates (fun s => s = .delta .void)
      (.recR b .void (.delta n)) := by
    apply (payloadLoop_terminates_iff _ _).mpr
    intro h
    cases h
  have hright : ¬ PayloadLoopTerminates (fun s => s = .delta .void)
      (.recR b (.delta .void) (.delta n)) := by
    intro h
    exact ((payloadLoop_terminates_iff _ _).mp h) rfl
  exact ⟨rfl, fun heq => hright (Eq.mp heq hleft)⟩

theorem arbitrary_system_counter_unlicensed :
    ¬ Licensed dpRank (PayloadLoopTerminates (fun s => s = .delta .void)) := by
  intro hlic
  have h := payloadSensitive_termination_collision .void .void
  exact h.2 (hlic _ _ h.1)

/-- The positive state takes an actual call; the negative state has an actual infinite run. -/
theorem payloadSensitive_execution_witness (b n : RecursorTerm) :
    PayloadLoopStep (fun s => s = .delta .void)
      (.recR b .void (.delta n)) (.recR b .void n) ∧
      PayloadLoopTerminates (fun s => s = .delta .void) (.recR b .void (.delta n)) ∧
      ∃ run : Nat → RecursorTerm, run 0 = .recR b (.delta .void) (.delta n) ∧
        ∀ k, PayloadLoopStep (fun s => s = .delta .void) (run k) (run (k + 1)) := by
  refine ⟨.call (.succ _ _ _), ?_, ?_⟩
  · apply (payloadLoop_terminates_iff _ _).mpr
    intro h
    cases h
  · exact payloadLoop_infinite_run (P := fun s => s = .delta .void)
      (t := .recR b (.delta .void) (.delta n)) rfl


/-! ## Fixed-system termination and observer dependence -/

/-- A globally terminating relation has a constant termination verdict, so every
observer licenses that verdict. This does not attribute information to a counter. -/
theorem licensed_termination_of_wellFounded
    {X : Type u} {Q : Type v} (q : X → Q) (R : X → X → Prop)
    (hR : WellFounded (fun a b => R b a)) :
    Licensed q (fun x => Acc (fun a b => R b a) x) := by
  intro x y _
  exact propext ⟨fun _ => hR.apply y, fun _ => hR.apply x⟩

theorem freeRecursor_termination_everywhere (t : RecursorTerm) :
    Acc (fun a b => FreeRecursorDPPair b a) t :=
  freeRecursor_dp_rev_wellFounded.apply t

theorem freeRecursor_termination_licensed_by_every_observer
    {Q : Type v} (q : RecursorTerm → Q) :
    Licensed q (fun t => Acc (fun a b => FreeRecursorDPPair b a) t) :=
  licensed_termination_of_wellFounded q FreeRecursorDPPair freeRecursor_dp_rev_wellFounded

/-- The roadmap's scoped termination instance uses the actual dependency-pair relation. -/
theorem recursor_counter_licensed :
    Licensed dpRank (fun t => Acc (fun a b => FreeRecursorDPPair b a) t) :=
  freeRecursor_termination_licensed_by_every_observer dpRank

theorem payloadLoop_false_step_iff (a b : RecursorTerm) :
    PayloadLoopStep (fun _ => False) a b ↔ FreeRecursorDPPair a b := by
  constructor
  · intro h
    cases h with
    | call h => exact h
    | payloadLoop _ _ _ h => exact h.elim
  · exact PayloadLoopStep.call

theorem payloadLoop_false_termination_iff (t : RecursorTerm) :
    PayloadLoopTerminates (fun _ => False) t ↔
      Acc (fun a b => FreeRecursorDPPair b a) t := by
  have hrel : (fun a b => PayloadLoopStep (fun _ => False) b a) =
      (fun a b => FreeRecursorDPPair b a) := by
    funext a b
    exact propext (payloadLoop_false_step_iff b a)
  change Acc (fun a b => PayloadLoopStep (fun _ => False) b a) t ↔ _
  rw [hrel]

/-- On one carrier the counter licenses base-system termination but fails after
a payload-sensitive extension that retains every base dependency-pair step. -/
theorem counter_termination_scope_dichotomy :
    ¬ Function.Injective dpRank ∧
      Licensed dpRank (fun t => Acc (fun a b => FreeRecursorDPPair b a) t) ∧
      ¬ Licensed dpRank (PayloadLoopTerminates (fun s => s = .delta .void)) ∧
      ∀ a b, FreeRecursorDPPair a b →
        PayloadLoopStep (fun s => s = .delta .void) a b :=
  ⟨freeRecursor_rank_not_injective, recursor_counter_licensed,
    arbitrary_system_counter_unlicensed, fun _ _ h => PayloadLoopStep.call h⟩


end OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
