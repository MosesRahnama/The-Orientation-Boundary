import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# Sequential observation and retained memory

A finite observation history contains every earlier stage observation as a coordinate.
Consequently, licensing through any earlier stage transports to the retained history.
This remains true when the current observation later forgets a distinction.

No concrete rewrite system, recursor, or KO7 rule is imported.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u v w

/-- Retain all stage observations from zero through `horizon`. -/
def historyObserver {X : Type u} {Q : Type v}
    (q : Nat → X → Q) (horizon : Nat) (x : X) : Fin (horizon + 1) → Q :=
  fun i => q i.val x

/-- The retained history refines every stage observation that it contains. -/
theorem historyObserver_refines_stage
    {X : Type u} {Q : Type v}
    (q : Nat → X → Q) {stage horizon : Nat} (hstage : stage ≤ horizon) :
    ObserverRefines (historyObserver q horizon) (q stage) := by
  intro x y hxy
  exact congrFun hxy ⟨stage, Nat.lt_succ_iff.mpr hstage⟩

/-- The longer retained history refines the shorter one. -/
theorem historyObserver_refines_previous
    {X : Type u} {Q : Type v}
    (q : Nat → X → Q) (horizon : Nat) :
    ObserverRefines (historyObserver q (horizon + 1)) (historyObserver q horizon) := by
  intro x y hxy
  funext i
  exact congrFun hxy ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (horizon + 1))⟩

/-- A target licensed at any retained stage is licensed by the whole history. -/
theorem licensed_stage_implies_licensed_history
    {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V)
    {stage horizon : Nat} (hstage : stage ≤ horizon)
    (hlicensed : Licensed (q stage) P) :
    Licensed (historyObserver q horizon) P :=
  hlicensed.of_refinement (historyObserver_refines_stage q hstage)

/-- Once a retained history licenses a target, appending another stage cannot destroy that license. -/
theorem licensed_history_monotone
    {X : Type u} {Q : Type v} {V : Type w}
    (q : Nat → X → Q) (P : X → V) (horizon : Nat)
    (hlicensed : Licensed (historyObserver q horizon) P) :
    Licensed (historyObserver q (horizon + 1)) P :=
  hlicensed.of_refinement (historyObserver_refines_previous q horizon)

/-! ## Forgetting control -/

/-- Stage zero exposes the Boolean state; every later stage forgets it. -/
def forgettingObserver (stage : Nat) (x : Bool) : Bool :=
  if stage = 0 then x else false

/-- The identity target is licensed before forgetting. -/
theorem forgettingObserver_stage0_licenses_identity :
    Licensed (forgettingObserver 0) (fun x : Bool => x) := by
  intro x y hxy
  simpa [forgettingObserver] using hxy

/-- The current stage after forgetting no longer licenses the identity target. -/
theorem forgettingObserver_stage1_not_licensed :
    ¬ Licensed (forgettingObserver 1) (fun x : Bool => x) := by
  intro h
  have hbad : (false : Bool) = true := h false true (by simp [forgettingObserver])
  cases hbad

/-- Retaining the two-stage history preserves the distinction even though the current stage has
forgotten it. -/
theorem forgettingObserver_history1_licenses_identity :
    Licensed (historyObserver forgettingObserver 1) (fun x : Bool => x) :=
  licensed_stage_implies_licensed_history forgettingObserver (fun x : Bool => x)
    (stage := 0) (horizon := 1) (by omega)
    forgettingObserver_stage0_licenses_identity

/-- Without a refinement/compatibility requirement on current observations, licensing can be lost
at the current stage while retained history remains sufficient. -/
theorem current_observation_can_forget_while_history_retains :
    Licensed (forgettingObserver 0) (fun x : Bool => x) ∧
      ¬ Licensed (forgettingObserver 1) (fun x : Bool => x) ∧
      Licensed (historyObserver forgettingObserver 1) (fun x : Bool => x) :=
  ⟨forgettingObserver_stage0_licenses_identity,
    forgettingObserver_stage1_not_licensed,
    forgettingObserver_history1_licenses_identity⟩

end OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery
