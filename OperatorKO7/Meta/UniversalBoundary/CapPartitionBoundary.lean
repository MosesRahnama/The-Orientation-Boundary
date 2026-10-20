import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# CAP partition boundary as an observer collision

The Gilbert and Lynch (SIGACT News 33(2), 2002) partition argument is ESTABLISHED. This module proves
the two-replica, one-write, one-read instance and cites that general statement. It does not prove the
full asynchronous network theorem.

Two replicas `n1` and `n2` hold a value of type `Val` with distinguished initial value `v₀`. A run is
`Run := { wrote : Bool, partitioned : Bool }`: whether a client wrote a new value `v₁` (`v₁ ≠ v₀`) at
`n1` before the read, and whether the link between the replicas was cut for the whole run. Replica
`n2`'s local history is the list of messages it received: `[]` when partitioned, `[v₁]` when not
partitioned and the write happened, else `[]`. A responder is a function
`respond : List Val → Option Val`; `none` is the typed halt "unavailable".

Availability requires an answer on every history. Consistency on a set of runs requires that answer
to equal the latest value. The two partitioned runs present the same empty history and, when
`v₁ ≠ v₀`, different latest values, so no responder is both available and consistent on the
partitioned set.

The lift is a healed partition: the write's message is the licensed channel, and history determines
the latest value on unpartitioned runs. The refusal keeps the partition and declines the empty
history instead of guessing.

Relation: OperationallyInexpressibleAt / FactorsThrough for history versus latest;
          LicensedOn for the unpartitioned repair; TypedBoundary for the Boolean fixture.
Closure: not applicable; no rewriting closure is claimed.
Strategy: direct finite case analysis on the two Boolean run fields.
Trust: some theorems use the baseline axiom propext; none introduce user axioms. The historical CAP
       result is ESTABLISHED and cited, not assumed.
Scope: the deterministic Run model above, arbitrary Val for the generic theorems, and the Boolean
       instance v₀ = false, v₁ = true for capBoundary.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.CapPartitionBoundary

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-! ## NameGate: imported boundary and observer API -/

#check @TypedBoundary
#check @TypedBoundary.verdict_not_observation_function
#check @OperationallyInexpressibleAt
#check @FactorsThrough
#check @not_factorsThrough_of_collision
#check @Licensed
#check @LicensedOn

universe u

/-- A reduced CAP run: whether the new value was written, and whether the answering replica is
partitioned from the write. -/
structure Run where
  wrote : Bool
  partitioned : Bool

/-- The value history visible to the responder. During a partition the visible history is empty;
without a partition it contains the new value exactly when the write completed. -/
def history {Val : Type u} (v₁ : Val) (r : Run) : List Val :=
  if r.partitioned then [] else if r.wrote then [v₁] else []

/-- The latest value required by the consistency condition. -/
def latest {Val : Type u} (v₀ v₁ : Val) (r : Run) : Val :=
  if r.wrote then v₁ else v₀

/-- Availability in this reduced model: the responder returns some value on every possible history. -/
def Available {Val : Type u} (respond : List Val → Option Val) : Prop :=
  ∀ h, (respond h).isSome

/-- Consistency on a selected set of runs: every selected run receives exactly its latest value. -/
def Consistent {Val : Type u} (v₀ v₁ : Val) (respond : List Val → Option Val)
    (S : Set Run) : Prop :=
  ∀ r ∈ S, respond (history v₁ r) = some (latest v₀ v₁ r)


/-! ## Partition collision and the CAP obstruction -/

/--
Proves: the two partitioned runs with and without the write have equal histories and different latest values.
Does not prove: a general CAP theorem outside the reduced Run model.
Relation: OperationallyInexpressibleAt (history v₁) (latest v₀ v₁).
Closure: not applicable.
Strategy: unfold the two concrete Boolean runs.
Trust: baseline propext.
Scope: arbitrary value type, assuming v₁ ≠ v₀.
-/
theorem partition_collision {Val : Type u} {v₀ v₁ : Val} (hv : v₁ ≠ v₀) :
    OperationallyInexpressibleAt (history v₁) (latest v₀ v₁)
      ⟨true, true⟩ ⟨false, true⟩ := by
  constructor
  · rfl
  · simpa [latest] using hv

/--
Proves: the latest-value target does not factor through visible history when the two values differ.
Does not prove: non-factorization for richer observers that retain the write across the partition.
Relation: FactorsThrough (history v₁) (latest v₀ v₁).
Closure: not applicable.
Strategy: apply not_factorsThrough_of_collision to partition_collision.
Trust: baseline propext, from partition_collision.
Scope: arbitrary value type, assuming v₁ ≠ v₀.
-/
theorem history_does_not_license_latest {Val : Type u} {v₀ v₁ : Val} (hv : v₁ ≠ v₀) :
    ¬ FactorsThrough (history v₁) (latest v₀ v₁) :=
  not_factorsThrough_of_collision (partition_collision hv)

/--
Proves: no responder is both available on every history and consistent on every partitioned run.
Does not prove: the full asynchronous distributed CAP theorem or any probabilistic impossibility.
Relation: conjunction of Available respond and Consistent v₀ v₁ respond on partitioned runs.
Closure: not applicable.
Strategy: both partitioned runs present the empty history; availability fixes an answer and consistency forces it to equal both values.
Trust: baseline propext.
Scope: every responder List Val → Option Val, arbitrary value type, assuming v₁ ≠ v₀.
-/
theorem cap {Val : Type u} {v₀ v₁ : Val} (hv : v₁ ≠ v₀)
    (respond : List Val → Option Val) :
    ¬ (Available respond ∧
      Consistent v₀ v₁ respond {r : Run | r.partitioned = true}) := by
  rintro ⟨hAvail, hCons⟩
  have hempty := hAvail ([] : List Val)
  cases hresp : respond [] with
  | none =>
      simp [hresp] at hempty
  | some v =>
      have hWritten := hCons ⟨true, true⟩ (by rfl)
      have hUnwritten := hCons ⟨false, true⟩ (by rfl)
      simp [history, latest, hresp] at hWritten hUnwritten
      exact hv (hWritten.symm.trans hUnwritten)

/-! Gate R5: the common inequality premise is inhabited at the exact theorem domain. -/

/--
Proves: the Boolean old and new values used by capBoundary are distinct.
Does not prove: any property of an arbitrary value type.
Relation: inequality of true and false.
Closure: not applicable.
Strategy: closed Boolean decision.
Trust: kernel-only.
Scope: the exact Boolean value domain used by capBoundary.
-/
private theorem value_inequality_nonvacuity : (true : Bool) ≠ false := by decide


/-! ## Lift: remove the partition -/

/--
Proves: visible history licenses the latest value on every unpartitioned run.
Does not prove: that the inequality premise is needed; this structural repair is valid even when v₁ = v₀.
Relation: LicensedOn unpartitioned runs (history v₁) (latest v₀ v₁).
Closure: not applicable.
Strategy: split on the two write bits after fixing partitioned = false.
Trust: baseline propext; the v₁ ≠ v₀ premise is requested by the instance and is unused here.
Scope: arbitrary value type; the requested v₁ ≠ v₀ premise records the same nondegenerate CAP instance but is non-load-bearing here.
-/
theorem healed_licenses {Val : Type u} {v₀ v₁ : Val} (_hv : v₁ ≠ v₀) :
    LicensedOn {r : Run | r.partitioned = false} (history v₁) (latest v₀ v₁) := by
  intro x hx y hy hxy
  rcases x with ⟨xw, xp⟩
  rcases y with ⟨yw, yp⟩
  change xp = false at hx
  change yp = false at hy
  subst xp
  subst yp
  cases xw <;> cases yw <;> simp [history, latest] at hxy ⊢

/-- A total healed responder: return the head of the visible history, defaulting to the old value. -/
def respondHealed {Val : Type u} (v₀ : Val) (h : List Val) : Option Val :=
  some (h.headD v₀)

/--
Proves: respondHealed is consistent on every unpartitioned run.
Does not prove: consistency on partitioned runs.
Relation: Consistent v₀ v₁ (respondHealed v₀) on the set partitioned = false.
Closure: not applicable.
Strategy: fix partitioned = false and split on wrote.
Trust: kernel-only; definitional reduction.
Scope: arbitrary value type and arbitrary old and new values.
-/
theorem respondHealed_consistent_unpartitioned {Val : Type u} (v₀ v₁ : Val) :
    Consistent v₀ v₁ (respondHealed v₀) {r : Run | r.partitioned = false} := by
  intro r hr
  rcases r with ⟨wrote, partitioned⟩
  change partitioned = false at hr
  subst partitioned
  cases wrote <;> rfl

/--
Proves: respondHealed returns some value on every history.
Does not prove: that its returned value is consistent on partitioned runs.
Relation: Available (respondHealed v₀).
Closure: not applicable.
Strategy: unfold one total Option constructor.
Trust: kernel-only; definitional reduction.
Scope: arbitrary value type and old value.
-/
theorem respondHealed_available {Val : Type u} (v₀ : Val) :
    Available (respondHealed v₀) := by
  intro h
  rfl

/-! ## Refusal: decline histories that cannot determine the latest value -/

/-- A refusing responder: decline the empty history; otherwise return its first visible value. -/
def respondRefuse {Val : Type u} : List Val → Option Val
  | [] => none
  | v :: _ => some v

/--
Proves: respondRefuse answers exactly on unpartitioned runs whose write completed.
Does not prove: consistency; it identifies the exact run set on which an answer exists.
Relation: Option.isSome for respondRefuse (history v₁ r).
Closure: not applicable.
Strategy: split on partitioned and wrote.
Trust: baseline propext from Boolean and Option reduction.
Scope: arbitrary value type and new value.
-/
private theorem respondRefuse_isSome_iff_answeringRun {Val : Type u} (v₁ : Val) (r : Run) :
    (respondRefuse (history v₁ r)).isSome ↔
      r.partitioned = false ∧ r.wrote = true := by
  rcases r with ⟨wrote, partitioned⟩
  cases partitioned <;> cases wrote <;> simp [respondRefuse, history]

/--
Proves: whenever respondRefuse answers, that answer equals the latest value.
Does not prove: availability; the empty history is intentionally refused.
Relation: respondRefuse (history v₁ r) = some (latest v₀ v₁ r) under the answer-given predicate.
Closure: not applicable.
Strategy: use the exact answering set partitioned = false and wrote = true, then reduce.
Trust: baseline propext.
Scope: every run; the answer-given set is exactly {r | r.partitioned = false ∧ r.wrote = true}.
-/
theorem respondRefuse_consistent_when_answering {Val : Type u} (v₀ v₁ : Val) :
    ∀ r, (respondRefuse (history v₁ r)).isSome →
      respondRefuse (history v₁ r) = some (latest v₀ v₁ r) := by
  intro r hAnswer
  have hr := (respondRefuse_isSome_iff_answeringRun v₁ r).1 hAnswer
  rcases r with ⟨wrote, partitioned⟩
  change partitioned = false ∧ wrote = true at hr
  rcases hr with ⟨hp, hw⟩
  subst partitioned
  subst wrote
  rfl

/--
Proves: respondRefuse is not available because it refuses the empty history.
Does not prove: any failure of consistency on histories where it answers.
Relation: negation of Available respondRefuse.
Closure: not applicable.
Strategy: instantiate availability at the empty history.
Trust: baseline propext.
Scope: arbitrary value type.
-/
theorem respondRefuse_not_available {Val : Type u} :
    ¬ Available (respondRefuse : List Val → Option Val) := by
  intro hAvailable
  have hEmpty := hAvailable ([] : List Val)
  simp [respondRefuse] at hEmpty

/-! Gate R5: the refusal theorem's answer-given premise is inhabited at the exact run domain. -/

/--
Proves: respondRefuse answers on the concrete unpartitioned run whose write completed.
Does not prove: availability on the empty history.
Relation: Option.isSome for respondRefuse after history true.
Closure: not applicable.
Strategy: definitional reduction on the concrete run.
Trust: kernel-only.
Scope: the exact Boolean run { wrote := true, partitioned := false }.
-/
private theorem refusal_answer_nonvacuity :
    (respondRefuse (history true (⟨true, false⟩ : Run))).isSome := by
  rfl


/-! ## The concrete CAP collision as a universal boundary -/

/-- The Boolean CAP collision packaged as a TypedBoundary: both partitioned runs expose the empty
history, while the latest-value verdict records whether the write completed. -/
def capBoundary : TypedBoundary where
  State := Run
  Obs := List Bool
  Verdict := Bool
  observe := history true
  verdict := latest false true
  s₁ := ⟨true, true⟩
  s₂ := ⟨false, true⟩
  obs_eq := by decide
  verdict_ne := by decide

/--
Proves: the Boolean CAP latest-value verdict is not a function of the visible history.
Does not prove: the full CAP theorem for arbitrary distributed protocols.
Relation: TypedBoundary.verdict_not_observation_function capBoundary.
Closure: not applicable.
Strategy: one application of the imported universal boundary law.
Trust: kernel-only; the boundary fixture is closed and its collision fields are decide-checked.
Scope: the Boolean instance v₀ = false, v₁ = true of the reduced Run model.
-/
theorem capBoundary_obeys_law :
    ¬ ∃ f : capBoundary.Obs → capBoundary.Verdict,
      ∀ s : capBoundary.State,
        capBoundary.verdict s = f (capBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function capBoundary

/-! ## Axiom audit -/

#print axioms partition_collision
#print axioms history_does_not_license_latest
#print axioms cap
#print axioms healed_licenses
#print axioms respondHealed_consistent_unpartitioned
#print axioms respondHealed_available
#print axioms respondRefuse_consistent_when_answering
#print axioms respondRefuse_not_available
#print axioms capBoundary_obeys_law

end OperatorKO7.Meta.UniversalBoundary.CapPartitionBoundary
