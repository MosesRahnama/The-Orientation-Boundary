import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore

/-!
# Three-node Byzantine agreement boundary

The model has one commander and two symmetric lieutenants. Values are `Bool`. In round one the
commander sends one value to each lieutenant. In round two each lieutenant relays to the other the
value received from the commander. A loyal node sends the protocol value; the single traitor may
send any value. A lieutenant observes the pair consisting of the commander's message and the other
lieutenant's relay. Both loyal lieutenants use one decision function on that view.

The general three-node, one-traitor impossibility is ESTABLISHED by Pease, Shostak and Lamport
(JACM 27(2), 1980), with the three-scenario argument also given by Fischer, Lynch and Merritt
(Distributed Computing 1, 1986). This module proves the one-relay-round instance directly. The
positive four-node result is not proved here; Algorithm OM(1) is ESTABLISHED by Lamport, Shostak
and Pease (1982).

Relation: equality on lieutenant-view fibers and the IC1/IC2 protocol requirements.
Closure: one commander-send round followed by one lieutenant-relay round.
Strategy: explicit three-scenario collision and contradiction.
Trust: kernel-checked definitions and finite `decide` facts under the project baseline.
Scope: three nodes, one traitor, oral messages, one relay round, symmetric lieutenant decision rule.
-/

set_option autoImplicit false

#check @OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary
#check @OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary.verdict_not_observation_function
#check @OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary.OperationallyInexpressibleAt
#check @OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.FactorsThrough
#check @OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary.not_factorsThrough_of_collision

namespace OperatorKO7.Meta.UniversalBoundary.ByzantineThreeNodeBoundary

/-- The local view of one lieutenant: commander's value, then the other lieutenant's relay. -/
abbrev View := Bool × Bool

/-- One complete channel assignment with exactly one designated traitor.
Traitor index 0 is the commander, 1 is L1, and 2 is L2. -/
structure Scenario where
  cToL1 : Bool
  cToL2 : Bool
  l1ToL2 : Bool
  l2ToL1 : Bool
  traitor : Fin 3

/-- L1's local view. -/
def viewL1 (s : Scenario) : View :=
  (s.cToL1, s.l2ToL1)

/-- L2's local view. -/
def viewL2 (s : Scenario) : View :=
  (s.cToL2, s.l1ToL2)

/-- Loyal nodes preserve their prescribed channel behavior. -/
def Loyal (s : Scenario) : Prop :=
  (s.traitor ≠ 0 → s.cToL1 = s.cToL2) ∧
  (s.traitor ≠ 1 → s.l1ToL2 = s.cToL1) ∧
  (s.traitor ≠ 2 → s.l2ToL1 = s.cToL2)

/-- Decidable Boolean form of `Loyal`. -/
def loyal? (s : Scenario) : Bool :=
  @decide (Loyal s) (by
    unfold Loyal
    infer_instance)

/--
Proves: the Boolean loyalty test is true exactly for loyal channel assignments.
Does not prove: that every arbitrary channel assignment is loyal.
Relation: logical equivalence between `loyal?` and `Loyal`.
Closure: not applicable.
Strategy: reduction of the decidable Boolean test.
Trust: kernel reduction and the ordinary `Decidable` instance only.
Scope: every `Scenario` in the three-node one-traitor model.
-/
theorem loyal?_iff (s : Scenario) : loyal? s = true ↔ Loyal s := by
  simp [loyal?]

/-- Loyal commander with command value true; L2 is the traitor and relays false to L1. -/
def sA : Scenario where
  cToL1 := true
  cToL2 := true
  l1ToL2 := true
  l2ToL1 := false
  traitor := 2

/-- Traitor commander sends true to L1 and false to L2; both lieutenants are loyal. -/
def sB : Scenario where
  cToL1 := true
  cToL2 := false
  l1ToL2 := true
  l2ToL1 := false
  traitor := 0

/-- Loyal commander with command value false; L1 is the traitor and relays true to L2. -/
def sC : Scenario where
  cToL1 := false
  cToL2 := false
  l1ToL2 := true
  l2ToL1 := false
  traitor := 1

/--
Proves: L1 has exactly the same local view in scenarios sA and sB.
Does not prove: that the full channel assignments sA and sB are equal.
Relation: equality of `viewL1` observations.
Closure: one commander-send round and one relay round.
Strategy: finite reduction of the two explicit scenarios.
Trust: kernel-checked `decide`.
Scope: the named scenarios sA and sB only.
-/
theorem viewL1_sA_eq_sB : viewL1 sA = viewL1 sB := by
  decide

/--
Proves: L2 has exactly the same local view in scenarios sB and sC.
Does not prove: that the full channel assignments sB and sC are equal.
Relation: equality of `viewL2` observations.
Closure: one commander-send round and one relay round.
Strategy: finite reduction of the two explicit scenarios.
Trust: kernel-checked `decide`.
Scope: the named scenarios sB and sC only.
-/
theorem viewL2_sB_eq_sC : viewL2 sB = viewL2 sC := by
  decide

/-- Interactive consistency condition IC2: a loyal commander fixes every loyal lieutenant's decision. -/
def IC2 (d : View → Bool) : Prop :=
  ∀ s, Loyal s → s.traitor ≠ 0 →
    (s.traitor ≠ 1 → d (viewL1 s) = s.cToL1) ∧
    (s.traitor ≠ 2 → d (viewL2 s) = s.cToL2)

/-- Interactive consistency condition IC1 for the only case used by the impossibility chain:
when the commander is the traitor, both loyal lieutenants decide the same value. -/
def IC1 (d : View → Bool) : Prop :=
  ∀ s, Loyal s → s.traitor = 0 → d (viewL1 s) = d (viewL2 s)

/-- The decision directly required of L1 when the commander is loyal, and no requirement otherwise.
This helper records the direct IC2 obligation but is not the framework verdict. -/
def required1 (s : Scenario) : Option Bool :=
  if s.traitor = 0 then none else some s.cToL1

/-- The commander's value as seen by L2, used as the framework target verdict. -/
def commanderValueSeenByL2 (s : Scenario) : Bool :=
  s.cToL2

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/--
Proves: sA and sB collide on L1's view while their L2-seen commander values differ.
Does not prove: the full Byzantine impossibility by itself.
Relation: `OperationallyInexpressibleAt viewL1 (fun s => s.cToL2)`.
Closure: one commander-send round and one relay round.
Strategy: explicit collision using the named scenarios sA and sB.
Trust: kernel proof plus a finite `decide` inequality.
Scope: the one-relay three-node scenarios sA and sB.
-/
theorem l1_collision :
    OperationallyInexpressibleAt viewL1 (fun s => s.cToL2) sA sB := by
  exact ⟨viewL1_sA_eq_sB, by decide⟩

/--
Proves: L2's commander value cannot factor through L1's local view.
Does not prove: that no richer observation can recover that target.
Relation: `FactorsThrough viewL1 (fun s => s.cToL2)`.
Closure: all scenarios, refuted by the explicit sA/sB fiber collision.
Strategy: apply the general collision-to-nonfactorization theorem.
Trust: kernel proof using the imported observer-target core theorem.
Scope: the `Scenario` carrier and L1 observation channel of this module.
-/
theorem view_does_not_license :
    ¬ FactorsThrough viewL1 (fun s => s.cToL2) :=
  not_factorsThrough_of_collision l1_collision

/--
Proves: no symmetric one-round decision function satisfies both IC1 and IC2 for all scenarios.
Does not prove: Byzantine impossibility for arbitrary node counts or arbitrary communication rounds.
Relation: conjunction of the module's IC1 agreement and IC2 loyal-commander requirements.
Closure: one commander-send round followed by one lieutenant-relay round.
Strategy: chain IC2 at sA, IC1 at sB, and IC2 at sC through the two equal-view equations.
Trust: kernel proof with finite `decide` facts only for the three explicit scenarios.
Scope: every decision function `d : View → Bool` on the three-node one-relay model.
-/
theorem byzantine_three_node_impossible :
    ∀ d : View → Bool, ¬ (IC1 d ∧ IC2 d) := by
  intro d hBoth
  rcases hBoth with ⟨hIC1, hIC2⟩
  have hLoyalA : Loyal sA := (loyal?_iff sA).1 (by decide)
  have hLoyalB : Loyal sB := (loyal?_iff sB).1 (by decide)
  have hLoyalC : Loyal sC := (loyal?_iff sC).1 (by decide)
  have hA := (hIC2 sA hLoyalA (by decide)).1 (by decide)
  change d (viewL1 sA) = true at hA
  have hB := hIC1 sB hLoyalB rfl
  have hC := (hIC2 sC hLoyalC (by decide)).2 (by decide)
  change d (viewL2 sC) = false at hC
  have hLeft : d (viewL1 sB) = true := by
    rw [← viewL1_sA_eq_sB]
    exact hA
  have hRight : d (viewL2 sB) = false := by
    rw [viewL2_sB_eq_sC]
    exact hC
  have hTrueFalse : true = false :=
    hLeft.symm.trans (hB.trans hRight)
  cases hTrueFalse

/--
Proves: the same universal one-round impossibility as `byzantine_three_node_impossible`.
Does not prove: a stronger multi-round or four-node impossibility.
Relation: conjunction of IC1 and IC2 over `Scenario`.
Closure: one commander-send round followed by one lieutenant-relay round.
Strategy: restrict IC1 and IC2 to sA, sB, sC, then `decide` every 4-bit table for `d`.
Trust: kernel-checked `decide` on the sixteen Boolean decision tables.
Scope: every decision function `d : View → Bool`.
-/
theorem byzantine_three_node_impossible' :
    ∀ d : View → Bool, ¬ (IC1 d ∧ IC2 d) := by
  intro d ⟨hIC1, hIC2⟩
  have hLoyalA : Loyal sA := (loyal?_iff sA).1 (by decide)
  have hLoyalB : Loyal sB := (loyal?_iff sB).1 (by decide)
  have hLoyalC : Loyal sC := (loyal?_iff sC).1 (by decide)
  have hA : d (true, false) = true := (hIC2 sA hLoyalA (by decide)).1 (by decide)
  have hC : d (false, true) = false := (hIC2 sC hLoyalC (by decide)).2 (by decide)
  have hB : d (true, false) = d (false, true) := hIC1 sB hLoyalB rfl
  have hunsat :
      ∀ (b00 b01 b10 b11 : Bool),
        b10 = true → b01 = false → b10 = b01 → False := by
    decide
  exact hunsat (d (false, false)) (d (false, true)) (d (true, false)) (d (true, true))
    hA hC hB

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-- The sA/sB L1-view collision packaged as the framework's universal typed boundary. -/
def byzantineBoundary : TypedBoundary where
  State := Scenario
  Obs := View
  Verdict := Bool
  observe := viewL1
  verdict := fun s => s.cToL2
  s₁ := sA
  s₂ := sB
  obs_eq := viewL1_sA_eq_sB
  verdict_ne := by decide

/--
Proves: the Byzantine view collision obeys the universal no-observation-only-verdict law.
Does not prove: the protocol impossibility without the separate IC1 and IC2 requirements.
Relation: the `byzantineBoundary` observation fiber and its Boolean verdict.
Closure: all states of the boundary carrier.
Strategy: instantiate `TypedBoundary.verdict_not_observation_function`.
Trust: kernel proof using the imported universal boundary theorem.
Scope: the concrete `byzantineBoundary` built from sA and sB.
-/
theorem byzantineBoundary_obeys_law :
    ¬ ∃ f : byzantineBoundary.Obs → byzantineBoundary.Verdict,
      ∀ s : byzantineBoundary.State,
        byzantineBoundary.verdict s = f (byzantineBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function byzantineBoundary

/--
Proves: scenario sA satisfies the loyal-node channel constraints.
Does not prove: that its designated traitor L2 follows any loyal constraint.
Relation: `Loyal sA`.
Closure: the four channels of the named one-round scenario.
Strategy: unfold the loyalty predicate and decide the closed finite proposition.
Trust: kernel-checked `decide`.
Scope: scenario sA only.
-/
theorem loyal_sA : Loyal sA := by
  unfold Loyal
  decide

/--
Proves: scenario sB satisfies the loyal-node channel constraints.
Does not prove: that its designated traitor commander follows any loyal constraint.
Relation: `Loyal sB`.
Closure: the four channels of the named one-round scenario.
Strategy: unfold the loyalty predicate and decide the closed finite proposition.
Trust: kernel-checked `decide`.
Scope: scenario sB only.
-/
theorem loyal_sB : Loyal sB := by
  unfold Loyal
  decide

/--
Proves: scenario sC satisfies the loyal-node channel constraints.
Does not prove: that its designated traitor L1 follows any loyal constraint.
Relation: `Loyal sC`.
Closure: the four channels of the named one-round scenario.
Strategy: unfold the loyalty predicate and decide the closed finite proposition.
Trust: kernel-checked `decide`.
Scope: scenario sC only.
-/
theorem loyal_sC : Loyal sC := by
  unfold Loyal
  decide

/--
Proves: IC2 alone is satisfiable by the decision rule that returns the commander's received value.
Does not prove: that this decision rule also satisfies IC1.
Relation: `IC2 Prod.fst`.
Closure: every scenario satisfying the loyal-commander hypotheses of IC2.
Strategy: choose `Prod.fst` and reduce each local view projection.
Trust: kernel proof by definitional equality.
Scope: the full `Scenario` carrier for IC2 alone.
-/
theorem exists_d_IC2_only : ∃ d : View → Bool, IC2 d := by
  refine ⟨Prod.fst, ?_⟩
  intro s _hLoyal _hCommander
  constructor
  · intro _hL1
    rfl
  · intro _hL2
    rfl

/--
Proves: the first-projection decision rule fails IC1, witnessed at scenario sB.
Does not prove: that every decision rule fails IC1.
Relation: negation of `IC1 Prod.fst`.
Closure: the universal IC1 condition, refuted at one explicit scenario.
Strategy: specialize IC1 at loyal scenario sB and reduce the two views to true and false.
Trust: kernel proof using `loyal_sB` and Boolean constructor disjointness.
Scope: `Prod.fst : View → Bool` and the named scenario sB.
-/
theorem fst_fails_IC1_at_sB : ¬ IC1 Prod.fst := by
  intro hIC1
  have hEq := hIC1 sB loyal_sB rfl
  change true = false at hEq
  cases hEq

end OperatorKO7.Meta.UniversalBoundary.ByzantineThreeNodeBoundary
