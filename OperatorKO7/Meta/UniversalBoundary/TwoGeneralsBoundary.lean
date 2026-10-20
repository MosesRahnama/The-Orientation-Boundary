import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore

/-!
# Two Generals as a chain of fiber collisions

The coordinated-attack impossibility is ESTABLISHED (Akkoyunlu, Ekanadham and Huber
1975; Gray 1978). This module proves it in the standard reduced model below and
cites that result. It does not prove a new impossibility, and it does not prove
any repair.

Reduced model. Messages alternate: message `i` (counting from `1`) is sent by
general A when `i` is odd and by general B when `i` is even, and each message
is sent only after the previous one arrived. A run is the number `k` of
messages delivered before the first loss, `0 ≤ k ≤ n` for a protocol of `n`
messages. A's view in run `k` is the number of messages A received, `k / 2`;
B's view is `(k + 1) / 2`. Each general decides from its view alone.

At every rung the sender of the next message has the same view whether or not
that message arrives, so its decision cannot depend on the delivery fact it
needs. The first-message collision is packaged as `twoGeneralsBoundary`. The
capstone `two_generals_impossible` is the downward induction of those rungs
against agreement, validity, and no-information-no-attack together.

The probabilistic repair (agreement with probability arbitrarily close to one)
is ESTABLISHED and is the lift of this boundary; it is not proved here. The
bounded-delay repair (a known delay bound that turns silence into a timeout)
is ESTABLISHED and is the refusal of this boundary; it is not proved here.

```
Relation: OperationallyInexpressibleAt / FactorsThrough on senderView versus
          delivered; TypedBoundary.verdict_not_observation_function on the
          first-message rung; Boolean equality of dA / dB on views.
Closure:  not applicable; no rewriting closure is claimed.
Strategy: downward induction on the undelivered suffix of a finite alternating
          protocol; not a rewriting strategy.
Trust:    kernel-only on this module; the historical impossibility is
          ESTABLISHED and cited, not taken as an axiom.
Scope:    the reduced finite deterministic lossy-link model stated above.
          No probabilistic protocol, no bounded-delay channel, no crash-fault
          model, and no more than two parties.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.TwoGeneralsBoundary

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-! ## NameGate: imported collision and boundary API -/

#check @TypedBoundary
#check @TypedBoundary.verdict_not_observation_function
#check @OperationallyInexpressibleAt
#check @not_factorsThrough_of_collision
#check @FactorsThrough

/-! ## Views and sender identity -/

/-- A's view in run `k`: the number of messages A received, `k / 2`. -/
def viewA (k : Nat) : Nat := k / 2

/-- B's view in run `k`: the number of messages B received, `(k + 1) / 2`. -/
def viewB (k : Nat) : Nat := (k + 1) / 2

/-- `true` when general A sends message `i` (odd `i`); `false` when B sends. -/
def sender (i : Nat) : Bool := decide (i % 2 = 1)

/-- The view of the general who sends message `i`, evaluated in run `k`. -/
def senderView (i k : Nat) : Nat := if sender i then viewA k else viewB k

example : viewA 0 = 0 := rfl
example : viewA 1 = 0 := rfl
example : viewB 0 = 0 := rfl
example : viewB 1 = 1 := rfl
example : sender 1 = true := rfl
example : sender 2 = false := rfl

/--
Proves: the sender of message `k + 1` has the same view in run `k + 1` and in
run `k`.
Does not prove: anything about the other general's view, and nothing about
delivery of any message other than `k + 1`.
Relation: equality of `senderView (k + 1)` at the two runs.
Closure: not applicable.
Strategy: case on the parity of `k`, then `omega` on integer division.
Trust: baseline `{propext, Quot.sound}` from `omega`; no `Classical.choice`.
Scope: every `k : Nat` in the reduced alternating model.
-/
theorem sender_view_eq (k : Nat) :
    senderView (k + 1) (k + 1) = senderView (k + 1) k := by
  unfold senderView sender viewA viewB
  by_cases h : (k + 1) % 2 = 1
  · simp [h]
    omega
  · simp [h]
    omega

/-! ## Rung collision: same sender view, different delivery fact -/

/-- Message `i` arrived in run `k`. -/
def delivered (i k : Nat) : Bool := decide (i ≤ k)

example : delivered 1 1 = true := rfl
example : delivered 1 0 = false := rfl

/--
Proves: runs `k + 1` and `k` collide for the sender of message `k + 1`: the
sender view is equal and the delivery of that message differs.
Does not prove: that the other general's view collides, and nothing about a
protocol decision function.
Relation: `OperationallyInexpressibleAt (senderView (k + 1)) (delivered (k + 1))`.
Closure: not applicable.
Strategy: `sender_view_eq` plus the closed facts `k + 1 ≤ k + 1` and
`¬ k + 1 ≤ k`.
Trust: baseline `{propext, Quot.sound}` inherited from `sender_view_eq`; no
`Classical.choice`.
Scope: every rung `k` of the reduced alternating model.
-/
theorem rung_collision (k : Nat) :
    OperationallyInexpressibleAt (senderView (k + 1)) (delivered (k + 1))
      (k + 1) k := by
  refine ⟨sender_view_eq k, ?_⟩
  unfold delivered
  have htrue : decide (k + 1 ≤ k + 1) = true := decide_eq_true (Nat.le_refl (k + 1))
  have hfalse : decide (k + 1 ≤ k) = false :=
    decide_eq_false (Nat.not_succ_le_self k)
  rw [htrue, hfalse]
  decide

/--
Proves: delivery of message `k + 1` does not factor through the sender's view.
Does not prove: that no protocol exists; that is the capstone, after agreement
is imposed across both generals.
Relation: `FactorsThrough (senderView (k + 1)) (delivered (k + 1))`.
Closure: not applicable.
Strategy: `not_factorsThrough_of_collision` at `rung_collision`.
Trust: baseline `{propext, Quot.sound}` inherited from `rung_collision`; the
imported collision lemma is constructive.
Scope: every rung `k` of the reduced alternating model.
-/
theorem sender_cannot_know (k : Nat) :
    ¬ FactorsThrough (senderView (k + 1)) (delivered (k + 1)) :=
  not_factorsThrough_of_collision (rung_collision k)

/-! ## Finite deterministic protocols -/

/-- A finite alternating protocol of `n` messages with view-only decisions. -/
structure Protocol where
  n : Nat
  dA : Nat → Bool
  dB : Nat → Bool

/-- Both generals output the same decision in every run `k ≤ n`. -/
def Agreement (P : Protocol) : Prop :=
  ∀ k, k ≤ P.n → P.dA (viewA k) = P.dB (viewB k)

/-- With every message delivered, A attacks. -/
def Validity (P : Protocol) : Prop :=
  P.dA (viewA P.n) = true

/-- B received nothing, so B does not attack. -/
def NoInformationNoAttack (P : Protocol) : Prop :=
  P.dB (viewB 0) = false

/--
Proves: agreement plus validity forces both generals to attack in every run
`k ≤ P.n`.
Does not prove: the capstone contradiction; `NoInformationNoAttack` is unused.
Relation: Boolean equality of `dA (viewA k)` and `dB (viewB k)` with `true`.
Closure: not applicable.
Strategy: induction on the undelivered suffix `j` with `k + j = P.n`; the
step uses `sender_view_eq` so the sender of message `k + 1` copies `true`
from run `k + 1` to run `k`, and `Agreement` at `k` transfers it.
Trust: baseline `{propext, Quot.sound}` from `omega` and `sender_view_eq`; no
`Classical.choice`.
Scope: every finite protocol in the reduced model; every run `k ≤ P.n`.
-/
theorem both_attack_of_agreement (P : Protocol)
    (hAg : Agreement P) (hV : Validity P) :
    ∀ k, k ≤ P.n → P.dA (viewA k) = true ∧ P.dB (viewB k) = true := by
  have aux : ∀ j k, k + j = P.n →
      P.dA (viewA k) = true ∧ P.dB (viewB k) = true := by
    intro j
    induction j with
    | zero =>
      intro k hk
      have hk_eq : k = P.n := by omega
      subst hk_eq
      refine ⟨hV, ?_⟩
      rw [← hAg P.n (Nat.le_refl P.n)]
      exact hV
    | succ j ih =>
      intro k hk
      have hkj : (k + 1) + j = P.n := by omega
      have ihk := ih (k + 1) hkj
      have hsv := sender_view_eq k
      cases hsend : sender (k + 1)
      · have hview : viewB (k + 1) = viewB k := by
          simp [senderView, hsend] at hsv
          exact hsv
        have hB : P.dB (viewB k) = true := by
          rw [← hview]
          exact ihk.2
        have hk_le : k ≤ P.n := by omega
        have hA : P.dA (viewA k) = true := by
          rw [hAg k hk_le]
          exact hB
        exact ⟨hA, hB⟩
      · have hview : viewA (k + 1) = viewA k := by
          simp [senderView, hsend] at hsv
          exact hsv
        have hA : P.dA (viewA k) = true := by
          rw [← hview]
          exact ihk.1
        have hk_le : k ≤ P.n := by omega
        have hB : P.dB (viewB k) = true := by
          rw [← hAg k hk_le]
          exact hA
        exact ⟨hA, hB⟩
  intro k hk
  exact aux (P.n - k) k (Nat.add_sub_of_le hk)

/--
Proves: no finite deterministic protocol in the reduced model satisfies
agreement, validity, and no-information-no-attack together.
Does not prove: the probabilistic lift or the bounded-delay refusal; both are
ESTABLISHED and named in the module docstring, and neither is proved here.
Relation: negation of the conjunction of `Agreement`, `Validity`, and
`NoInformationNoAttack`.
Closure: not applicable.
Strategy: `both_attack_of_agreement` at `k = 0` yields `dB (viewB 0) = true`,
contradicting `NoInformationNoAttack`.
Trust: baseline `{propext, Quot.sound}` inherited from
`both_attack_of_agreement`; the historical result is ESTABLISHED (Akkoyunlu,
Ekanadham and Huber 1975; Gray 1978) and is cited, not assumed.
Scope: every `Protocol` in this reduced model; no hypothesis beyond `P`.
-/
theorem two_generals_impossible (P : Protocol) :
    ¬ (Agreement P ∧ Validity P ∧ NoInformationNoAttack P) := by
  rintro ⟨hAg, hV, hNI⟩
  have hB := (both_attack_of_agreement P hAg hV 0 (Nat.zero_le P.n)).2
  have hfalse : P.dB (viewB 0) = false := hNI
  rw [hB] at hfalse
  nomatch hfalse

/-! ## First-message rung as a `TypedBoundary` -/

/-- The first-message collision: A's view is the same in run `0` and run `1`,
while delivery of message `1` differs. -/
def twoGeneralsBoundary : TypedBoundary where
  State := Nat
  Obs := Nat
  Verdict := Bool
  observe := senderView 1
  verdict := delivered 1
  s₁ := 0
  s₂ := 1
  obs_eq := rfl
  verdict_ne := by decide

/--
Proves: `twoGeneralsBoundary` obeys the universal boundary law: the delivery
verdict is not a function of A's first-message view.
Does not prove: the capstone over a whole protocol; that is
`two_generals_impossible`.
Relation: `TypedBoundary.verdict_not_observation_function`.
Closure: not applicable.
Strategy: one application of the imported universal law.
Trust: kernel-only.
Scope: the first-message rung `s₁ = 0`, `s₂ = 1` of the reduced model.
-/
theorem twoGeneralsBoundary_obeys_law :
    ¬ ∃ f : twoGeneralsBoundary.Obs → twoGeneralsBoundary.Verdict,
      ∀ s : twoGeneralsBoundary.State,
        twoGeneralsBoundary.verdict s = f (twoGeneralsBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function twoGeneralsBoundary

/-! ## Non-vacuity: each requirement is separately satisfiable -/

/-- One-message protocol: A always attacks; B attacks exactly when B received
a message. -/
def P1 : Protocol :=
  ⟨1, fun _ => true, fun v => decide (0 < v)⟩

/-- Always-attack one-message protocol. -/
def P0 : Protocol :=
  ⟨1, fun _ => true, fun _ => true⟩

/--
Proves: `P1` satisfies `Validity`.
Does not prove: `Agreement` for `P1`.
Relation: `Validity P1`.
Closure: not applicable.
Strategy: definitional.
Trust: kernel-only.
Scope: the one-message protocol `P1`.
-/
theorem P1_validity : Validity P1 := rfl

/--
Proves: `P1` satisfies `NoInformationNoAttack`.
Does not prove: `Agreement` for `P1`.
Relation: `NoInformationNoAttack P1`.
Closure: not applicable.
Strategy: definitional.
Trust: kernel-only.
Scope: the one-message protocol `P1`.
-/
theorem P1_noInformationNoAttack : NoInformationNoAttack P1 := rfl

/--
Proves: `P1` fails `Agreement` at run `k = 0`.
Does not prove: failure of validity or of no-information-no-attack.
Relation: `Agreement P1`.
Closure: not applicable.
Strategy: instantiate at `k = 0`; A attacks and B does not.
Trust: kernel-only; closed Boolean inequality.
Scope: the one-message protocol `P1`.
-/
theorem P1_not_agreement : ¬ Agreement P1 := by
  intro h
  have h0 := h 0 (by decide)
  nomatch h0

/--
Proves: `P0` satisfies `Agreement`.
Does not prove: `NoInformationNoAttack` for `P0`.
Relation: `Agreement P0`.
Closure: not applicable.
Strategy: both decisions are constantly `true`.
Trust: kernel-only.
Scope: the always-attack protocol `P0`.
-/
theorem P0_agreement : Agreement P0 := fun _ _ => rfl

/--
Proves: `P0` satisfies `Validity`.
Does not prove: `NoInformationNoAttack` for `P0`.
Relation: `Validity P0`.
Closure: not applicable.
Strategy: definitional.
Trust: kernel-only.
Scope: the always-attack protocol `P0`.
-/
theorem P0_validity : Validity P0 := rfl

/--
Proves: `P0` fails `NoInformationNoAttack`.
Does not prove: failure of agreement or of validity.
Relation: `NoInformationNoAttack P0`.
Closure: not applicable.
Strategy: B's decision is constantly `true`.
Trust: kernel-only; closed Boolean inequality.
Scope: the always-attack protocol `P0`.
-/
theorem P0_not_noInformationNoAttack : ¬ NoInformationNoAttack P0 := by
  intro h
  nomatch h

-- Axiom audit (Rule W16: recorded for the build log).
#print axioms sender_view_eq
#print axioms rung_collision
#print axioms sender_cannot_know
#print axioms both_attack_of_agreement
#print axioms two_generals_impossible
#print axioms twoGeneralsBoundary_obeys_law
#print axioms P1_validity
#print axioms P1_noInformationNoAttack
#print axioms P1_not_agreement
#print axioms P0_agreement
#print axioms P0_validity
#print axioms P0_not_noInformationNoAttack

end OperatorKO7.Meta.UniversalBoundary.TwoGeneralsBoundary
