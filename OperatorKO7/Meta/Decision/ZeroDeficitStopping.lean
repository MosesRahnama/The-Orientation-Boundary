/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Zero-deficit stopping

Finite decision theory: a nonempty finite action set, a finite target, and a
bounded (`ℕ`-valued) loss. The licensed-channel deficit is imported from
`LicensedChannelDeficit` (`circular_reference_zero_deficit`, `deficit_bracket`,
`deficit_witness_pos`). It is not rebuilt.

Decision reading (the theorem): if the channel is informationally a copy of the
direct surface, then the value of computation is zero; any strictly positive
cost makes the stop branch strictly dominate, so the optimal meta-policy
refuses the computation. Relicensing deliberation requires a positive deficit,
a new obligation, or a changed loss model.

Cognitive reading (ANALOGY, with falsifier): the informational echo is an
identity reflective pair and is refused. Falsifier: a positive-deficit channel
whose information value exceeds the cost; then the stop conclusion fails
(`positive_deficit_stop_conclusion_fails`, computed by `optimalMetaPolicy` at
cost one half).

Worked instance: every verdict of the two-action two-state instance is the value
of `optimalMetaPolicy` on `demoDecision` with the instance data, computed from the
expected losses of the two branches (`demo_twoState_instance_halfCost_unitCostControl`).
At unit cost the revealing channel ties and the policy stops
(`demo_revealing_unitCost_policy_stop`, control R1).

Relation: not applicable (finite decision theory, not a rewriting relation).
Closure: not applicable. Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

open scoped BigOperators

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

namespace OperatorKO7.Meta.Decision.ZeroDeficitStopping

/-- Meta-policy: act on current information, or pay the cost and consult the
channel before acting. -/
inductive MetaPolicy where
  | stop
  | compute
deriving DecidableEq, Repr

/-- Finite nonempty action set, finite target, bounded loss. -/
structure FiniteDecision (A X : Type) [DecidableEq A] [Fintype X] where
  actions : Finset A
  nonempty : actions.Nonempty
  loss : A → X → ℕ

/-- Expected loss of action `a` in a single `(W0, C)` cell. -/
noncomputable def cellLoss {A X W Cn : Type} [Fintype X]
    (loss : A → X → ℕ) (r : W → Cn → X → ℝ) (a : A) (w : W) (c : Cn) : ℝ :=
  ∑ x, r w c x * (loss a x : ℝ)

/-- Expected loss of action `a` given only `W0`, mixing out the channel. -/
noncomputable def directCellLoss {A X W Cn : Type} [Fintype X] [Fintype Cn]
    (ν : W → Cn → ℝ) (loss : A → X → ℕ) (r : W → Cn → X → ℝ)
    (a : A) (w : W) : ℝ :=
  ∑ x, (∑ c, ν w c * r w c x) * (loss a x : ℝ)

/-- Best expected loss at a `(W0, C)` cell. -/
noncomputable def bestCellLoss {A X W Cn : Type} [DecidableEq A] [Fintype X]
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) (w : W) (c : Cn) : ℝ :=
  D.actions.inf' D.nonempty (fun a => cellLoss D.loss r a w c)

/-- Best expected loss given only `W0`. -/
noncomputable def bestDirectLoss {A X W Cn : Type} [DecidableEq A] [Fintype X]
    [Fintype Cn] (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (w : W) : ℝ :=
  D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w)

/-- Expected loss of the stop branch (act without consulting the channel). -/
noncomputable def expectedStop {A X W Cn : Type} [DecidableEq A] [Fintype X]
    [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) : ℝ :=
  ∑ w, μ w * bestDirectLoss ν D r w

/-- Expected loss after consulting the channel, before adding the cost. -/
noncomputable def expectedComputeNoCost {A X W Cn : Type} [DecidableEq A]
    [Fintype X] [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) : ℝ :=
  ∑ w, μ w * ∑ c, ν w c * bestCellLoss D r w c

/-- Expected total loss of the compute branch. -/
noncomputable def expectedCompute {A X W Cn : Type} [DecidableEq A]
    [Fintype X] [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) (cost : ℝ) : ℝ :=
  expectedComputeNoCost μ ν D r + cost

/-- Value of computation of a licensed channel: reduction in expected loss
before cost. Channel independence makes this zero. -/
noncomputable def valueOfComputation {A X W Cn : Type} [DecidableEq A]
    [Fintype X] [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) : ℝ :=
  expectedStop μ ν D r - expectedComputeNoCost μ ν D r

/-- Optimal meta-policy: compute only when the channel strictly reduces total
expected loss after cost. Uses classical decidability of `ℝ` order. -/
noncomputable def optimalMetaPolicy {A X W Cn : Type} [DecidableEq A]
    [Fintype X] [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ) (cost : ℝ) : MetaPolicy :=
  haveI := Classical.dec
    (expectedCompute μ ν D r cost < expectedStop μ ν D r)
  if expectedCompute μ ν D r cost < expectedStop μ ν D r then
    MetaPolicy.compute
  else
    MetaPolicy.stop

/-- Imported zero-deficit surface: a channel-constant conditional has deficit
zero (`circular_reference_zero_deficit`). -/
theorem circular_reference_is_zero_deficit {X W Cn : Type}
    [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (s : W → X → ℝ)
    (hconst : ∀ w c, r w c = s w) :
    deficit μ ν r = 0 :=
  circular_reference_zero_deficit μ ν r hν1 s hconst

private theorem mixture_of_channel_const {X W Cn : Type} [Fintype X] [Fintype Cn]
    (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) (s : W → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (hconst : ∀ w c, r w c = s w) (w : W) :
    (fun x => ∑ c, ν w c * r w c x) = s w := by
  funext x
  calc
    ∑ c, ν w c * r w c x = ∑ c, ν w c * s w x := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hconst w c]
    _ = (∑ c, ν w c) * s w x := by rw [← Finset.sum_mul]
    _ = s w x := by rw [hν1 w, one_mul]

private theorem cellLoss_eq_direct_of_const {A X W Cn : Type} [Fintype X]
    [Fintype Cn] (ν : W → Cn → ℝ) (loss : A → X → ℕ) (r : W → Cn → X → ℝ)
    (s : W → X → ℝ) (hν1 : ∀ w, ∑ c, ν w c = 1)
    (hconst : ∀ w c, r w c = s w) (a : A) (w : W) (c : Cn) :
    cellLoss loss r a w c = directCellLoss ν loss r a w := by
    unfold cellLoss directCellLoss
    rw [hconst w c]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [congrFun (mixture_of_channel_const ν r s hν1 hconst w) x]

/-- Channel independence (the deficit-zero condition on the imported surface)
leaves the best expected loss unchanged: value of computation is zero. -/
theorem zero_deficit_zero_VOC {A X W Cn : Type} [DecidableEq A] [Fintype X]
    [Fintype W] [Fintype Cn] (μ : W → ℝ) (ν : W → Cn → ℝ)
    (D : FiniteDecision A X) (r : W → Cn → X → ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (s : W → X → ℝ)
    (hconst : ∀ w c, r w c = s w) :
    valueOfComputation μ ν D r = 0 := by
  unfold valueOfComputation expectedStop expectedComputeNoCost
    bestDirectLoss bestCellLoss
  have hcell : ∀ w c,
      D.actions.inf' D.nonempty (fun a => cellLoss D.loss r a w c) =
        D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w) := by
    intro w c
    exact D.actions.inf'_congr D.nonempty rfl (fun a _ =>
      cellLoss_eq_direct_of_const ν D.loss r s hν1 hconst a w c)
  have hmix : ∀ w,
      (∑ c, ν w c * D.actions.inf' D.nonempty (fun a => cellLoss D.loss r a w c)) =
        D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w) := by
    intro w
    calc
      ∑ c, ν w c * D.actions.inf' D.nonempty (fun a => cellLoss D.loss r a w c) =
          ∑ c, ν w c *
            D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hcell w c]
      _ = (∑ c, ν w c) *
            D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w) := by
        rw [← Finset.sum_mul]
      _ = D.actions.inf' D.nonempty (fun a => directCellLoss ν D.loss r a w) := by
        rw [hν1 w, one_mul]
  refine sub_eq_zero.mpr ?_
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hmix w]

/-- With any strictly positive cost, a zero-deficit channel is refused: the
stop branch strictly dominates, so the optimal meta-policy is `stop`. -/
theorem positive_cost_zero_deficit_forces_stop {A X W Cn : Type}
    [DecidableEq A] [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (D : FiniteDecision A X)
    (r : W → Cn → X → ℝ) (cost : ℝ)
    (hν1 : ∀ w, ∑ c, ν w c = 1) (s : W → X → ℝ)
    (hconst : ∀ w c, r w c = s w) (hcost : 0 < cost) :
    optimalMetaPolicy μ ν D r cost = MetaPolicy.stop := by
  have hVOC : valueOfComputation μ ν D r = 0 :=
    zero_deficit_zero_VOC μ ν D r hν1 s hconst
  have hEq : expectedCompute μ ν D r cost = expectedStop μ ν D r + cost := by
    unfold expectedCompute valueOfComputation at *
    linarith
  have hlt : expectedStop μ ν D r < expectedCompute μ ν D r cost := by
    rw [hEq]
    exact lt_add_of_pos_right _ hcost
  unfold optimalMetaPolicy
  split_ifs with h
  · exact (lt_asymm hlt h).elim
  · rfl

/-! ## Two-action, two-state worked instance, computed by the formal policy

The instance of `prop:zero-deficit-stopping`: two actions and two target states with loss `0` on
a match and `2` on a mismatch (`demoDecision`), one observer cell of weight one (`demoPrior`), a
channel value in `Fin 2` with the uniform conditional law (`demoChannelLaw`), the copy channel
`echoChannel` (the uniform target law in every cell) and the revealing channel
`revealingChannel` (the point mass at the channel cell). Every verdict below is the value of
`optimalMetaPolicy` on this data, read off the expected losses of the two branches; no score is
written by hand. At cost one half (`demoHalfCost`) the copy channel stops and the revealing
channel computes. At unit cost (`demoCost`) the revealing channel ties the two branches and the
policy stops: this is the control R1 of the closure proof graph. -/

def demoLoss (a x : Fin 2) : ℕ := if a = x then 0 else 2

def demoDecision : FiniteDecision (Fin 2) (Fin 2) where
  actions := Finset.univ
  nonempty := Finset.univ_nonempty
  loss := demoLoss

/-- Unit cost of the control R1, cast to `ℝ` at its use.
Proves: no proposition; it fixes the cost `1` of the control instance.
Does not prove: any policy verdict; `demo_revealing_unitCost_policy_stop` reads it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
def demoCost : ℕ := 1

/-- Observer weights of the instance: one observer cell of weight one.
Proves: no proposition; it fixes `μ`.
Does not prove: any policy verdict.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
noncomputable def demoPrior : Fin 1 → ℝ := fun _ => 1

/-- Conditional channel law of the instance: weight one half on each channel cell.
Proves: no proposition; it fixes `ν`.
Does not prove: any policy verdict; `demoChannelLaw_sum_one` proves the law sums to one.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
noncomputable def demoChannelLaw : Fin 1 → Fin 2 → ℝ := fun _ _ => (1 : ℝ) / 2

/-- The copy channel: the target law is uniform in every `(w, c)` cell, so the channel carries
no target information beyond the observer cell.
Proves: no proposition; it fixes `r` for the copy case.
Does not prove: the zero deficit; `demo_echo_zero_deficit_and_stop` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
noncomputable def echoChannel : Fin 1 → Fin 2 → Fin 2 → ℝ := fun _ _ _ => (1 : ℝ) / 2

/-- The revealing channel: the target law in cell `(w, c)` is the point mass at `c`.
Proves: no proposition; it fixes `r` for the revealing case.
Does not prove: the positive deficit; `positive_deficit_stop_conclusion_fails` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
noncomputable def revealingChannel : Fin 1 → Fin 2 → Fin 2 → ℝ := fun _ c => pointMass c

/-- The cost one half of the paper's instance.
Proves: no proposition; it fixes the cost of the compute branch.
Does not prove: any policy verdict.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: the two-action two-state instance. -/
noncomputable def demoHalfCost : ℝ := 1 / 2

/-- Proves: the channel law of the instance sums to one in the observer cell.
Does not prove: any loss value.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: `demoChannelLaw`. -/
theorem demoChannelLaw_sum_one : ∀ w : Fin 1, ∑ c, demoChannelLaw w c = 1 := by
  intro w
  rw [Fin.sum_univ_two]
  norm_num [demoChannelLaw]

private theorem demo_echo_cellLoss (a : Fin 2) (w : Fin 1) (c : Fin 2) :
    cellLoss demoDecision.loss echoChannel a w c = 1 := by
  fin_cases a <;>
    simp [cellLoss, echoChannel, Fin.sum_univ_two, demoDecision, demoLoss]

private theorem demo_echo_directCellLoss (a : Fin 2) (w : Fin 1) :
    directCellLoss demoChannelLaw demoDecision.loss echoChannel a w = 1 := by
  fin_cases a <;>
    simp [directCellLoss, demoChannelLaw, echoChannel, Fin.sum_univ_two, demoDecision,
      demoLoss]

private theorem demo_revealing_cellLoss (a : Fin 2) (w : Fin 1) (c : Fin 2) :
    cellLoss demoDecision.loss revealingChannel a w c = (demoLoss a c : ℝ) := by
  fin_cases a <;> fin_cases c <;>
    simp [cellLoss, revealingChannel, pointMass, Fin.sum_univ_two, demoDecision, demoLoss]

private theorem demo_revealing_directCellLoss (a : Fin 2) (w : Fin 1) :
    directCellLoss demoChannelLaw demoDecision.loss revealingChannel a w = 1 := by
  fin_cases a <;>
    simp [directCellLoss, demoChannelLaw, revealingChannel, pointMass, Fin.sum_univ_two,
      demoDecision, demoLoss]

/-- Proves: the stop branch of the copy channel has expected loss `1`: every action has expected
loss `(1/2)·0 + (1/2)·2 = 1` given the observer cell alone.
Does not prove: the compute branch value; `demo_echo_expectedComputeNoCost` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_echo_expectedStop :
    expectedStop demoPrior demoChannelLaw demoDecision echoChannel = 1 := by
  have hbest : ∀ w : Fin 1, bestDirectLoss demoChannelLaw demoDecision echoChannel w = 1 := by
    intro w
    unfold bestDirectLoss
    simp only [demo_echo_directCellLoss]
    exact Finset.inf'_const _ _
  simp only [expectedStop, Fin.sum_univ_one, hbest, demoPrior, mul_one]

/-- Proves: after consulting the copy channel the least expected loss is still `1` in every cell,
so the compute branch has expected loss `1` before cost.
Does not prove: the policy verdict; `demo_echo_halfCost_policy_stop` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_echo_expectedComputeNoCost :
    expectedComputeNoCost demoPrior demoChannelLaw demoDecision echoChannel = 1 := by
  have hbest : ∀ (w : Fin 1) (c : Fin 2), bestCellLoss demoDecision echoChannel w c = 1 := by
    intro w c
    unfold bestCellLoss
    simp only [demo_echo_cellLoss]
    exact Finset.inf'_const _ _
  simp only [expectedComputeNoCost, Fin.sum_univ_one, hbest, mul_one, demoPrior, one_mul]
  exact demoChannelLaw_sum_one 0

/-- Proves: the stop branch of the revealing channel has expected loss `1`: mixing out the channel
gives the uniform target law, and every action has expected loss `1` under it.
Does not prove: the compute branch value; `demo_revealing_expectedComputeNoCost` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_revealing_expectedStop :
    expectedStop demoPrior demoChannelLaw demoDecision revealingChannel = 1 := by
  have hbest : ∀ w : Fin 1,
      bestDirectLoss demoChannelLaw demoDecision revealingChannel w = 1 := by
    intro w
    unfold bestDirectLoss
    simp only [demo_revealing_directCellLoss]
    exact Finset.inf'_const _ _
  simp only [expectedStop, Fin.sum_univ_one, hbest, demoPrior, mul_one]

/-- Proves: after consulting the revealing channel the action equal to the channel cell has
loss `0`, so the compute branch has expected loss `0` before cost.
Does not prove: the policy verdict; `demo_revealing_halfCost_policy_compute` proves it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_revealing_expectedComputeNoCost :
    expectedComputeNoCost demoPrior demoChannelLaw demoDecision revealingChannel = 0 := by
  have hbest : ∀ (w : Fin 1) (c : Fin 2), bestCellLoss demoDecision revealingChannel w c = 0 := by
    intro w c
    unfold bestCellLoss
    apply le_antisymm
    · exact (Finset.inf'_le _ (by simp [demoDecision] : c ∈ demoDecision.actions)).trans_eq
        ((demo_revealing_cellLoss c w c).trans (by simp [demoLoss]))
    · exact Finset.le_inf' _ _ (fun a _ =>
        le_of_le_of_eq (by positivity) (demo_revealing_cellLoss a w c).symm)
  simp only [expectedComputeNoCost, hbest, mul_zero, Finset.sum_const_zero]

/-- Proves: at cost one half the formal policy stops on the copy channel. The verdict is the
general stop theorem `positive_cost_zero_deficit_forces_stop` applied to the instance (the copy
channel is channel-constant and the cost is positive); the branch values are `1` (stop) and
`1 + 1/2` (compute).
Does not prove: a verdict at another cost or another channel.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_echo_halfCost_policy_stop :
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision echoChannel demoHalfCost =
      MetaPolicy.stop :=
  positive_cost_zero_deficit_forces_stop demoPrior demoChannelLaw demoDecision echoChannel
    demoHalfCost demoChannelLaw_sum_one (fun _ _ => (1 : ℝ) / 2) (fun _ _ => rfl)
    (by norm_num [demoHalfCost])

/-- Proves: at cost one half the formal policy computes on the revealing channel: the compute
branch costs `0 + 1/2`, strictly below the stop branch value `1`.
Does not prove: a verdict at unit cost; `demo_revealing_unitCost_policy_stop` gives that verdict.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_revealing_halfCost_policy_compute :
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision revealingChannel demoHalfCost =
      MetaPolicy.compute := by
  unfold optimalMetaPolicy expectedCompute
  rw [demo_revealing_expectedComputeNoCost, demo_revealing_expectedStop]
  norm_num [demoHalfCost]

/-- Proves: at unit cost the revealing channel ties the two branches: the compute branch costs
`0 + 1` and the stop branch costs `1`.
Does not prove: a strict preference; the tie is the content of the control R1.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_revealing_unitCost_tie :
    expectedCompute demoPrior demoChannelLaw demoDecision revealingChannel (demoCost : ℝ) =
      expectedStop demoPrior demoChannelLaw demoDecision revealingChannel := by
  unfold expectedCompute
  rw [demo_revealing_expectedComputeNoCost, demo_revealing_expectedStop]
  norm_num [demoCost]

/-- Proves: at unit cost the formal policy stops on the revealing channel, because a tie is not a
strict improvement (control R1: a positive deficit alone does not make the policy compute).
Does not prove: stopping at a cost below one; `demo_revealing_halfCost_policy_compute` refutes it.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_revealing_unitCost_policy_stop :
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision revealingChannel (demoCost : ℝ) =
      MetaPolicy.stop := by
  unfold optimalMetaPolicy
  rw [demo_revealing_unitCost_tie]
  simp

/-- Proves: the copy channel of the instance has deficit zero, and at cost one half the formal
policy `optimalMetaPolicy` stops on it.
Does not prove: a verdict at another cost; the stop at every positive cost is
`positive_cost_zero_deficit_forces_stop`.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_echo_zero_deficit_and_stop :
    deficit demoPrior demoChannelLaw echoChannel = 0 ∧
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision echoChannel demoHalfCost =
      MetaPolicy.stop :=
  ⟨circular_reference_witness_zero, demo_echo_halfCost_policy_stop⟩

/-- Counter-instance of the zero-deficit hypothesis.
Proves: the revealing channel has positive deficit, and at cost one half the formal policy
`optimalMetaPolicy` computes on it, so the conclusion of the stop theorem fails once the
zero-deficit hypothesis is dropped.
Does not prove: that a positive deficit forces computing at every cost; at unit cost the policy
stops (`demo_revealing_unitCost_policy_stop`).
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem positive_deficit_stop_conclusion_fails :
    0 < deficit demoPrior demoChannelLaw revealingChannel ∧
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision revealingChannel demoHalfCost =
      MetaPolicy.compute :=
  ⟨deficit_witness_pos, demo_revealing_halfCost_policy_compute⟩

/-- The two-action two-state instance of `prop:zero-deficit-stopping` as one statement.
Proves: with mismatch loss `2`, uniform prior and cost one half, the copy channel has deficit zero
and the formal policy stops; the revealing channel has positive deficit and the formal policy
computes; at unit cost the revealing channel ties the two branches and the formal policy stops.
Does not prove: a verdict for any other loss, prior or channel.
Relation: not applicable. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline. Scope: the two-action two-state instance. -/
theorem demo_twoState_instance_halfCost_unitCostControl :
    deficit demoPrior demoChannelLaw echoChannel = 0 ∧
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision echoChannel demoHalfCost =
      MetaPolicy.stop ∧
    0 < deficit demoPrior demoChannelLaw revealingChannel ∧
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision revealingChannel demoHalfCost =
      MetaPolicy.compute ∧
    expectedCompute demoPrior demoChannelLaw demoDecision revealingChannel (demoCost : ℝ) =
      expectedStop demoPrior demoChannelLaw demoDecision revealingChannel ∧
    optimalMetaPolicy demoPrior demoChannelLaw demoDecision revealingChannel (demoCost : ℝ) =
      MetaPolicy.stop :=
  ⟨demo_echo_zero_deficit_and_stop.1, demo_echo_zero_deficit_and_stop.2,
    positive_deficit_stop_conclusion_fails.1, positive_deficit_stop_conclusion_fails.2,
    demo_revealing_unitCost_tie, demo_revealing_unitCost_policy_stop⟩

/-- Imported bracket, consumed as a named fact on the echo channel. -/
theorem demo_echo_deficit_bracket :
    0 ≤ deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) ∧
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) ≤
      condEntropyDirect (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
        (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) :=
  deficit_bracket (fun _ => 1) (fun _ _ => (1 : ℝ) / 2)
    (fun _ _ => fun _ => (1 : ℝ) / 2)
    (fun _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ => by rw [Fin.sum_univ_two]; norm_num)
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)

end OperatorKO7.Meta.Decision.ZeroDeficitStopping
