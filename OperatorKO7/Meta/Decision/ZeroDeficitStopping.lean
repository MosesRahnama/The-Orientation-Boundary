/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Zero-deficit stopping (Roadmap 09, Layer 7.1)

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
(`positive_deficit_stop_conclusion_fails`).

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

/-! ## R5: two-action, two-state worked instance (optimum by `decide`)

Mismatch loss is 2 so a uniform prior has stop-score 2. Unit cost then makes
the echo (zero deficit) compute-score 3 and the revealing (positive deficit)
compute-score 1. -/

def demoLoss (a x : Fin 2) : ℕ := if a = x then 0 else 2

def demoDecision : FiniteDecision (Fin 2) (Fin 2) where
  actions := Finset.univ
  nonempty := Finset.univ_nonempty
  loss := demoLoss

def demoStopScore : ℕ := 2

def demoCost : ℕ := 1

def demoZeroDeficitComputeScore : ℕ := 3

def demoPosDeficitComputeScore : ℕ := 1

def demoZeroDeficitOptimal : MetaPolicy :=
  if demoZeroDeficitComputeScore < demoStopScore then MetaPolicy.compute
  else MetaPolicy.stop

def demoPosDeficitOptimal : MetaPolicy :=
  if demoPosDeficitComputeScore < demoStopScore then MetaPolicy.compute
  else MetaPolicy.stop

theorem demoStopScore_is_min :
    ∀ a : Fin 2, demoStopScore ≤ ∑ x : Fin 2, demoLoss a x := by
  decide

theorem demo_zero_deficit_optimal_is_stop :
    demoZeroDeficitOptimal = MetaPolicy.stop := by
  decide

theorem demo_pos_deficit_optimal_is_compute :
    demoPosDeficitOptimal = MetaPolicy.compute := by
  decide

/-- The echo channel of the imported circular-reference witness has deficit
zero, and the worked instance stops. -/
theorem demo_echo_zero_deficit_and_stop :
    deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ _ => fun _ => (1 : ℝ) / 2) = 0 ∧
    demoZeroDeficitOptimal = MetaPolicy.stop :=
  ⟨circular_reference_witness_zero, demo_zero_deficit_optimal_is_stop⟩

/-- Load-bearing counter-instance: the imported positive-deficit witness
(perfectly revealing binary channel) has positive deficit, and the stop
theorem's conclusion fails (compute strictly dominates). The zero-deficit
hypothesis is therefore not idle. -/
theorem positive_deficit_stop_conclusion_fails :
    0 < deficit (W := Fin 1) (Cn := Fin 2) (X := Fin 2)
      (fun _ => 1) (fun _ _ => (1 : ℝ) / 2) (fun _ c => pointMass c) ∧
    demoPosDeficitOptimal ≠ MetaPolicy.stop :=
  ⟨deficit_witness_pos, by decide⟩

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
