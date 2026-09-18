import OperatorKO7.Meta.SchemaConfessionDominance

/-!
# The confession crossing point

`SchemaConfessionDominance` proves the growth law: a direct observer that
carries every duplicated payload accumulates burden $(k+1)(k+2)p$ in doubled
units, against residual proof work that grows linearly in $k$. The law says the
carried cost eventually dominates. It leaves open when.

This module closes that. A confessing observer pays a fixed license price once
and then pays only the residual, so the two cost curves cross. The crossing
point is the least depth at which carrying costs more than confessing, it is
computable from the payload size and the license price, and past it the
inequality never reverses.

The consequence is that the confession event stops being arbitrary. An observer
does not confess at an unspecified moment chosen by patience. It confesses at
`crossingPoint`, and an exhaustion budget set at or above that value is forced
by the arithmetic instead of chosen by the designer.

Sharpness is recorded too: with payload size zero there is no crossing at any
depth (`no_crossing_of_zero_payload`), so duplication is what creates the
crossing and the hypothesis `1 ≤ p` cannot be dropped.

## Claim typing (binding)
* PROVEN: every theorem below, on the declared cost model.
* SCOPE: the cost model is declared, not derived. `directCarryCostDoubled` is
  the existing `confessedBurdenDoubled`; `confessExitCostDoubled` charges a
  fixed license price plus the existing `residualProofWork`. Different license
  pricing gives a different crossing point, and the theorems are stated against
  the price as a parameter.

## Audit slots
- Relation: none; finite arithmetic over the declared cost curves.
- Closure: none. Trust: no `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ConfessionCrossingPoint

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-! ## The two cost curves -/

/-- Doubled cost of the direct observer at depth `k` with payload size `p`: it
carries every copy, so its burden is the quadratic confessed-burden total. -/
def directCarryCostDoubled (k p : Nat) : Nat := confessedBurdenDoubled k p

/-- Doubled cost of the confessing observer: a fixed license price paid once,
plus the linear residual proof work. -/
def confessExitCostDoubled (licenseCost k : Nat) : Nat :=
  2 * licenseCost + 2 * residualProofWork k

@[simp] theorem directCarryCostDoubled_eq (k p : Nat) :
    directCarryCostDoubled k p = (k + 1) * (k + 2) * p := rfl

@[simp] theorem confessExitCostDoubled_eq (licenseCost k : Nat) :
    confessExitCostDoubled licenseCost k = 2 * licenseCost + 2 * k := rfl

/-- Carrying costs more than confessing at depth `k`. -/
def CarryExceedsConfess (p licenseCost k : Nat) : Prop :=
  confessExitCostDoubled licenseCost k < directCarryCostDoubled k p

instance decidableCarryExceedsConfess (p licenseCost : Nat) :
    DecidablePred (CarryExceedsConfess p licenseCost) := by
  intro k
  unfold CarryExceedsConfess
  infer_instance

/-! ## The crossing exists and is explicit -/

/-- With a nonzero payload the curves have crossed by depth `licenseCost`. This
is an explicit computable witness, so existence needs no search. -/
theorem carry_exceeds_at_licenseCost (p licenseCost : Nat) (hp : 1 ≤ p) :
    CarryExceedsConfess p licenseCost licenseCost := by
  unfold CarryExceedsConfess
  simp only [directCarryCostDoubled_eq, confessExitCostDoubled_eq]
  have key : 2 * licenseCost + 2 * licenseCost
      < (licenseCost + 1) * (licenseCost + 2) := by
    cases licenseCost with
    | zero => norm_num
    | succ n => nlinarith [Nat.zero_le n]
  calc 2 * licenseCost + 2 * licenseCost
      < (licenseCost + 1) * (licenseCost + 2) := key
    _ = (licenseCost + 1) * (licenseCost + 2) * 1 := by ring
    _ ≤ (licenseCost + 1) * (licenseCost + 2) * p := Nat.mul_le_mul_left _ hp

/-- The crossing is witnessed, so the least crossing depth is well defined. -/
theorem crossing_exists (p licenseCost : Nat) (hp : 1 ≤ p) :
    ∃ k, CarryExceedsConfess p licenseCost k :=
  ⟨licenseCost, carry_exceeds_at_licenseCost p licenseCost hp⟩

/-- **The crossing point.** The least depth at which carrying costs more than
confessing. It is computed, not chosen. -/
def crossingPoint (p licenseCost : Nat) (hp : 1 ≤ p) : Nat :=
  Nat.find (crossing_exists p licenseCost hp)

/-- At the crossing point, carrying costs more. -/
theorem crossingPoint_spec (p licenseCost : Nat) (hp : 1 ≤ p) :
    CarryExceedsConfess p licenseCost (crossingPoint p licenseCost hp) :=
  Nat.find_spec (crossing_exists p licenseCost hp)

/-- Below the crossing point, carrying is still the cheaper option. This is what
makes the point a crossing instead of a threshold. -/
theorem crossingPoint_least (p licenseCost : Nat) (hp : 1 ≤ p) {k : Nat}
    (hk : k < crossingPoint p licenseCost hp) :
    ¬ CarryExceedsConfess p licenseCost k :=
  Nat.find_min (crossing_exists p licenseCost hp) hk

/-- The crossing point is bounded by the license price, so it is small and
explicitly computable. -/
theorem crossingPoint_le_licenseCost (p licenseCost : Nat) (hp : 1 ≤ p) :
    crossingPoint p licenseCost hp ≤ licenseCost :=
  Nat.find_le (carry_exceeds_at_licenseCost p licenseCost hp)

/-! ## The inequality never reverses -/

/-- One step past a crossing the gap only widens. -/
theorem carry_exceeds_succ (p licenseCost k : Nat) (hp : 1 ≤ p)
    (h : CarryExceedsConfess p licenseCost k) :
    CarryExceedsConfess p licenseCost (k + 1) := by
  unfold CarryExceedsConfess at h ⊢
  simp only [directCarryCostDoubled_eq, confessExitCostDoubled_eq] at h ⊢
  nlinarith [h, hp, Nat.zero_le k, Nat.zero_le licenseCost]

/-- **Past the crossing point the direct observer is always behind.** -/
theorem carry_exceeds_of_crossingPoint_le (p licenseCost : Nat) (hp : 1 ≤ p)
    {k : Nat} (hk : crossingPoint p licenseCost hp ≤ k) :
    CarryExceedsConfess p licenseCost k := by
  induction k with
  | zero =>
      have h0 : crossingPoint p licenseCost hp = 0 := Nat.le_zero.mp hk
      have := crossingPoint_spec p licenseCost hp
      rwa [h0] at this
  | succ n ih =>
      rcases Nat.lt_or_ge n (crossingPoint p licenseCost hp) with hlt | hge
      · have hn : crossingPoint p licenseCost hp = n + 1 :=
          Nat.le_antisymm hk hlt
        have := crossingPoint_spec p licenseCost hp
        rwa [hn] at this
      · exact carry_exceeds_succ p licenseCost n hp (ih hge)

/-- **The confession event is located.** Carrying costs more than confessing at
depth `k` if and only if `k` has reached the crossing point. The direct
observer's exit is therefore determined by arithmetic on the payload size and
the license price. -/
theorem carry_exceeds_iff_crossingPoint_le (p licenseCost : Nat) (hp : 1 ≤ p)
    (k : Nat) :
    CarryExceedsConfess p licenseCost k ↔ crossingPoint p licenseCost hp ≤ k := by
  constructor
  · intro h
    refine Classical.byContradiction (fun hlt => ?_)
    exact crossingPoint_least p licenseCost hp (Nat.lt_of_not_le hlt) h
  · exact carry_exceeds_of_crossingPoint_le p licenseCost hp

/-! ## Sharpness: duplication is what creates the crossing -/

/-- With payload size zero the curves never cross. Duplication is the source of
the crossing, and the hypothesis `1 ≤ p` cannot be dropped. -/
theorem no_crossing_of_zero_payload (licenseCost k : Nat) :
    ¬ CarryExceedsConfess 0 licenseCost k := by
  unfold CarryExceedsConfess
  simp only [directCarryCostDoubled_eq, confessExitCostDoubled_eq]
  simp

/-! ## The budget reading -/

/-- An exhaustion budget is **derived** when it sits at or above the crossing
point: every depth the budget still permits is a depth at which carrying already
costs more than confessing. -/
def BudgetDerived (p licenseCost budget : Nat) (hp : 1 ≤ p) : Prop :=
  crossingPoint p licenseCost hp ≤ budget

/-- **A derived budget forces the exit.** If the budget has reached the crossing
point, then at the budget and at every depth beyond it, carrying costs more than
confessing, so the exit is compelled by the cost curves instead of chosen. -/
theorem derived_budget_forces_confession
    (p licenseCost budget : Nat) (hp : 1 ≤ p)
    (hb : BudgetDerived p licenseCost budget hp) :
    ∀ k, budget ≤ k → CarryExceedsConfess p licenseCost k := by
  intro k hk
  exact carry_exceeds_of_crossingPoint_le p licenseCost hp
    (Nat.le_trans hb hk)

/-- The least derived budget is the crossing point itself. -/
theorem crossingPoint_is_least_derived_budget
    (p licenseCost : Nat) (hp : 1 ≤ p) :
    BudgetDerived p licenseCost (crossingPoint p licenseCost hp) hp
      ∧ ∀ b, BudgetDerived p licenseCost b hp → crossingPoint p licenseCost hp ≤ b :=
  ⟨Nat.le_refl _, fun _ hb => hb⟩

/-! ## The crown -/

/-- **The confession crossing law.** For a nonzero payload the two cost curves
cross at a computable depth bounded by the license price; below it carrying is
cheaper, at and above it confessing is cheaper, the inequality never reverses,
and the least budget that forces the exit is that same depth. With payload size
zero no crossing occurs at any depth. -/
theorem confession_crossing_law (p licenseCost : Nat) (hp : 1 ≤ p) :
    crossingPoint p licenseCost hp ≤ licenseCost
      ∧ CarryExceedsConfess p licenseCost (crossingPoint p licenseCost hp)
      ∧ (∀ k, k < crossingPoint p licenseCost hp →
          ¬ CarryExceedsConfess p licenseCost k)
      ∧ (∀ k, CarryExceedsConfess p licenseCost k ↔
          crossingPoint p licenseCost hp ≤ k)
      ∧ (∀ b, BudgetDerived p licenseCost b hp →
          ∀ k, b ≤ k → CarryExceedsConfess p licenseCost k)
      ∧ (∀ k, ¬ CarryExceedsConfess 0 licenseCost k) :=
  ⟨crossingPoint_le_licenseCost p licenseCost hp,
    crossingPoint_spec p licenseCost hp,
    fun _ hk => crossingPoint_least p licenseCost hp hk,
    carry_exceeds_iff_crossingPoint_le p licenseCost hp,
    fun b hb => derived_budget_forces_confession p licenseCost b hp hb,
    fun k => no_crossing_of_zero_payload licenseCost k⟩

/-! ## The marginal law

The crossing above compares accumulated curves. The per-step exchange rate is
sharper: one further step buys one further unit of residual descent at a price
that rises with depth. -/

/-- One step buys one unit of residual proof work. The numerator of the exchange
rate is constant. -/
theorem residual_marginal (k : Nat) :
    residualProofWork (k + 1) = residualProofWork k + 1 := rfl

/-- One step costs `(k+2)p` of confessed burden, in doubled units `2(k+2)p`. The
denominator of the exchange rate rises with depth. -/
theorem carry_marginal_doubled (k p : Nat) :
    directCarryCostDoubled (k + 1) p
      = directCarryCostDoubled k p + 2 * ((k + 2) * p) := by
  simp only [directCarryCostDoubled_eq]
  ring

/-- **The exchange rate deteriorates without bound.** For any ceiling on the
value of one further step, some depth prices the next step above it. -/
theorem marginal_cost_exceeds_any_bound (p bound : Nat) (hp : 1 ≤ p) :
    ∃ k, bound < (k + 2) * p := by
  refine ⟨bound, ?_⟩
  calc bound < bound + 2 := by omega
    _ = (bound + 2) * 1 := by ring
    _ ≤ (bound + 2) * p := Nat.mul_le_mul_left _ hp

/-! ## The stopping rule

A cost-rational observer continues while the value of one further step exceeds
its marginal price. Two regimes follow, and they are different. -/

/-- Continue at depth `k` when the value of one further step exceeds its
marginal confessed cost. -/
def ContinueAt (value : Nat → Nat) (unitCost p k : Nat) : Prop :=
  unitCost * ((k + 2) * p) < value k

/-- **Eventual domination.** With a ceiling on the value of one further step,
every cost-rational policy stops, and it stops by depth `vmax`. This is the
Confession Dominance regime: continuation is worth paying for at first and stops
being worth paying for later. -/
theorem bounded_value_stops (value : Nat → Nat) (vmax unitCost p : Nat)
    (hv : ∀ k, value k ≤ vmax) (hc : 1 ≤ unitCost) (hp : 1 ≤ p) :
    ∀ j, vmax ≤ j → ¬ ContinueAt value unitCost p j := by
  intro j hj
  unfold ContinueAt
  have hcost : vmax < unitCost * ((j + 2) * p) := by
    calc vmax < j + 2 := by omega
      _ = (j + 2) * 1 := by ring
      _ ≤ (j + 2) * p := Nat.mul_le_mul_left _ hp
      _ = 1 * ((j + 2) * p) := by ring
      _ ≤ unitCost * ((j + 2) * p) := Nat.mul_le_mul_right _ hc
  exact fun h => absurd (Nat.lt_of_le_of_lt (hv j) hcost) (Nat.not_lt.mpr (Nat.le_of_lt h))

/-- **Immediate domination.** When one further step carries zero value,
continuation is dominated at every depth, including the first. No crossing is
needed and no budget is consumed. This is the Echo regime, and it is strictly
stronger than the Confession regime: it consumes neither the positive-cost
hypothesis nor the nonzero-payload hypothesis, so it holds unconditionally. -/
theorem zero_value_never_continues (unitCost p k : Nat) :
    ¬ ContinueAt (fun _ => 0) unitCost p k := by
  unfold ContinueAt
  exact Nat.not_lt.mpr (Nat.zero_le _)

/-- **The two stopping regimes, separated.** A zero-value channel is dominated
at depth zero; a bounded-value channel is dominated only from `vmax` onward.
The first needs no budget, the second sets one. -/
theorem stopping_regimes_separate (value : Nat → Nat) (vmax unitCost p : Nat)
    (hv : ∀ k, value k ≤ vmax) (hc : 1 ≤ unitCost) (hp : 1 ≤ p) :
    (∀ k, ¬ ContinueAt (fun _ => 0) unitCost p k)
      ∧ (∀ j, vmax ≤ j → ¬ ContinueAt value unitCost p j) :=
  ⟨fun k => zero_value_never_continues unitCost p k,
    bounded_value_stops value vmax unitCost p hv hc hp⟩

end OperatorKO7.Meta.ConfessionCrossingPoint
