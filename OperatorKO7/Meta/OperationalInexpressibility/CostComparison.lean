import OperatorKO7.Meta.ConfessionCrossingPoint
import OperatorKO7.Meta.Decision.EchoStoppingMDP
import OperatorKO7.Meta.Decision.RecursorStopping
import OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms

/-!
# Complete cost comparison for the Operational Inexpressibility recursor

This module completes the doubled-cost comparison already defined by
`ConfessionCrossingPoint`.  It keeps weak crossing, strict crossing and ties
separate, covers zero payload and zero denominator cases, and reuses the
finite-horizon stopping theorem rather than replacing it with a static rule.

The quantities are logical accounting quantities.  No physical heat claim is
made here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.CostComparison

open OperatorKO7.Meta.ConfessionCrossingPoint
open OperatorKO7.Meta.Decision.EchoStopping
open OperatorKO7.Meta.Decision.RecursorStopping
open OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms

/-- The direct carry burden is no smaller than the confession burden. -/
def WeakCrossing (payload licenseCost depth : Nat) : Prop :=
  confessExitCostDoubled licenseCost depth ≤ directCarryCostDoubled depth payload

/-- The two doubled burdens are equal. -/
def CostTie (payload licenseCost depth : Nat) : Prop :=
  directCarryCostDoubled depth payload = confessExitCostDoubled licenseCost depth

instance weakCrossingDecidable (payload licenseCost : Nat) :
    DecidablePred (WeakCrossing payload licenseCost) := fun depth =>
  inferInstanceAs (Decidable
    (confessExitCostDoubled licenseCost depth ≤ directCarryCostDoubled depth payload))

instance costTieDecidable (payload licenseCost : Nat) :
    DecidablePred (CostTie payload licenseCost) := fun depth =>
  inferInstanceAs (Decidable
    (directCarryCostDoubled depth payload = confessExitCostDoubled licenseCost depth))

@[simp] theorem weakCrossing_iff (payload licenseCost depth : Nat) :
    WeakCrossing payload licenseCost depth ↔
      2 * licenseCost + 2 * depth ≤ (depth + 1) * (depth + 2) * payload := by
  rfl

@[simp] theorem costTie_iff (payload licenseCost depth : Nat) :
    CostTie payload licenseCost depth ↔
      (depth + 1) * (depth + 2) * payload = 2 * licenseCost + 2 * depth := by
  rfl

/-- Complete three-way cost comparison at one depth. -/
inductive BurdenOrder where
  | carryCheaper
  | tie
  | confessCheaper
deriving DecidableEq, Repr

/-- Executable comparison of the two doubled natural-number burdens. -/
def compareBurden (payload licenseCost depth : Nat) : BurdenOrder :=
  let carry := directCarryCostDoubled depth payload
  let confess := confessExitCostDoubled licenseCost depth
  if carry < confess then .carryCheaper
  else if carry = confess then .tie
  else .confessCheaper

@[simp] theorem compareBurden_eq_carryCheaper_iff (payload licenseCost depth : Nat) :
    compareBurden payload licenseCost depth = .carryCheaper ↔
      directCarryCostDoubled depth payload < confessExitCostDoubled licenseCost depth := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  change (if c < e then BurdenOrder.carryCheaper
      else if c = e then BurdenOrder.tie else BurdenOrder.confessCheaper) =
      BurdenOrder.carryCheaper ↔ c < e
  by_cases h : c < e
  · simp [h]
  · by_cases heq : c = e <;> simp [h, heq]

@[simp] theorem compareBurden_eq_tie_iff (payload licenseCost depth : Nat) :
    compareBurden payload licenseCost depth = .tie ↔ CostTie payload licenseCost depth := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  change (if c < e then BurdenOrder.carryCheaper
      else if c = e then BurdenOrder.tie else BurdenOrder.confessCheaper) =
      BurdenOrder.tie ↔ c = e
  by_cases hlt : c < e
  · have hne : c ≠ e := ne_of_lt hlt
    simp [hlt, hne]
  · by_cases heq : c = e <;> simp [hlt, heq]

@[simp] theorem compareBurden_eq_confessCheaper_iff (payload licenseCost depth : Nat) :
    compareBurden payload licenseCost depth = .confessCheaper ↔
      confessExitCostDoubled licenseCost depth < directCarryCostDoubled depth payload := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  change (if c < e then BurdenOrder.carryCheaper
      else if c = e then BurdenOrder.tie else BurdenOrder.confessCheaper) =
      BurdenOrder.confessCheaper ↔ e < c
  by_cases hlt : c < e
  · have hnot : ¬ e < c := by omega
    simp [hlt, hnot]
  · by_cases heq : c = e
    · simp [heq]
    · have hgt : e < c := by omega
      simp [hlt, heq, hgt]

/-- Zero payload has one equality case only: both the license price and the
selected depth are zero. -/
theorem zero_payload_tie_iff (licenseCost depth : Nat) :
    CostTie 0 licenseCost depth ↔ licenseCost = 0 ∧ depth = 0 := by
  simp [CostTie, directCarryCostDoubled, confessExitCostDoubled]
  omega

/-- Zero payload never reaches a strict crossing. -/
theorem zero_payload_never_strict (licenseCost depth : Nat) :
    ¬ CarryExceedsConfess 0 licenseCost depth :=
  no_crossing_of_zero_payload licenseCost depth

/-- With positive payload, a tie can occur at at most one depth. -/
theorem tie_depth_unique_of_payload_pos
    {payload licenseCost i j : Nat} (hp : 1 ≤ payload)
    (hi : CostTie payload licenseCost i)
    (hj : CostTie payload licenseCost j) : i = j := by
  let f : Nat → Int := fun depth =>
    (directCarryCostDoubled depth payload : Int) -
      (confessExitCostDoubled licenseCost depth : Int)
  have hfstep : ∀ depth, f depth < f (depth + 1) := by
    intro depth
    simp [f, directCarryCostDoubled, confessExitCostDoubled]
    nlinarith
  have hfmono : StrictMono f := strictMono_nat_of_lt_succ hfstep
  have hfi : f i = 0 := by
    unfold CostTie at hi
    change (directCarryCostDoubled i payload : Int) -
      (confessExitCostDoubled licenseCost i : Int) = 0
    rw [hi]
    simp
  have hfj : f j = 0 := by
    unfold CostTie at hj
    change (directCarryCostDoubled j payload : Int) -
      (confessExitCostDoubled licenseCost j : Int) = 0
    rw [hj]
    simp
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have := hfmono hij
    omega
  · have := hfmono hji
    omega

/-- A positive payload has a weak crossing because the already proved strict
crossing is also weak. -/
theorem weak_crossing_exists (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    ∃ depth, WeakCrossing payload licenseCost depth := by
  obtain ⟨depth, hdepth⟩ := crossing_exists payload licenseCost hp
  exact ⟨depth, Nat.le_of_lt hdepth⟩

/-- Least depth where direct carry is at least confession. The predicate is
decidable, so this least search is computable in the same sense as the existing
strict crossing point. -/
def weakCrossingPoint (payload licenseCost : Nat) (hp : 1 ≤ payload) : Nat :=
  Nat.find (weak_crossing_exists payload licenseCost hp)

theorem weakCrossingPoint_spec (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    WeakCrossing payload licenseCost (weakCrossingPoint payload licenseCost hp) := by
  exact Nat.find_spec (weak_crossing_exists payload licenseCost hp)

theorem weakCrossingPoint_least (payload licenseCost : Nat) (hp : 1 ≤ payload)
    {depth : Nat} (hdepth : depth < weakCrossingPoint payload licenseCost hp) :
    ¬ WeakCrossing payload licenseCost depth := by
  exact Nat.find_min (weak_crossing_exists payload licenseCost hp) hdepth

/-- Executable weak-threshold search. The search bound is the declared license
price because positive payloads cross by that depth. -/
def weakCrossingPoint? (payload licenseCost : Nat) : Option Nat :=
  boundedWitnessRank? licenseCost
    (fun depth => decide (WeakCrossing payload licenseCost depth))

/-- Executable strict-threshold search over the same finite window. -/
def strictCrossingPoint? (payload licenseCost : Nat) : Option Nat :=
  boundedWitnessRank? licenseCost
    (fun depth => decide (CarryExceedsConfess payload licenseCost depth))

/-- For positive payload, the executable weak search returns the mathematical
least weak crossing. -/
theorem weakCrossingPoint?_eq_some
    (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    weakCrossingPoint? payload licenseCost =
      some (weakCrossingPoint payload licenseCost hp) := by
  have hbound : weakCrossingPoint payload licenseCost hp ≤ licenseCost :=
    Nat.find_min' (weak_crossing_exists payload licenseCost hp)
      (Nat.le_of_lt (carry_exceeds_at_licenseCost payload licenseCost hp))
  by_cases hnone : weakCrossingPoint? payload licenseCost = none
  · have hall := (boundedWitnessRank?_eq_none_iff licenseCost
      (fun depth => decide (WeakCrossing payload licenseCost depth))).1 hnone
    have hfalse := hall (weakCrossingPoint payload licenseCost hp) hbound
    have hnot : ¬ WeakCrossing payload licenseCost
        (weakCrossingPoint payload licenseCost hp) := by
      intro hw
      have htrue := decide_eq_true hw
      rw [hfalse] at htrue
      contradiction
    exact (hnot (weakCrossingPoint_spec payload licenseCost hp)).elim
  · cases hsearch : weakCrossingPoint? payload licenseCost with
    | none => exact (hnone hsearch).elim
    | some n =>
        have hs : WeakCrossing payload licenseCost n :=
          of_decide_eq_true (boundedWitnessRank?_sound_bool hsearch)
        have hnle : weakCrossingPoint payload licenseCost hp ≤ n :=
          Nat.find_min' (weak_crossing_exists payload licenseCost hp) hs
        have hnmin := boundedWitnessRank?_minimal hsearch
        have hrev : n ≤ weakCrossingPoint payload licenseCost hp := by
          by_contra hnotle
          have hlt : weakCrossingPoint payload licenseCost hp < n :=
            Nat.lt_of_not_ge hnotle
          have hfalse := hnmin _ hlt
          have hnot : ¬ WeakCrossing payload licenseCost
              (weakCrossingPoint payload licenseCost hp) := by
            intro hw
            have htrue := decide_eq_true hw
            rw [hfalse] at htrue
            contradiction
          exact (hnot (weakCrossingPoint_spec payload licenseCost hp)).elim
        have heq : n = weakCrossingPoint payload licenseCost hp :=
          Nat.le_antisymm hrev hnle
        exact congrArg some heq

/-- For positive payload, the executable strict search returns the existing
strict crossing point. -/
theorem strictCrossingPoint?_eq_some
    (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    strictCrossingPoint? payload licenseCost =
      some (crossingPoint payload licenseCost hp) := by
  have hbound := crossingPoint_le_licenseCost payload licenseCost hp
  by_cases hnone : strictCrossingPoint? payload licenseCost = none
  · have hall := (boundedWitnessRank?_eq_none_iff licenseCost
      (fun depth => decide (CarryExceedsConfess payload licenseCost depth))).1 hnone
    have hfalse := hall (crossingPoint payload licenseCost hp) hbound
    have htrue : decide (CarryExceedsConfess payload licenseCost
      (crossingPoint payload licenseCost hp)) = true := by
      simp [crossingPoint_spec payload licenseCost hp]
    simp [htrue] at hfalse
  · cases hsearch : strictCrossingPoint? payload licenseCost with
    | none => exact (hnone hsearch).elim
    | some n =>
        have hs : CarryExceedsConfess payload licenseCost n :=
          of_decide_eq_true (boundedWitnessRank?_sound_bool hsearch)
        have hnle : crossingPoint payload licenseCost hp ≤ n :=
          (carry_exceeds_iff_crossingPoint_le payload licenseCost hp n).1 hs
        have hnmin := boundedWitnessRank?_minimal hsearch
        have hrev : n ≤ crossingPoint payload licenseCost hp := by
          by_contra hnot
          have hlt : crossingPoint payload licenseCost hp < n := Nat.lt_of_not_ge hnot
          have hfalse := hnmin _ hlt
          have htrue : decide (CarryExceedsConfess payload licenseCost
            (crossingPoint payload licenseCost hp)) = true := by
            simp [crossingPoint_spec payload licenseCost hp]
          simp [htrue] at hfalse
        have heq : n = crossingPoint payload licenseCost hp :=
          Nat.le_antisymm hrev hnle
        exact congrArg some heq

/-- Zero payload has a weak threshold only in the zero-price case. -/
theorem weakCrossingPoint?_zero_payload (licenseCost : Nat) :
    weakCrossingPoint? 0 licenseCost = if licenseCost = 0 then some 0 else none := by
  cases licenseCost with
  | zero => simp [weakCrossingPoint?, boundedWitnessRank?, WeakCrossing,
      directCarryCostDoubled, confessExitCostDoubled]
  | succ licenseCost =>
      simp only [Nat.succ_ne_zero, if_false]
      unfold weakCrossingPoint?
      apply (boundedWitnessRank?_eq_none_iff (licenseCost + 1) _).2
      intro depth hdepth
      simp [WeakCrossing, directCarryCostDoubled, confessExitCostDoubled]

/-- Zero payload has no strict crossing inside any finite window. -/
theorem strictCrossingPoint?_zero_payload (licenseCost : Nat) :
    strictCrossingPoint? 0 licenseCost = none := by
  apply (boundedWitnessRank?_eq_none_iff licenseCost _).2
  intro n hn
  simp [CarryExceedsConfess, directCarryCostDoubled, confessExitCostDoubled]

/-- The weak threshold is no later than the strict threshold. -/
theorem weakCrossingPoint_le_crossingPoint
    (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    weakCrossingPoint payload licenseCost hp ≤ crossingPoint payload licenseCost hp := by
  exact Nat.find_min' (weak_crossing_exists payload licenseCost hp)
    (Nat.le_of_lt (crossingPoint_spec payload licenseCost hp))

/-- The first strict crossing is either the first weak crossing or its immediate
successor. -/
theorem crossingPoint_le_weakCrossingPoint_succ
    (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    crossingPoint payload licenseCost hp ≤ weakCrossingPoint payload licenseCost hp + 1 := by
  apply (carry_exceeds_iff_crossingPoint_le payload licenseCost hp
    (weakCrossingPoint payload licenseCost hp + 1)).1
  have hw := weakCrossingPoint_spec payload licenseCost hp
  unfold WeakCrossing at hw
  unfold CarryExceedsConfess
  simp only [directCarryCostDoubled_eq, confessExitCostDoubled_eq] at hw ⊢
  have hp' : 0 < payload := by omega
  nlinarith

/-- A tie at the weak threshold forces the strict threshold to be the next
depth. -/
theorem crossingPoint_eq_weak_succ_of_tie
    (payload licenseCost : Nat) (hp : 1 ≤ payload)
    (htie : CostTie payload licenseCost (weakCrossingPoint payload licenseCost hp)) :
    crossingPoint payload licenseCost hp = weakCrossingPoint payload licenseCost hp + 1 := by
  have hbounds := crossingPoint_le_weakCrossingPoint_succ payload licenseCost hp
  have hweak := weakCrossingPoint_le_crossingPoint payload licenseCost hp
  have hnot : ¬ crossingPoint payload licenseCost hp ≤ weakCrossingPoint payload licenseCost hp := by
    intro hle
    have hs := (carry_exceeds_iff_crossingPoint_le payload licenseCost hp
      (weakCrossingPoint payload licenseCost hp)).2 hle
    unfold CostTie at htie
    unfold CarryExceedsConfess at hs
    omega
  omega

/-- If the weak threshold is already strict, both thresholds coincide. -/
theorem crossingPoint_eq_weak_of_strict
    (payload licenseCost : Nat) (hp : 1 ≤ payload)
    (hstrict : CarryExceedsConfess payload licenseCost
      (weakCrossingPoint payload licenseCost hp)) :
    crossingPoint payload licenseCost hp = weakCrossingPoint payload licenseCost hp := by
  apply Nat.le_antisymm
  · exact (carry_exceeds_iff_crossingPoint_le payload licenseCost hp _).1 hstrict
  · exact weakCrossingPoint_le_crossingPoint payload licenseCost hp

/-- The weak threshold is a tie exactly when the strict threshold is one step
later. -/
theorem weak_tie_iff_strict_threshold_next
    (payload licenseCost : Nat) (hp : 1 ≤ payload) :
    CostTie payload licenseCost (weakCrossingPoint payload licenseCost hp) ↔
      crossingPoint payload licenseCost hp = weakCrossingPoint payload licenseCost hp + 1 := by
  constructor
  · exact crossingPoint_eq_weak_succ_of_tie payload licenseCost hp
  · intro hnext
    have hw := weakCrossingPoint_spec payload licenseCost hp
    have hns : ¬ CarryExceedsConfess payload licenseCost
        (weakCrossingPoint payload licenseCost hp) := by
      intro hs
      have hle := (carry_exceeds_iff_crossingPoint_le payload licenseCost hp _).1 hs
      omega
    unfold WeakCrossing at hw
    unfold CarryExceedsConfess at hns
    unfold CostTie
    omega

/-- Signed pointwise difference between direct carry and confession costs. -/
def costDifferenceDoubled (payload licenseCost depth : Nat) : Int :=
  (directCarryCostDoubled depth payload : Int) -
    (confessExitCostDoubled licenseCost depth : Int)

/-- For positive payload, the signed cost difference grows strictly with depth. -/
theorem costDifferenceDoubled_strict_growth
    (payload licenseCost depth : Nat) (hp : 1 ≤ payload) :
    costDifferenceDoubled payload licenseCost depth <
      costDifferenceDoubled payload licenseCost (depth + 1) := by
  simp [costDifferenceDoubled, directCarryCostDoubled, confessExitCostDoubled]
  nlinarith

/-- Sum of direct doubled carry burdens from depth zero through `horizon`. -/
def cumulativeCarryDoubled (payload horizon : Nat) : Nat :=
  ∑ depth ∈ Finset.range (horizon + 1), directCarryCostDoubled depth payload

/-- Sum of doubled confession burdens from depth zero through `horizon`. -/
def cumulativeConfessDoubled (licenseCost horizon : Nat) : Nat :=
  ∑ depth ∈ Finset.range (horizon + 1), confessExitCostDoubled licenseCost depth

@[simp] theorem cumulativeCarryDoubled_zero (payload : Nat) :
    cumulativeCarryDoubled payload 0 = 2 * payload := by
  simp [cumulativeCarryDoubled]

@[simp] theorem cumulativeConfessDoubled_zero (licenseCost : Nat) :
    cumulativeConfessDoubled licenseCost 0 = 2 * licenseCost := by
  simp [cumulativeConfessDoubled]

/-- Division-free recurrence for the all-depth carry burden. -/
theorem cumulativeCarryDoubled_succ (payload horizon : Nat) :
    cumulativeCarryDoubled payload (horizon + 1) =
      cumulativeCarryDoubled payload horizon +
        directCarryCostDoubled (horizon + 1) payload := by
  simp [cumulativeCarryDoubled, Finset.sum_range_succ]

/-- Division-free recurrence for the all-depth confession burden. -/
theorem cumulativeConfessDoubled_succ (licenseCost horizon : Nat) :
    cumulativeConfessDoubled licenseCost (horizon + 1) =
      cumulativeConfessDoubled licenseCost horizon +
        confessExitCostDoubled licenseCost (horizon + 1) := by
  simp [cumulativeConfessDoubled, Finset.sum_range_succ]

/-- Closed all-depth carry identity. This sum is cubic in the horizon and is
separate from the original single-trace quadratic burden. -/
theorem cumulativeCarryDoubled_closed (payload horizon : Nat) :
    3 * cumulativeCarryDoubled payload horizon =
      (horizon + 1) * (horizon + 2) * (horizon + 3) * payload := by
  induction horizon with
  | zero =>
      rw [cumulativeCarryDoubled_zero]
      ring
  | succ horizon ih =>
      rw [cumulativeCarryDoubled_succ]
      calc
        3 * (cumulativeCarryDoubled payload horizon +
            directCarryCostDoubled (horizon + 1) payload) =
            3 * cumulativeCarryDoubled payload horizon +
              3 * directCarryCostDoubled (horizon + 1) payload := by ring
        _ = (horizon + 2) * (horizon + 3) * (horizon + 4) * payload := by
          rw [ih]
          simp [directCarryCostDoubled]
          ring

/-- Closed all-depth confession identity. -/
theorem cumulativeConfessDoubled_closed (licenseCost horizon : Nat) :
    cumulativeConfessDoubled licenseCost horizon =
      2 * licenseCost * (horizon + 1) + horizon * (horizon + 1) := by
  induction horizon with
  | zero => simp [cumulativeConfessDoubled_zero]
  | succ horizon ih =>
      rw [cumulativeConfessDoubled_succ, ih]
      simp [confessExitCostDoubled]
      ring

/-- An optional rational ratio between direct carry cost and confession cost.
This is not the carry-to-residual-work ratio. -/
def burdenRatio? (payload licenseCost depth : Nat) : Option ℚ :=
  if confessExitCostDoubled licenseCost depth = 0 then none
  else some ((directCarryCostDoubled depth payload : ℚ) /
    (confessExitCostDoubled licenseCost depth : ℚ))

@[simp] theorem burdenRatio?_eq_none_iff (payload licenseCost depth : Nat) :
    burdenRatio? payload licenseCost depth = none ↔ licenseCost = 0 ∧ depth = 0 := by
  simp [burdenRatio?, confessExitCostDoubled]

/-- The ratio is available exactly outside the zero-denominator case. -/
theorem burdenRatio?_isSome_iff (payload licenseCost depth : Nat) :
    (burdenRatio? payload licenseCost depth).isSome ↔
      ¬ (licenseCost = 0 ∧ depth = 0) := by
  rw [Option.isSome_iff_ne_none, ne_eq, burdenRatio?_eq_none_iff]

/-- Direct carrying burden divided by the actual residual work `depth`. Doubled
units are used in numerator and denominator, so the ratio equals `Carry/Res`.
Depth zero has no ratio. -/
def carryResidualRatio? (payload depth : Nat) : Option ℚ :=
  if depth = 0 then none
  else some ((directCarryCostDoubled depth payload : ℚ) / (2 * depth : ℚ))

@[simp] theorem carryResidualRatio?_eq_none_iff (payload depth : Nat) :
    carryResidualRatio? payload depth = none ↔ depth = 0 := by
  simp [carryResidualRatio?]

/-- Positive depth exposes the exact carry-to-residual rational expression. -/
theorem carryResidualRatio?_eq_some_of_pos
    (payload depth : Nat) (hdepth : 0 < depth) :
    carryResidualRatio? payload depth =
      some (((depth + 1) * (depth + 2) * payload : ℚ) / (2 * depth : ℚ)) := by
  have hne : depth ≠ 0 := Nat.ne_of_gt hdepth
  simp [carryResidualRatio?, hne, directCarryCostDoubled]

inductive CostAction where
  | carry
  | confess
deriving DecidableEq, Repr

/-- Every minimizing action is retained, so ties contain both actions. -/
def optimalActions (payload licenseCost depth : Nat) : Finset CostAction :=
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  if c < e then {CostAction.carry}
  else if e < c then {CostAction.confess}
  else {CostAction.carry, CostAction.confess}

@[simp] theorem optimalActions_tie
    {payload licenseCost depth : Nat} (h : CostTie payload licenseCost depth) :
    optimalActions payload licenseCost depth = {CostAction.carry, CostAction.confess} := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  have heq : c = e := by simpa [c, e, CostTie] using h
  change (if c < e then {CostAction.carry}
    else if e < c then {CostAction.confess}
    else {CostAction.carry, CostAction.confess}) =
      {CostAction.carry, CostAction.confess}
  simp [heq]

inductive TieBreakPolicy where
  | preferCarry
  | preferConfess
deriving DecidableEq, Repr

/-- A deterministic selection from the tie-preserving optimal action set. -/
def chooseOptimal (policy : TieBreakPolicy) (payload licenseCost depth : Nat) : CostAction :=
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  if c < e then .carry
  else if e < c then .confess
  else match policy with
    | .preferCarry => .carry
    | .preferConfess => .confess

/-- Every tie-breaking policy selects a member of the complete minimizing set. -/
theorem chooseOptimal_mem_optimalActions
    (policy : TieBreakPolicy) (payload licenseCost depth : Nat) :
    chooseOptimal policy payload licenseCost depth ∈
      optimalActions payload licenseCost depth := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  change (if c < e then CostAction.carry else if e < c then CostAction.confess else
      match policy with
      | TieBreakPolicy.preferCarry => CostAction.carry
      | TieBreakPolicy.preferConfess => CostAction.confess) ∈
    (if c < e then {CostAction.carry} else if e < c then {CostAction.confess}
      else {CostAction.carry, CostAction.confess})
  by_cases hcf : c < e
  · simp [hcf]
  · by_cases hfc : e < c
    · simp [hcf, hfc]
    · cases policy <;> simp [hcf, hfc]

/-- The two policies differ exactly on a cost tie. -/
theorem tieBreakPolicies_differ_iff (payload licenseCost depth : Nat) :
    chooseOptimal .preferCarry payload licenseCost depth ≠
      chooseOptimal .preferConfess payload licenseCost depth ↔
        CostTie payload licenseCost depth := by
  let c := directCarryCostDoubled depth payload
  let e := confessExitCostDoubled licenseCost depth
  change (if c < e then CostAction.carry else if e < c then CostAction.confess
      else CostAction.carry) ≠
      (if c < e then CostAction.carry else if e < c then CostAction.confess
      else CostAction.confess) ↔ c = e
  by_cases hcf : c < e
  · have hne : c ≠ e := ne_of_lt hcf
    simp [hcf, hne]
  · by_cases hfc : e < c
    · have hne : c ≠ e := Ne.symm (ne_of_lt hfc)
      simp [hcf, hfc, hne]
    · have heq : c = e := by omega
      simp [heq]

/-- The finite-horizon stopping theorem reused by this cost surface. -/
theorem finite_horizon_stop_iff_edge_bound
    {S Q : Type} [DecidableEq S]
    (M : EchoStoppingMDP S Q) :
    (∀ n s, horizonValue M n s = M.stopValue s) ↔
      ∀ s t, t ∈ M.successors s →
        M.currentGain s + M.stopValue t - M.computeCost s ≤ M.stopValue s :=
  horizonValue_eq_stop_iff_edge_bound M

/-- Positive unit price and positive payload give the existing finite binary
stopping cutoff for constant bounded benefit. -/
theorem positive_price_binary_stopping_region
    (benefitBound unitCost payload k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) :
    (∀ n,
      OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value
        (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
          unitCost payload 1) n k = 0) ↔
      binaryMarginalCutoff benefitBound (unitCost * payload) ≤ k :=
  binary_constantBenefit_all_horizons_stop_iff benefitBound unitCost payload k hunit hpayload

/-- Zero immediate gain alone is insufficient for stopping because a larger
future stop reward can dominate positive cost. -/
theorem zero_gain_alone_not_a_stopping_rule :
    realizedFutureGainFixture.currentGain false = 0 ∧
      realizedFutureGainFixture.computeCost false = 1 ∧
      horizonPolicy realizedFutureGainFixture 1 false = .compute := by
  exact ⟨rfl, rfl, realizedFutureGainFixture_computes.2.2.2⟩

end OperatorKO7.Meta.OperationalInexpressibility.CostComparison
