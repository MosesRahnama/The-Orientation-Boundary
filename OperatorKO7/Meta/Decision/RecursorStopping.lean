import OperatorKO7.Meta.Decision.EchoStoppingMDP
import OperatorKO7.Meta.ConfessionCrossingPoint
import OperatorKO7.Meta.Recursor.RaryDuplicatorLaws
import Mathlib.Algebra.Order.Floor.Div

/-!
# Exact stopping law for duplicating recursors

The cumulative price is read from the live `r`-ary recursor orbit.  Its
increment is the payload multiplicity of the newly exposed stage.  The induced
finite-support decision model has an exact least stopping depth, and immediate
stopping is optimal there at every finite horizon against every adaptive policy.

The binary law is the specialization `r = 1`.  Arity zero, zero payload, zero
unit price, and future-value growth are explicit controls.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Decision.RecursorStopping

open OperatorKO7.Meta.Decision.EchoStopping
open OperatorKO7.Meta.Decision.EchoStopping.Stochastic
open OperatorKO7.Meta.Recursor.GaugeCost
open OperatorKO7.Meta.Recursor.RaryDuplicator
open OperatorKO7.Meta.Recursor.RaryDuplicatorLaws
open OperatorKO7.Meta.Recursor.TraceAction

/-! ## Execution-derived cumulative and marginal prices -/

/-- Cumulative payload price through depth `k` for an `r`-ary recursor. -/
def raryCumulativeCost (k unitCost payload arity : Nat) : Nat :=
  unitCost * conMassR k payload arity

/-- The number of payload copies in the next live state. -/
def raryMarginalCopies (k arity : Nat) : Nat :=
  arity * (k + 1) + 1

/-- Price of extending the recursor computation from depth `k` to `k+1`. -/
def raryMarginalCost (k unitCost payload arity : Nat) : Nat :=
  (unitCost * payload) * raryMarginalCopies k arity

/-- The binary cumulative price. -/
def binaryCumulativeCost (k payload : Nat) : Nat :=
  conMassR k payload 1

/-- The arbitrary-arity cumulative price is the sum of payload multiplicities
on the actual live orbit. -/
theorem raryCumulativeCost_eq_live_sum
    (ia ib k unitCost payload arity : Nat) :
    raryCumulativeCost k unitCost payload arity =
      unitCost *
        (∑ i ∈ Finset.range (k + 1),
          countPayR (rOrbit (.base ia) (.pay ib) k arity i) * payload) := by
  rw [raryCumulativeCost, conMassR_eq_live_sum]

/-- The marginal copy count is read from the next live orbit state. -/
theorem raryMarginalCopies_eq_live_next
    (ia ib k arity : Nat) :
    raryMarginalCopies k arity =
      countPayR (rOrbit (.base ia) (.pay ib) (k + 1) arity (k + 1)) := by
  rw [L10_trace_law_r ia ib (k + 1) arity (k + 1) (Nat.le_refl _)]
  rfl

/-- The marginal price is the unit price times the live next-stage payload. -/
theorem raryMarginalCost_eq_live_next
    (ia ib k unitCost payload arity : Nat) :
    raryMarginalCost k unitCost payload arity =
      unitCost *
        (countPayR (rOrbit (.base ia) (.pay ib) (k + 1) arity (k + 1)) * payload) := by
  rw [← raryMarginalCopies_eq_live_next ia ib k arity]
  simp [raryMarginalCost]
  ring

/-- Cumulative cost grows by exactly the execution-derived marginal price. -/
theorem raryCumulativeCost_succ
    (k unitCost payload arity : Nat) :
    raryCumulativeCost (k + 1) unitCost payload arity =
      raryCumulativeCost k unitCost payload arity +
        raryMarginalCost k unitCost payload arity := by
  unfold raryCumulativeCost raryMarginalCost raryMarginalCopies conMassR
  rw [show tri (k + 1) = tri k + (k + 1) by rfl]
  ring

/-- Extending the selected depth by one appends exactly the priced live stage
from the longer actual recursor execution. -/
theorem raryCumulativeCost_succ_eq_actual_live_extension
    (ia ib k unitCost payload arity : Nat) :
    raryCumulativeCost (k + 1) unitCost payload arity =
      raryCumulativeCost k unitCost payload arity +
        unitCost *
          (countPayR (rOrbit (.base ia) (.pay ib) (k + 1) arity (k + 1)) * payload) := by
  rw [raryCumulativeCost_succ,
    raryMarginalCost_eq_live_next ia ib k unitCost payload arity]

/-- Binary cumulative cost is the triangular payload sum. -/
theorem binaryCumulativeCost_eq_tri (k payload : Nat) :
    binaryCumulativeCost k payload = tri (k + 1) * payload := by
  simpa [binaryCumulativeCost] using conMassR_one k payload

/-- Division-free form of `C(k)=p(k+1)(k+2)/2`. -/
theorem binaryCumulativeCost_doubled (k payload : Nat) :
    2 * binaryCumulativeCost k payload = (k + 1) * (k + 2) * payload := by
  rw [binaryCumulativeCost_eq_tri]
  calc
    2 * (tri (k + 1) * payload) = (2 * tri (k + 1)) * payload := by ring
    _ = ((k + 1) * (k + 2)) * payload := by rw [two_mul_tri]
    _ = (k + 1) * (k + 2) * payload := rfl

/-- Binary cumulative cost is a sum over the actual binary recursor orbit. -/
theorem binaryCumulativeCost_eq_live_sum (ia ib k payload : Nat) :
    binaryCumulativeCost k payload =
      ∑ i ∈ Finset.range (k + 1),
        countPayR (rOrbit (.base ia) (.pay ib) k 1 i) * payload := by
  simpa [binaryCumulativeCost] using conMassR_eq_live_sum ia ib k 1 payload

/-- The binary marginal cost is `(k+2)p`. -/
theorem binaryCumulativeCost_succ (k payload : Nat) :
    binaryCumulativeCost (k + 1) payload =
      binaryCumulativeCost k payload + (k + 2) * payload := by
  have h := raryCumulativeCost_succ k 1 payload 1
  simpa [binaryCumulativeCost, raryCumulativeCost, raryMarginalCost,
    raryMarginalCopies, Nat.mul_comm, Nat.add_assoc] using h

/-- Runtime descent remains `k+1` at every arity even though cumulative copy
cost depends on arity. -/
theorem runtime_descent_separate_from_copy_cost
    (ia ib ia' ib' k arity arity' unitCost payload : Nat) :
    RStepsTo arity (rOrbit (.base ia) (.pay ib) k arity 0) (k + 1)
        (rOrbit (.base ia) (.pay ib) k arity (k + 1)) ∧
      RStepsTo arity' (rOrbit (.base ia') (.pay ib') k arity' 0) (k + 1)
        (rOrbit (.base ia') (.pay ib') k arity' (k + 1)) ∧
      raryCumulativeCost k unitCost payload arity =
        unitCost * conMassR k payload arity :=
  ⟨(L10_runtime_r_blind ia ib ia' ib' k arity arity').1,
    (L10_runtime_r_blind ia ib ia' ib' k arity arity').2,
    rfl⟩

/-- Every decision depth is backed by an actual terminating recursor execution
of exactly `k+1` rewrite steps. -/
theorem decisionDepth_has_actual_execution (ia ib k arity : Nat) :
    RStepsTo arity (rOrbit (.base ia) (.pay ib) k arity 0) (k + 1)
      (rOrbit (.base ia) (.pay ib) k arity (k + 1)) :=
  (L10_runtime_r_blind ia ib ia ib k arity arity).1

/-! ## Exact least cutoff -/

/-- Least depth whose `r`-ary marginal price reaches the benefit bound. -/
def raryMarginalCutoff (benefitBound unitPayloadCost arity : Nat) : Nat :=
  (((benefitBound ⌈/⌉ unitPayloadCost) - 1) ⌈/⌉ arity) - 1

/-- Binary closed form of the cutoff. -/
def binaryMarginalCutoff (benefitBound unitPayloadCost : Nat) : Nat :=
  (benefitBound ⌈/⌉ unitPayloadCost) - 2

/-- Marginal price at the computed cutoff reaches the benefit bound. -/
theorem raryMarginalCutoff_spec
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) :
    benefitBound ≤ unitPayloadCost *
      (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) := by
  let q := benefitBound ⌈/⌉ unitPayloadCost
  let a := (q - 1) ⌈/⌉ arity
  have hbenefit : benefitBound ≤ unitPayloadCost * q :=
    (ceilDiv_le_iff_le_mul hcost).1 (Nat.le_refl q)
  have hqa : q - 1 ≤ arity * a :=
    (ceilDiv_le_iff_le_mul harity).1 (Nat.le_refl a)
  have haa : a ≤ (a - 1) + 1 := by omega
  have hq : q ≤ arity * ((a - 1) + 1) + 1 := by
    calc
      q ≤ (q - 1) + 1 := by omega
      _ ≤ arity * a + 1 := Nat.add_le_add_right hqa 1
      _ ≤ arity * ((a - 1) + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left arity haa) 1
  exact hbenefit.trans (Nat.mul_le_mul_left unitPayloadCost (by
    simpa [raryMarginalCutoff, q, a] using hq))

/-- No smaller depth reaches the benefit bound. -/
theorem raryMarginalCutoff_least
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity)
    {k : Nat}
    (hk : benefitBound ≤ unitPayloadCost * (arity * (k + 1) + 1)) :
    raryMarginalCutoff benefitBound unitPayloadCost arity ≤ k := by
  let q := benefitBound ⌈/⌉ unitPayloadCost
  let a := (q - 1) ⌈/⌉ arity
  have hq : q ≤ arity * (k + 1) + 1 :=
    (ceilDiv_le_iff_le_mul hcost).2 hk
  have hsub : q - 1 ≤ arity * (k + 1) := by omega
  have ha : a ≤ k + 1 := (ceilDiv_le_iff_le_mul harity).2 hsub
  change a - 1 ≤ k
  omega

/-- The cutoff exactly classifies the weak stopping-price region. -/
theorem raryMarginalCutoff_le_iff
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) (k : Nat) :
    raryMarginalCutoff benefitBound unitPayloadCost arity ≤ k ↔
      benefitBound ≤ unitPayloadCost * (arity * (k + 1) + 1) := by
  constructor
  · intro hk
    have hbase := raryMarginalCutoff_spec benefitBound unitPayloadCost arity hcost harity
    have hcopies :
        arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1 ≤
          arity * (k + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left arity (Nat.add_le_add_right hk 1)) 1
    exact hbase.trans (Nat.mul_le_mul_left unitPayloadCost hcopies)
  · exact raryMarginalCutoff_least benefitBound unitPayloadCost arity hcost harity

/-- Every depth below the cutoff has marginal price strictly below the bound. -/
theorem raryMarginalCost_lt_of_lt_cutoff
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity)
    {k : Nat}
    (hk : k < raryMarginalCutoff benefitBound unitPayloadCost arity) :
    unitPayloadCost * (arity * (k + 1) + 1) < benefitBound := by
  exact Nat.lt_of_not_ge (fun h =>
    (Nat.not_le_of_gt hk)
      (raryMarginalCutoff_least benefitBound unitPayloadCost arity hcost harity h))

/-- The binary cutoff is the `r=1` specialization of the general formula. -/
theorem raryMarginalCutoff_one (benefitBound unitPayloadCost : Nat) :
    raryMarginalCutoff benefitBound unitPayloadCost 1 =
      binaryMarginalCutoff benefitBound unitPayloadCost := by
  simp [raryMarginalCutoff, binaryMarginalCutoff]
  omega

/-- Least depth at which marginal price is strictly greater than the bound. -/
def raryStrictMarginalCutoff
    (benefitBound unitPayloadCost arity : Nat) : Nat :=
  raryMarginalCutoff (benefitBound + 1) unitPayloadCost arity

/-- Exact strict-price classification. -/
theorem raryStrictMarginalCutoff_le_iff
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) (k : Nat) :
    raryStrictMarginalCutoff benefitBound unitPayloadCost arity ≤ k ↔
      benefitBound < unitPayloadCost * (arity * (k + 1) + 1) := by
  rw [raryStrictMarginalCutoff,
    raryMarginalCutoff_le_iff (benefitBound + 1) unitPayloadCost arity hcost harity]
  omega

/-- Weak and strict cutoffs differ by at most one depth. -/
theorem rary_cutoff_le_strictCutoff_le_succ
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) :
    raryMarginalCutoff benefitBound unitPayloadCost arity ≤
        raryStrictMarginalCutoff benefitBound unitPayloadCost arity ∧
      raryStrictMarginalCutoff benefitBound unitPayloadCost arity ≤
        raryMarginalCutoff benefitBound unitPayloadCost arity + 1 := by
  constructor
  · apply raryMarginalCutoff_least benefitBound unitPayloadCost arity hcost harity
    have hs := (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
      hcost harity (raryStrictMarginalCutoff benefitBound unitPayloadCost arity)).1 le_rfl
    omega
  · apply (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
      hcost harity _).2
    have hw := (raryMarginalCutoff_le_iff benefitBound unitPayloadCost arity
      hcost harity (raryMarginalCutoff benefitBound unitPayloadCost arity)).1 le_rfl
    have hstep :
        unitPayloadCost *
            (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) <
          unitPayloadCost *
            (arity * ((raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) + 1) := by
      have hinc : 0 < unitPayloadCost * arity := Nat.mul_pos hcost harity
      nlinarith
    exact hw.trans_lt hstep

/-- The weak and strict cutoffs coincide exactly when the marginal price at
the weak cutoff is already strictly above the benefit bound. -/
theorem rary_cutoff_eq_strictCutoff_iff
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) :
    raryMarginalCutoff benefitBound unitPayloadCost arity =
        raryStrictMarginalCutoff benefitBound unitPayloadCost arity ↔
      benefitBound < unitPayloadCost *
        (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) := by
  constructor
  · intro hEq
    apply (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
      hcost harity _).1
    rw [← hEq]
  · intro hstrict
    apply Nat.le_antisymm
    · exact (rary_cutoff_le_strictCutoff_le_succ benefitBound unitPayloadCost arity
        hcost harity).1
    · exact (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
        hcost harity _).2 hstrict

/-- When the marginal price ties the bound at the weak cutoff, the first
strictly dominating depth is exactly the next one. -/
theorem rary_strictCutoff_eq_succ_iff_tie
    (benefitBound unitPayloadCost arity : Nat)
    (hcost : 0 < unitPayloadCost) (harity : 0 < arity) :
    raryStrictMarginalCutoff benefitBound unitPayloadCost arity =
        raryMarginalCutoff benefitBound unitPayloadCost arity + 1 ↔
      unitPayloadCost *
          (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) =
        benefitBound := by
  have hbounds := rary_cutoff_le_strictCutoff_le_succ benefitBound
    unitPayloadCost arity hcost harity
  have hweak := raryMarginalCutoff_spec benefitBound unitPayloadCost arity hcost harity
  constructor
  · intro hsucc
    apply Nat.le_antisymm
    · by_contra hnot
      have hstrict : benefitBound < unitPayloadCost *
          (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) :=
        Nat.lt_of_not_ge hnot
      have hle := (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
        hcost harity (raryMarginalCutoff benefitBound unitPayloadCost arity)).2 hstrict
      omega
    · exact hweak
  · intro htie
    have hnot : ¬ raryStrictMarginalCutoff benefitBound unitPayloadCost arity ≤
        raryMarginalCutoff benefitBound unitPayloadCost arity := by
      intro hle
      have hstrict : benefitBound < unitPayloadCost *
          (arity * (raryMarginalCutoff benefitBound unitPayloadCost arity + 1) + 1) := by
        exact (raryStrictMarginalCutoff_le_iff benefitBound unitPayloadCost arity
          hcost harity (raryMarginalCutoff benefitBound unitPayloadCost arity)).1 hle
      omega
    omega

/-! ## Deterministic finite-support Bellman model -/

/-- The deterministic next-depth model. `benefit` is current computational
reward and `stopValue` is the reward for stopping at a depth. -/
def recursorStoppingModel
    (benefit stopValue : Nat → ℝ) (unitCost payload arity : Nat) :
    Model Nat Unit where
  actions := fun _ => {()}
  support := fun k _ => {k + 1}
  probability := fun k _ t => if t = k + 1 then 1 else 0
  probability_nonneg := by
    intro k a ha t ht
    split <;> norm_num
  probability_sum := by
    intro k a ha
    simp
  stopValue := stopValue
  reward := fun k _ _ =>
    benefit k - (raryMarginalCost k unitCost payload arity : ℝ)

@[simp] theorem recursorStoppingModel_actions
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).actions k = {()} :=
  rfl

@[simp] theorem recursorStoppingModel_support
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) (a : Unit) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).support k a =
      {k + 1} :=
  rfl

/-- A decision transition extends the selected recursor depth by one. This is
an input-depth extension, not a rewrite step inside a fixed input. -/
def DepthExtension (k t : Nat) : Prop := t = k + 1

@[simp] theorem recursorStoppingModel_probability
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k t : Nat) (a : Unit) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).probability k a t =
      if t = k + 1 then 1 else 0 :=
  rfl

theorem recursorStoppingModel_support_iff_depthExtension
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k t : Nat) (a : Unit) :
    t ∈ (recursorStoppingModel benefit stopValue unitCost payload arity).support k a ↔
      DepthExtension k t := by
  simp [DepthExtension]

theorem recursorStoppingModel_positive_probability_iff_depthExtension
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k t : Nat) (a : Unit) :
    0 < (recursorStoppingModel benefit stopValue unitCost payload arity).probability k a t ↔
      DepthExtension k t := by
  by_cases ht : t = k + 1
  · simp [DepthExtension, recursorStoppingModel, ht]
  · simp [DepthExtension, recursorStoppingModel, ht]

@[simp] theorem recursorStoppingModel_stopValue
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k =
      stopValue k :=
  rfl

/-- The expected return is the declared benefit minus the execution-derived
marginal price plus the value at the unique next depth. -/
theorem recursorStoppingModel_expected
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat)
    (V : Nat → ℝ) (a : Unit) :
    expected (recursorStoppingModel benefit stopValue unitCost payload arity)
        V k a =
      benefit k - (raryMarginalCost k unitCost payload arity : ℝ) +
        V (k + 1) := by
  simp [expected, recursorStoppingModel]

/-! ## Exact finite-horizon solution for arbitrary rewards -/

/-- Net return from extending the selected depth once. -/
def recursorNetGain
    (benefit : Nat → ℝ) (unitCost payload arity k : Nat) : ℝ :=
  benefit k - (raryMarginalCost k unitCost payload arity : ℝ)

/-- Return obtained by extending the selected depth exactly `t` times and then
stopping. -/
def recursorPrefixReturn
    (benefit stopValue : Nat → ℝ) (unitCost payload arity : Nat) : Nat → Nat → ℝ
  | k, 0 => stopValue k
  | k, t + 1 =>
      recursorNetGain benefit unitCost payload arity k +
        recursorPrefixReturn benefit stopValue unitCost payload arity (k + 1) t

/-- Recursive maximum of all exact stopping-time returns with `t ≤ n`. -/
def recursorFiniteHorizonMaximum
    (benefit stopValue : Nat → ℝ) (unitCost payload arity : Nat) : Nat → Nat → ℝ
  | 0, k => stopValue k
  | n + 1, k =>
      max (stopValue k)
        (recursorNetGain benefit unitCost payload arity k +
          recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n (k + 1))

@[simp] theorem recursorPrefixReturn_zero
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    recursorPrefixReturn benefit stopValue unitCost payload arity k 0 = stopValue k :=
  rfl

@[simp] theorem recursorPrefixReturn_succ
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k t : Nat) :
    recursorPrefixReturn benefit stopValue unitCost payload arity k (t + 1) =
      recursorNetGain benefit unitCost payload arity k +
        recursorPrefixReturn benefit stopValue unitCost payload arity (k + 1) t :=
  rfl

/-- The recursive return is the stopping reward plus the sum of all preceding
execution-derived net gains. -/
theorem recursorPrefixReturn_eq_sum
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k t : Nat) :
    recursorPrefixReturn benefit stopValue unitCost payload arity k t =
      (∑ i ∈ Finset.range t,
        recursorNetGain benefit unitCost payload arity (k + i)) + stopValue (k + t) := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
      rw [recursorPrefixReturn_succ, ih]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hsum :
          (∑ i ∈ Finset.range t,
              recursorNetGain benefit unitCost payload arity (k + 1 + i)) =
            ∑ i ∈ Finset.range t,
              recursorNetGain benefit unitCost payload arity (k + (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show k + 1 + i = k + (i + 1) by omega]
      rw [hsum]
      rw [show k + 1 + t = k + (t + 1) by omega]
      ring

/-- The Bellman operator for the deterministic recursor model is the maximum
of immediate stopping and the unique continuation return. -/
theorem recursorStoppingModel_bellman_eq_max
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) (V : Nat → ℝ) :
    bellman (recursorStoppingModel benefit stopValue unitCost payload arity) V k =
      max (stopValue k)
        (recursorNetGain benefit unitCost payload arity k + V (k + 1)) := by
  let M := recursorStoppingModel benefit stopValue unitCost payload arity
  apply le_antisymm
  · apply Finset.sup'_le (choices_nonempty M k) (choiceValue M V k)
    intro c hc
    rcases (mem_choices M k c).mp hc with rfl | ⟨a, ha, rfl⟩
    · change stopValue k ≤ _
      exact le_max_left _ _
    · cases a
      change expected M V k () ≤ _
      rw [recursorStoppingModel_expected]
      exact le_max_right _ _
  · apply max_le
    · simpa [M] using stop_le_bellman M V k
    · have h := expected_le_bellman M V
        (s := k) (a := ()) (by simp [M, recursorStoppingModel])
      rw [recursorStoppingModel_expected] at h
      exact h

/-- The stochastic Bellman value is exactly the finite stopping-time maximum
for arbitrary real rewards and every natural cost, payload and arity. -/
theorem recursorStopping_value_eq_finiteHorizonMaximum
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k : Nat) :
    value (recursorStoppingModel benefit stopValue unitCost payload arity) n k =
      recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      change bellman (recursorStoppingModel benefit stopValue unitCost payload arity)
          (value (recursorStoppingModel benefit stopValue unitCost payload arity) n) k =
        max (stopValue k)
          (recursorNetGain benefit unitCost payload arity k +
            recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n (k + 1))
      rw [recursorStoppingModel_bellman_eq_max, ih]

/-- Every stopping-time return with `t ≤ n` is bounded by the recursive
finite-horizon maximum. -/
theorem recursorPrefixReturn_le_finiteHorizonMaximum
    (benefit stopValue : Nat → ℝ) (unitCost payload arity : Nat)
    {n k t : Nat} (ht : t ≤ n) :
    recursorPrefixReturn benefit stopValue unitCost payload arity k t ≤
      recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n k := by
  induction n generalizing k t with
  | zero =>
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst t
      rfl
  | succ n ih =>
      cases t with
      | zero =>
          exact le_max_left _ _
      | succ t =>
          have ht' : t ≤ n := Nat.le_of_succ_le_succ ht
          exact (add_le_add_left (ih (k := k + 1) ht') _).trans (le_max_right _ _)

/-- Some stopping time `t ≤ n` attains the recursive finite-horizon maximum. -/
theorem recursorFiniteHorizonMaximum_attained
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k : Nat) :
    ∃ t, t ≤ n ∧
      recursorPrefixReturn benefit stopValue unitCost payload arity k t =
        recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n k := by
  induction n generalizing k with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
      by_cases hstop :
          recursorNetGain benefit unitCost payload arity k +
              recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n (k + 1) ≤
            stopValue k
      · refine ⟨0, Nat.zero_le _, ?_⟩
        exact (max_eq_left hstop).symm
      · obtain ⟨t, ht, heq⟩ := ih (k + 1)
        refine ⟨t + 1, Nat.succ_le_succ ht, ?_⟩
        rw [recursorPrefixReturn_succ, heq]
        exact (max_eq_right (le_of_not_ge hstop)).symm

/-- The recursive finite-horizon value is the greatest exact stopping-time
return. -/
theorem recursorFiniteHorizonMaximum_isGreatest
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k : Nat) :
    IsGreatest
      {x : ℝ | ∃ t, t ≤ n ∧
        recursorPrefixReturn benefit stopValue unitCost payload arity k t = x}
      (recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n k) := by
  obtain ⟨t, ht, heq⟩ := recursorFiniteHorizonMaximum_attained
    benefit stopValue unitCost payload arity n k
  refine ⟨⟨t, ht, heq⟩, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  exact recursorPrefixReturn_le_finiteHorizonMaximum
    benefit stopValue unitCost payload arity hu

/-- A policy follows the unique positive-probability depth extension exactly
`t` times and then stops. -/
inductive RecursorPolicyStopsAfter
    (benefit stopValue : Nat → ℝ) (unitCost payload arity : Nat) :
    {n k : Nat} →
      Policy (recursorStoppingModel benefit stopValue unitCost payload arity) n k →
      Nat → Prop
  | stop (n k : Nat) :
      RecursorPolicyStopsAfter benefit stopValue unitCost payload arity
        (Policy.stop n k) 0
  | compute {n k t : Nat}
      (ha : () ∈
        (recursorStoppingModel benefit stopValue unitCost payload arity).actions k)
      (next : ∀ s : Nat,
        Policy (recursorStoppingModel benefit stopValue unitCost payload arity) n s)
      (hnext : RecursorPolicyStopsAfter benefit stopValue unitCost payload arity
        (next (k + 1)) t) :
      RecursorPolicyStopsAfter benefit stopValue unitCost payload arity
        (Policy.compute k () ha next) (t + 1)

/-- Every exact stopping-time return is realized by a policy that computes
exactly that many positive-probability depth extensions and then stops. -/
theorem recursorPrefixReturn_realized
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k t : Nat)
    (ht : t ≤ n) :
    ∃ policy : Policy
        (recursorStoppingModel benefit stopValue unitCost payload arity) n k,
      policy.value = recursorPrefixReturn benefit stopValue unitCost payload arity k t ∧
        RecursorPolicyStopsAfter benefit stopValue unitCost payload arity policy t := by
  induction t generalizing n k with
  | zero =>
      exact ⟨Policy.stop n k, rfl,
        RecursorPolicyStopsAfter.stop
          (benefit := benefit) (stopValue := stopValue)
          (unitCost := unitCost) (payload := payload) (arity := arity) n k⟩
  | succ t ih =>
      cases n with
      | zero => omega
      | succ n =>
          have ht' : t ≤ n := Nat.le_of_succ_le_succ ht
          let next : ∀ s : Nat,
              Policy (recursorStoppingModel benefit stopValue unitCost payload arity) n s :=
            fun s => Classical.choose (ih (n := n) (k := s) ht')
          have hnextValue : ∀ s : Nat,
              (next s).value =
                recursorPrefixReturn benefit stopValue unitCost payload arity s t :=
            fun s => (Classical.choose_spec (ih (n := n) (k := s) ht')).1
          have hnextStops : ∀ s : Nat,
              RecursorPolicyStopsAfter benefit stopValue unitCost payload arity
                (next s) t :=
            fun s => (Classical.choose_spec (ih (n := n) (k := s) ht')).2
          have ha : () ∈
              (recursorStoppingModel benefit stopValue unitCost payload arity).actions k := by
            simp [recursorStoppingModel]
          refine ⟨Policy.compute k () ha next, ?_,
            RecursorPolicyStopsAfter.compute
              (benefit := benefit) (stopValue := stopValue)
              (unitCost := unitCost) (payload := payload) (arity := arity)
              ha next (hnextStops (k + 1))⟩
          change expected (recursorStoppingModel benefit stopValue unitCost payload arity)
              (fun s => (next s).value) k () = _
          rw [recursorStoppingModel_expected, hnextValue (k + 1)]
          rfl

/-- Chosen policy realizing exactly `t` depth extensions. -/
noncomputable def recursorStopAfter
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k t : Nat)
    (ht : t ≤ n) :
    Policy (recursorStoppingModel benefit stopValue unitCost payload arity) n k :=
  Classical.choose
    (recursorPrefixReturn_realized benefit stopValue unitCost payload arity n k t ht)

theorem recursorStopAfter_value
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k t : Nat)
    (ht : t ≤ n) :
    (recursorStopAfter benefit stopValue unitCost payload arity n k t ht).value =
      recursorPrefixReturn benefit stopValue unitCost payload arity k t :=
  (Classical.choose_spec
    (recursorPrefixReturn_realized benefit stopValue unitCost payload arity n k t ht)).1

theorem recursorStopAfter_stopsAfter
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k t : Nat)
    (ht : t ≤ n) :
    RecursorPolicyStopsAfter benefit stopValue unitCost payload arity
      (recursorStopAfter benefit stopValue unitCost payload arity n k t ht) t :=
  (Classical.choose_spec
    (recursorPrefixReturn_realized benefit stopValue unitCost payload arity n k t ht)).2

/-- An exact stopping time and a policy following it attain the Bellman value. -/
theorem recursorOptimalStoppingTime_and_policy_exists
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k : Nat) :
    ∃ t, t ≤ n ∧
      ∃ policy : Policy
        (recursorStoppingModel benefit stopValue unitCost payload arity) n k,
        policy.value =
            value (recursorStoppingModel benefit stopValue unitCost payload arity) n k ∧
          RecursorPolicyStopsAfter benefit stopValue unitCost payload arity policy t := by
  obtain ⟨t, ht, heq⟩ := recursorFiniteHorizonMaximum_attained
    benefit stopValue unitCost payload arity n k
  refine ⟨t, ht,
    recursorStopAfter benefit stopValue unitCost payload arity n k t ht, ?_,
      recursorStopAfter_stopsAfter benefit stopValue unitCost payload arity n k t ht⟩
  rw [recursorStopAfter_value, heq]
  exact (recursorStopping_value_eq_finiteHorizonMaximum
    benefit stopValue unitCost payload arity n k).symm

/-- Exact finite-horizon stopping criterion for arbitrary real rewards and all
natural cost regimes. -/
theorem recursorStopping_value_eq_stop_iff_all_prefixReturns_le
    (benefit stopValue : Nat → ℝ) (unitCost payload arity n k : Nat) :
    value (recursorStoppingModel benefit stopValue unitCost payload arity) n k =
        stopValue k ↔
      ∀ t, t ≤ n →
        recursorPrefixReturn benefit stopValue unitCost payload arity k t ≤ stopValue k := by
  constructor
  · intro hvalue t ht
    calc
      recursorPrefixReturn benefit stopValue unitCost payload arity k t ≤
          recursorFiniteHorizonMaximum benefit stopValue unitCost payload arity n k :=
        recursorPrefixReturn_le_finiteHorizonMaximum
          benefit stopValue unitCost payload arity ht
      _ = value (recursorStoppingModel benefit stopValue unitCost payload arity) n k :=
        (recursorStopping_value_eq_finiteHorizonMaximum
          benefit stopValue unitCost payload arity n k).symm
      _ = stopValue k := hvalue
  · intro hprefix
    apply le_antisymm
    · rw [recursorStopping_value_eq_finiteHorizonMaximum]
      obtain ⟨t, ht, heq⟩ := recursorFiniteHorizonMaximum_attained
        benefit stopValue unitCost payload arity n k
      rw [← heq]
      exact hprefix t ht
    · simpa [recursorStoppingModel] using
        stop_le_value
          (recursorStoppingModel benefit stopValue unitCost payload arity) n k

/-- Immediate stopping is optimal at every finite horizon exactly when every
finite prefix return is bounded by the current stopping value. -/
theorem recursorStopping_all_horizons_eq_stop_iff_all_prefixReturns_le
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    (∀ n,
      value (recursorStoppingModel benefit stopValue unitCost payload arity) n k =
        stopValue k) ↔
      ∀ t,
        recursorPrefixReturn benefit stopValue unitCost payload arity k t ≤ stopValue k := by
  constructor
  · intro hall t
    exact (recursorStopping_value_eq_stop_iff_all_prefixReturns_le
      benefit stopValue unitCost payload arity t k).1 (hall t) t (Nat.le_refl t)
  · intro hprefix n
    exact (recursorStopping_value_eq_stop_iff_all_prefixReturns_le
      benefit stopValue unitCost payload arity n k).2 (fun t _ => hprefix t)

/-- Every positive-probability transition charges the payload count of the
new live stage in the extended actual recursor execution. -/
theorem positive_transition_cost_eq_actual_live_stage
    (ia ib : Nat) (benefit stopValue : Nat → ℝ)
    (unitCost payload arity k t : Nat) (a : Unit)
    (ht : 0 <
      (recursorStoppingModel benefit stopValue unitCost payload arity).probability k a t) :
    t = k + 1 ∧
      raryMarginalCost k unitCost payload arity =
        unitCost *
          (countPayR (rOrbit (.base ia) (.pay ib) (k + 1) arity (k + 1)) * payload) := by
  exact ⟨(recursorStoppingModel_positive_probability_iff_depthExtension
    benefit stopValue unitCost payload arity k t a).mp ht,
    raryMarginalCost_eq_live_next ia ib k unitCost payload arity⟩

/-- Exact one-step Bellman classifier for arbitrary real rewards and stopping
values. Immediate stopping is optimal exactly when the next-depth return does
not exceed the current stop value after paying the actual marginal cost. -/
theorem oneStep_stop_iff
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    value (recursorStoppingModel benefit stopValue unitCost payload arity) 1 k =
        (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k ↔
      benefit k + stopValue (k + 1) ≤
        (raryMarginalCost k unitCost payload arity : ℝ) + stopValue k := by
  let M := recursorStoppingModel benefit stopValue unitCost payload arity
  change bellman M M.stopValue k = M.stopValue k ↔ _
  rw [bellman_eq_stop_iff]
  constructor
  · intro h
    have hunit := h () (by simp [M, recursorStoppingModel])
    rw [recursorStoppingModel_expected] at hunit
    simp only [M, recursorStoppingModel_stopValue] at hunit
    linarith
  · intro h a ha
    cases a
    rw [recursorStoppingModel_expected]
    simp only [M, recursorStoppingModel_stopValue]
    linarith

/-- Exact one-step continuation classifier. -/
theorem oneStep_continues_iff
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k <
        value (recursorStoppingModel benefit stopValue unitCost payload arity) 1 k ↔
      (raryMarginalCost k unitCost payload arity : ℝ) + stopValue k <
        benefit k + stopValue (k + 1) := by
  let M := recursorStoppingModel benefit stopValue unitCost payload arity
  constructor
  · intro hcontinue
    by_contra hnot
    have hstop : value M 1 k = M.stopValue k :=
      (oneStep_stop_iff benefit stopValue unitCost payload arity k).2
        (le_of_not_gt hnot)
    rw [hstop] at hcontinue
    exact lt_irrefl _ hcontinue
  · intro hgain
    have hne : value M 1 k ≠ M.stopValue k := by
      intro hstop
      have hle := (oneStep_stop_iff benefit stopValue unitCost payload arity k).1 hstop
      exact (not_le_of_gt hgain) hle
    exact lt_of_le_of_ne (stop_le_value M 1 k) (Ne.symm hne)

/-- The compute action ties immediate stopping exactly when reward plus next
stop value equals marginal cost plus current stop value. -/
theorem oneStep_compute_ties_stop_iff
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat) :
    expected (recursorStoppingModel benefit stopValue unitCost payload arity)
        (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k () =
        (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k ↔
      benefit k + stopValue (k + 1) =
        (raryMarginalCost k unitCost payload arity : ℝ) + stopValue k := by
  rw [recursorStoppingModel_expected]
  simp only [recursorStoppingModel_stopValue]
  constructor <;> intro h <;> linarith

/-- Depths at or above the exact cutoff form an invariant set. -/
def AfterCutoff (benefitBound unitCost payload arity k : Nat) : Prop :=
  raryMarginalCutoff benefitBound (unitCost * payload) arity ≤ k

/-- Membership in the stopping region is exactly the marginal-price inequality. -/
theorem afterCutoff_iff_marginalCost
    (benefitBound unitCost payload arity k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity) :
    AfterCutoff benefitBound unitCost payload arity k ↔
      benefitBound ≤ raryMarginalCost k unitCost payload arity := by
  simpa [AfterCutoff, raryMarginalCost, raryMarginalCopies, Nat.mul_assoc] using
    raryMarginalCutoff_le_iff benefitBound (unitCost * payload) arity
      (Nat.mul_pos hunit hpayload) harity k

/-- The strict cutoff is exactly the region where marginal price strictly
exceeds the benefit bound. -/
theorem strictCutoff_le_iff_marginalCost_gt
    (benefitBound unitCost payload arity k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity) :
    raryStrictMarginalCutoff benefitBound (unitCost * payload) arity ≤ k ↔
      benefitBound < raryMarginalCost k unitCost payload arity := by
  simpa [raryMarginalCost, raryMarginalCopies, Nat.mul_assoc] using
    raryStrictMarginalCutoff_le_iff benefitBound (unitCost * payload) arity
      (Nat.mul_pos hunit hpayload) harity k

theorem afterCutoff_closed
    (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity : Nat) :
    ∀ s a t,
      AfterCutoff benefitBound unitCost payload arity s →
      a ∈ (recursorStoppingModel benefit stopValue unitCost payload arity).actions s →
      t ∈ (recursorStoppingModel benefit stopValue unitCost payload arity).support s a →
      0 < (recursorStoppingModel benefit stopValue unitCost payload arity).probability s a t →
      AfterCutoff benefitBound unitCost payload arity t := by
  intro s a t hs ha ht hp
  have ht' : t = s + 1 := by
    simpa [recursorStoppingModel] using ht
  subst t
  exact hs.trans (Nat.le_succ s)

/-- The reward plus the next stopping value is bounded by the current stopping
value throughout the cutoff region. -/
theorem expected_stopValue_le_afterCutoff
    (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity)
    (hbenefit : ∀ k,
      AfterCutoff benefitBound unitCost payload arity k →
        benefit k + stopValue (k + 1) ≤ (benefitBound : ℝ) + stopValue k) :
    ∀ s,
      AfterCutoff benefitBound unitCost payload arity s →
      ∀ a ∈ (recursorStoppingModel benefit stopValue unitCost payload arity).actions s,
        expected (recursorStoppingModel benefit stopValue unitCost payload arity)
            (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue s a ≤
          (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue s := by
  intro s hs a ha
  have hcost : 0 < unitCost * payload := Nat.mul_pos hunit hpayload
  have hprice : benefitBound ≤ raryMarginalCost s unitCost payload arity := by
    exact (raryMarginalCutoff_le_iff benefitBound (unitCost * payload) arity
      hcost harity s).1 hs
  have hbenefitR :
      benefit s + stopValue (s + 1) ≤
        (benefitBound : ℝ) + stopValue s :=
    hbenefit s hs
  have hpriceR : (benefitBound : ℝ) ≤
      (raryMarginalCost s unitCost payload arity : ℝ) := by
    exact_mod_cast hprice
  rw [recursorStoppingModel_expected]
  simp only [recursorStoppingModel_stopValue]
  linarith

/-- At and beyond the cutoff, immediate stopping is the Bellman value at every
finite horizon. -/
theorem value_eq_stop_afterCutoff
    (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity)
    (hbenefit : ∀ k,
      AfterCutoff benefitBound unitCost payload arity k →
        benefit k + stopValue (k + 1) ≤ (benefitBound : ℝ) + stopValue k)
    (n k : Nat) (hk : AfterCutoff benefitBound unitCost payload arity k) :
    value (recursorStoppingModel benefit stopValue unitCost payload arity) n k =
      stopValue k := by
  exact value_eq_stop_on_invariant
    (recursorStoppingModel benefit stopValue unitCost payload arity)
    (AfterCutoff benefitBound unitCost payload arity)
    (afterCutoff_closed benefit stopValue benefitBound unitCost payload arity)
    (expected_stopValue_le_afterCutoff benefit stopValue benefitBound unitCost payload arity
      hunit hpayload harity hbenefit) n k hk

/-- Every adaptive policy is bounded by immediate stopping after the cutoff. -/
theorem adaptivePolicy_le_stop_afterCutoff
    (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity)
    (hbenefit : ∀ k,
      AfterCutoff benefitBound unitCost payload arity k →
        benefit k + stopValue (k + 1) ≤ (benefitBound : ℝ) + stopValue k)
    {n k : Nat} (hk : AfterCutoff benefitBound unitCost payload arity k)
    (policy : Policy
      (recursorStoppingModel benefit stopValue unitCost payload arity) n k) :
    policy.value ≤ stopValue k := by
  calc
    policy.value ≤ value
        (recursorStoppingModel benefit stopValue unitCost payload arity) n k :=
      policy.le_value
    _ = stopValue k := value_eq_stop_afterCutoff benefit stopValue benefitBound
      unitCost payload arity hunit hpayload harity hbenefit n k hk

/-- An adaptive policy attains the stopping value at every finite horizon after
the cutoff. -/
theorem adaptivePolicy_attains_stop_afterCutoff
    (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity)
    (hbenefit : ∀ k,
      AfterCutoff benefitBound unitCost payload arity k →
        benefit k + stopValue (k + 1) ≤ (benefitBound : ℝ) + stopValue k)
    (n k : Nat) (hk : AfterCutoff benefitBound unitCost payload arity k) :
    ∃ policy : Policy
        (recursorStoppingModel benefit stopValue unitCost payload arity) n k,
      policy.value = value
          (recursorStoppingModel benefit stopValue unitCost payload arity) n k ∧
        policy.value = stopValue k := by
  let policy : Policy
      (recursorStoppingModel benefit stopValue unitCost payload arity) n k :=
    Policy.stop n k
  refine ⟨policy, ?_, ?_⟩
  · simpa [policy] using
      (value_eq_stop_afterCutoff benefit stopValue benefitBound unitCost payload arity
        hunit hpayload harity hbenefit n k hk).symm
  · change stopValue k = stopValue k
    rfl

/-! ## Sharpness and controls -/

/-- Below the cutoff, constant benefit makes one-step continuation strictly
better than immediate stopping. -/
theorem constantBenefit_value_one_pos_belowCutoff
    (benefitBound unitCost payload arity k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity)
    (hk : k < raryMarginalCutoff benefitBound (unitCost * payload) arity) :
    0 < value
      (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        unitCost payload arity) 1 k := by
  let M := recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
    unitCost payload arity
  have hcost : 0 < unitCost * payload := Nat.mul_pos hunit hpayload
  have hprice : raryMarginalCost k unitCost payload arity < benefitBound := by
    exact raryMarginalCost_lt_of_lt_cutoff benefitBound (unitCost * payload) arity
      hcost harity hk
  have hpriceR : (raryMarginalCost k unitCost payload arity : ℝ) <
      (benefitBound : ℝ) := by exact_mod_cast hprice
  have hexpected : 0 < expected M M.stopValue k () := by
    rw [recursorStoppingModel_expected]
    simp only [M, recursorStoppingModel_stopValue]
    linarith
  have hle : expected M M.stopValue k () ≤ bellman M M.stopValue k :=
    expected_le_bellman M M.stopValue (by simp [M, recursorStoppingModel])
  simpa only [M, value] using hexpected.trans_le hle

/-- For constant bounded benefit and zero stop reward, the computed cutoff is
exactly the region where every finite horizon stops. -/
theorem constantBenefit_all_horizons_stop_iff
    (benefitBound unitCost payload arity k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) (harity : 0 < arity) :
    (∀ n,
      value (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        unitCost payload arity) n k = 0) ↔
      AfterCutoff benefitBound unitCost payload arity k := by
  constructor
  · intro hall
    by_contra hk
    have hlt : k < raryMarginalCutoff benefitBound (unitCost * payload) arity :=
      Nat.lt_of_not_ge hk
    have hpos := constantBenefit_value_one_pos_belowCutoff benefitBound unitCost
      payload arity k hunit hpayload harity hlt
    rw [hall 1] at hpos
    exact lt_irrefl 0 hpos
  · intro hk n
    exact value_eq_stop_afterCutoff (fun _ => (benefitBound : ℝ)) (fun _ => 0)
      benefitBound unitCost payload arity hunit hpayload harity
      (by intro j hj; simp) n k hk

/-- A zero unit price gives zero cumulative and marginal cost. -/
theorem zero_unitCost_control (k payload arity : Nat) :
    raryCumulativeCost k 0 payload arity = 0 ∧
      raryMarginalCost k 0 payload arity = 0 := by
  simp [raryCumulativeCost, raryMarginalCost]

/-- A zero payload gives zero cumulative and marginal cost. -/
theorem zero_payload_control (k unitCost arity : Nat) :
    raryCumulativeCost k unitCost 0 arity = 0 ∧
      raryMarginalCost k unitCost 0 arity = 0 := by
  simp [raryCumulativeCost, raryMarginalCost, conMassR]

/-- Positive benefit with zero marginal price makes a one-step continuation
strictly better than stopping. -/
theorem positiveBenefit_zeroPrice_continues
    (benefit stopValue : Nat → ℝ) (unitCost payload arity k : Nat)
    (hbenefit : stopValue k < benefit k + stopValue (k + 1))
    (hprice : raryMarginalCost k unitCost payload arity = 0) :
    (recursorStoppingModel benefit stopValue unitCost payload arity).stopValue k <
      value (recursorStoppingModel benefit stopValue unitCost payload arity) 1 k := by
  apply (oneStep_continues_iff benefit stopValue unitCost payload arity k).2
  simpa [hprice] using hbenefit

/-- Positive constant benefit continues at one step when unit price is zero. -/
theorem zero_unitCost_positiveBenefit_continues
    (benefitBound payload arity k : Nat) (hbenefit : 0 < benefitBound) :
    0 < value
      (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        0 payload arity) 1 k := by
  have hgain : (0 : ℝ) < (benefitBound : ℝ) := by exact_mod_cast hbenefit
  simpa using positiveBenefit_zeroPrice_continues
    (fun _ => (benefitBound : ℝ)) (fun _ => 0) 0 payload arity k (by simpa using hgain)
      (zero_unitCost_control k payload arity).2

/-- Positive constant benefit continues at one step when payload size is zero. -/
theorem zero_payload_positiveBenefit_continues
    (benefitBound unitCost arity k : Nat) (hbenefit : 0 < benefitBound) :
    0 < value
      (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        unitCost 0 arity) 1 k := by
  have hgain : (0 : ℝ) < (benefitBound : ℝ) := by exact_mod_cast hbenefit
  simpa using positiveBenefit_zeroPrice_continues
    (fun _ => (benefitBound : ℝ)) (fun _ => 0) unitCost 0 arity k (by simpa using hgain)
      (zero_payload_control k unitCost arity).2

/-- At arity zero the marginal price is constant; duplication is the premise
that makes the cutoff finite for every benefit bound. -/
theorem zero_arity_marginalCost (k unitCost payload : Nat) :
    raryMarginalCost k unitCost payload 0 = unitCost * payload := by
  simp [raryMarginalCost, raryMarginalCopies]

/-- At arity zero, constant-benefit stopping has a complete all-horizon
classification: every horizon stops exactly when the constant marginal price
meets the benefit. -/
theorem zero_arity_constantBenefit_all_horizons_stop_iff
    (benefitBound unitCost payload k : Nat) :
    (∀ n,
      value (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        unitCost payload 0) n k = 0) ↔
      benefitBound ≤ unitCost * payload := by
  let M := recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
    unitCost payload 0
  constructor
  · intro hall
    have hstop : value M 1 k = M.stopValue k := by
      simpa [M] using hall 1
    have hineq := (oneStep_stop_iff (fun _ => (benefitBound : ℝ)) (fun _ => 0)
      unitCost payload 0 k).1 hstop
    have hineq' : (benefitBound : ℝ) ≤ ((unitCost * payload : Nat) : ℝ) := by
      simpa [zero_arity_marginalCost] using hineq
    exact_mod_cast hineq'
  · intro hprice n
    have hpriceR : (benefitBound : ℝ) ≤ ((unitCost * payload : Nat) : ℝ) := by
      exact_mod_cast hprice
    have hall : ∀ n s, value M n s = M.stopValue s :=
      (value_eq_stop_iff M).2 (by
        intro s a ha
        cases a
        rw [recursorStoppingModel_expected]
        simp only [M, recursorStoppingModel_stopValue]
        rw [zero_arity_marginalCost]
        linarith)
    simpa [M] using hall n k

/-- Zero current benefit does not force stopping: growth of the next stopping
reward can exceed the genuine binary marginal price. -/
theorem zero_current_benefit_future_reward_continues :
    (recursorStoppingModel (fun _ => (0 : ℝ)) (fun k => 3 * (k : ℝ)) 1 1 1).stopValue 0 <
      value (recursorStoppingModel (fun _ => (0 : ℝ))
        (fun k => 3 * (k : ℝ)) 1 1 1) 1 0 := by
  apply (oneStep_continues_iff (fun _ => (0 : ℝ)) (fun k => 3 * (k : ℝ))
    1 1 1 0).2
  norm_num [raryMarginalCost, raryMarginalCopies]

/-- The preceding control has zero current benefit and positive marginal price;
its continuation advantage comes only from the next stopping reward. -/
theorem zero_current_benefit_future_reward_control_values :
    (fun _ : Nat => (0 : ℝ)) 0 = 0 ∧
      raryMarginalCost 0 1 1 1 = 2 ∧
      (fun k : Nat => 3 * (k : ℝ)) 0 = 0 ∧
      (fun k : Nat => 3 * (k : ℝ)) 1 = 3 := by
  norm_num [raryMarginalCost, raryMarginalCopies]

/-- Binary corollary: the least stopping depth is
`ceil(V/(unitCost*payload))-2`, truncated in `Nat`. -/
theorem binary_constantBenefit_all_horizons_stop_iff
    (benefitBound unitCost payload k : Nat)
    (hunit : 0 < unitCost) (hpayload : 0 < payload) :
    (∀ n,
      value (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
        unitCost payload 1) n k = 0) ↔
      binaryMarginalCutoff benefitBound (unitCost * payload) ≤ k := by
  rw [← raryMarginalCutoff_one benefitBound (unitCost * payload)]
  exact constantBenefit_all_horizons_stop_iff benefitBound unitCost payload 1 k
    hunit hpayload (by decide)

/-- Core execution-cost and exact-cutoff package. -/
theorem recursor_stopping_complete :
    (∀ ia ib k payload,
      binaryCumulativeCost k payload =
        ∑ i ∈ Finset.range (k + 1),
          countPayR (rOrbit (.base ia) (.pay ib) k 1 i) * payload) ∧
      (∀ k payload,
        binaryCumulativeCost (k + 1) payload =
          binaryCumulativeCost k payload + (k + 2) * payload) ∧
      (∀ benefitBound unitCost payload arity k : Nat,
        0 < unitCost → 0 < payload → 0 < arity →
          ((∀ n,
            value (recursorStoppingModel (fun _ => (benefitBound : ℝ)) (fun _ => 0)
              unitCost payload arity) n k = 0) ↔
            AfterCutoff benefitBound unitCost payload arity k)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact binaryCumulativeCost_eq_live_sum
  · exact binaryCumulativeCost_succ
  · intro benefitBound unitCost payload arity k hunit hpayload harity
    exact constantBenefit_all_horizons_stop_iff benefitBound unitCost payload arity k
      hunit hpayload harity

/-- Universal C6 policy crown. For arbitrary real reward and stopping-value
functions satisfying the execution-derived regional inequality, immediate
stopping is the Bellman value at every finite horizon, bounds every adaptive
policy, and is itself an attaining policy. -/
theorem recursor_stopping_policy_crown :
    ∀ (benefit stopValue : Nat → ℝ) (benefitBound unitCost payload arity n k : Nat),
      0 < unitCost → 0 < payload → 0 < arity →
      (∀ j,
        AfterCutoff benefitBound unitCost payload arity j →
          benefit j + stopValue (j + 1) ≤ (benefitBound : ℝ) + stopValue j) →
      AfterCutoff benefitBound unitCost payload arity k →
      value (recursorStoppingModel benefit stopValue unitCost payload arity) n k =
          stopValue k ∧
        (∀ policy : Policy
            (recursorStoppingModel benefit stopValue unitCost payload arity) n k,
          policy.value ≤ stopValue k) ∧
        ∃ policy : Policy
            (recursorStoppingModel benefit stopValue unitCost payload arity) n k,
          policy.value =
              value (recursorStoppingModel benefit stopValue unitCost payload arity) n k ∧
            policy.value = stopValue k := by
  intro benefit stopValue benefitBound unitCost payload arity n k
    hunit hpayload harity hbenefit hk
  refine ⟨value_eq_stop_afterCutoff benefit stopValue benefitBound unitCost payload arity
      hunit hpayload harity hbenefit n k hk, ?_, ?_⟩
  · intro policy
    exact adaptivePolicy_le_stop_afterCutoff benefit stopValue benefitBound unitCost payload
      arity hunit hpayload harity hbenefit hk policy
  · exact adaptivePolicy_attains_stop_afterCutoff benefit stopValue benefitBound unitCost
      payload arity hunit hpayload harity hbenefit n k hk

end OperatorKO7.Meta.Decision.RecursorStopping
