import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.AblationComparisons
import Mathlib.Tactic

/-!
# Coupling corollary and expected-negative controls

`retained_wrapper_forces_payload_coupled_gain` in `CouplingTheorem.lean` assumes that the
wrapper keeps both of its arguments at cost `c_w`, meaning `c_w + M x + M y ≤ M (wrap x y)`.
This module adds the cell form of its corollary and one control for each half of the
retention premise.

* A retentive orienter whose payload values are unbounded lies in the unbounded-wrapper,
  unbounded-gain cell of `CellClassification.lean` at every pair `(b, n)`.
* The counter projection `counterRank` drops the payload argument of the wrapper. It has
  wrapper cost zero and counter gain one at every instance.
* `recursiveDropMeasure` satisfies the affine constructor equations with wrapper
  coefficients `(1, 0)`, so it drops the recursive result. It has counter gain one at every
  instance.

Both controls orient every successor instance of the free schema, fail retention at every
cost, and violate `M s + c_w < gain`.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CouplingControls

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.AblationComparisons

universe u

/-! ## Cell form of the coupling corollary -/

/-- A wrapper-retentive orienter with unbounded payload values lies in the
unbounded-wrapper, unbounded-gain cell at every pair `(b, n)`. -/
theorem retentive_orienter_unbounded_unbounded
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema} (M : S.T → Nat) (c_w : Nat)
    (hretain : ∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y))
    (horient : ∀ b s n : S.T,
      M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)))
    (hunbounded : ∀ K : Nat, ∃ s : S.T, K ≤ M s) (b n : S.T) :
    CellClassification.WrapUnboundedAt M b n ∧ CellClassification.GainUnboundedAt M b n := by
  constructor
  · intro K
    obtain ⟨s, hs⟩ := hunbounded (K + 1)
    refine ⟨s, ?_⟩
    have hr := hretain s (S.recur b s n)
    omega
  · intro K
    obtain ⟨s, hs⟩ := hunbounded K
    refine ⟨s, ?_⟩
    have hr := hretain s (S.recur b s n)
    have ho := horient b s n
    omega

/-! ## Counter projection: the payload argument is dropped -/

/-- The counter projection has wrapper cost zero at every instance. -/
theorem counterRank_wrapperCost_eq_zero (b s n : FreeTerm Empty) :
    wrapperCostZ (S := freeSchema Empty) counterRank b s n = 0 := by
  show ((counterRank (FreeTerm.wrap s (FreeTerm.recur b s n)) : Nat) : Int) -
      ((counterRank (FreeTerm.recur b s n) : Nat) : Int) = 0
  simp only [counterRank]
  omega

/-- The counter projection has counter gain one at every instance. -/
theorem counterRank_counterGain_eq_one (b s n : FreeTerm Empty) :
    counterGainZ (S := freeSchema Empty) counterRank b s n = 1 := by
  show ((counterRank (FreeTerm.recur b s (FreeTerm.succ n)) : Nat) : Int) -
      ((counterRank (FreeTerm.recur b s n) : Nat) : Int) = 1
  simp only [counterRank]
  omega

/-- The counter projection is not retentive at any cost: retention fails at
`x = succ zero`, `y = zero`. -/
theorem counterRank_not_retentive (c_w : Nat) :
    ¬ ∀ x y : (freeSchema Empty).T,
      c_w + counterRank x + counterRank y ≤ counterRank ((freeSchema Empty).wrap x y) := by
  intro h
  have h1 := h (FreeTerm.succ FreeTerm.zero) FreeTerm.zero
  have e1 : counterRank ((freeSchema Empty).wrap (FreeTerm.succ FreeTerm.zero)
      (FreeTerm.zero : FreeTerm Empty)) = 0 := rfl
  have e2 : counterRank (FreeTerm.succ (FreeTerm.zero : FreeTerm Empty)) = 1 := rfl
  omega

/-- Control for the coupling clause: the counter projection orients every successor
instance, is not retentive at any cost, and violates `M s + c_w < gain` at
`s = succ zero`. -/
theorem counterRank_nonretentive_control (c_w : Nat) :
    (∀ b s n : (freeSchema Empty).T,
        counterRank ((freeSchema Empty).wrap s ((freeSchema Empty).recur b s n)) <
          counterRank ((freeSchema Empty).recur b s ((freeSchema Empty).succ n))) ∧
      (¬ ∀ x y : (freeSchema Empty).T,
        c_w + counterRank x + counterRank y ≤ counterRank ((freeSchema Empty).wrap x y)) ∧
      ¬ ∀ b s n : (freeSchema Empty).T,
        (counterRank s : Int) + (c_w : Int) <
          counterGainZ (S := freeSchema Empty) counterRank b s n := by
  refine ⟨fun b s n => counterRank_orients_original_successor b s n,
    counterRank_not_retentive c_w, ?_⟩
  intro h
  have h1 := h FreeTerm.zero (FreeTerm.succ FreeTerm.zero) FreeTerm.zero
  rw [counterRank_counterGain_eq_one] at h1
  have e1 : counterRank (FreeTerm.succ (FreeTerm.zero : FreeTerm Empty)) = 1 := rfl
  omega

/-! ## Affine member with zero recursive-result coefficient -/

/-- Affine constructor interpretation with successor `n + 1`, wrapper `x + 1` and recursor
`s + n + 1`. The wrapper coefficient of the recursive result is zero. -/
def recursiveDropMeasure {ν : Type u} : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 0
  | .succ t => recursiveDropMeasure t + 1
  | .wrap x _ => recursiveDropMeasure x + 1
  | .recur _ s n => recursiveDropMeasure s + recursiveDropMeasure n + 1

/-- The constructor equations of `recursiveDropMeasure` in the affine form of
`StepDuplicatingSchema.AffineMeasure`: base `0`, successor `(1, 1)`, wrapper `(1, 1, 0)`,
recursor `(1, 0, 1, 1)`. Only the positivity field `h_wrap_right_pos` fails. -/
theorem recursiveDropMeasure_affine_laws {ν : Type u} :
    recursiveDropMeasure (FreeTerm.zero : FreeTerm ν) = 0 ∧
      (∀ t : FreeTerm ν,
        recursiveDropMeasure (FreeTerm.succ t) = 1 + 1 * recursiveDropMeasure t) ∧
      (∀ x y : FreeTerm ν, recursiveDropMeasure (FreeTerm.wrap x y) =
        1 + 1 * recursiveDropMeasure x + 0 * recursiveDropMeasure y) ∧
      ∀ b s n : FreeTerm ν, recursiveDropMeasure (FreeTerm.recur b s n) =
        1 + 0 * recursiveDropMeasure b + 1 * recursiveDropMeasure s +
          1 * recursiveDropMeasure n := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t
    simp only [recursiveDropMeasure]
    omega
  · intro x y
    simp only [recursiveDropMeasure]
    omega
  · intro b s n
    simp only [recursiveDropMeasure]
    omega

/-- Wrapper cost of `recursiveDropMeasure` is minus the counter value. -/
theorem recursiveDrop_wrapperCost_eq (b s n : FreeTerm Empty) :
    wrapperCostZ (S := freeSchema Empty) recursiveDropMeasure b s n =
      -((recursiveDropMeasure n : Nat) : Int) := by
  show ((recursiveDropMeasure (FreeTerm.wrap s (FreeTerm.recur b s n)) : Nat) : Int) -
      ((recursiveDropMeasure (FreeTerm.recur b s n) : Nat) : Int) =
        -((recursiveDropMeasure n : Nat) : Int)
  simp only [recursiveDropMeasure]
  omega

/-- Counter gain of `recursiveDropMeasure` is one at every instance. -/
theorem recursiveDrop_counterGain_eq_one (b s n : FreeTerm Empty) :
    counterGainZ (S := freeSchema Empty) recursiveDropMeasure b s n = 1 := by
  show ((recursiveDropMeasure (FreeTerm.recur b s (FreeTerm.succ n)) : Nat) : Int) -
      ((recursiveDropMeasure (FreeTerm.recur b s n) : Nat) : Int) = 1
  simp only [recursiveDropMeasure]
  omega

/-- `recursiveDropMeasure` orients every successor instance of the free schema. -/
theorem recursiveDrop_orients (b s n : FreeTerm Empty) :
    recursiveDropMeasure (FreeTerm.wrap s (FreeTerm.recur b s n)) <
      recursiveDropMeasure (FreeTerm.recur b s (FreeTerm.succ n)) := by
  simp only [recursiveDropMeasure]
  omega

/-- `recursiveDropMeasure` is not retentive at any cost: retention fails at `x = zero`,
`y = succ (succ zero)`. -/
theorem recursiveDrop_not_retentive (c_w : Nat) :
    ¬ ∀ x y : (freeSchema Empty).T,
      c_w + recursiveDropMeasure x + recursiveDropMeasure y ≤
        recursiveDropMeasure ((freeSchema Empty).wrap x y) := by
  intro h
  have h1 := h FreeTerm.zero (FreeTerm.succ (FreeTerm.succ FreeTerm.zero))
  have e1 : recursiveDropMeasure ((freeSchema Empty).wrap (FreeTerm.zero : FreeTerm Empty)
      (FreeTerm.succ (FreeTerm.succ FreeTerm.zero))) = 1 := rfl
  have e2 : recursiveDropMeasure
      (FreeTerm.succ (FreeTerm.succ (FreeTerm.zero : FreeTerm Empty))) = 2 := rfl
  omega

/-- Control for the retention constant: the affine member with zero recursive-result
coefficient orients every successor instance, is not retentive at any cost, and violates
`M s + c_w < gain` at `s = succ zero`. -/
theorem recursiveDrop_nonretentive_control (c_w : Nat) :
    (∀ b s n : (freeSchema Empty).T,
        recursiveDropMeasure ((freeSchema Empty).wrap s ((freeSchema Empty).recur b s n)) <
          recursiveDropMeasure ((freeSchema Empty).recur b s ((freeSchema Empty).succ n))) ∧
      (¬ ∀ x y : (freeSchema Empty).T,
        c_w + recursiveDropMeasure x + recursiveDropMeasure y ≤
          recursiveDropMeasure ((freeSchema Empty).wrap x y)) ∧
      ¬ ∀ b s n : (freeSchema Empty).T,
        (recursiveDropMeasure s : Int) + (c_w : Int) <
          counterGainZ (S := freeSchema Empty) recursiveDropMeasure b s n := by
  refine ⟨fun b s n => recursiveDrop_orients b s n, recursiveDrop_not_retentive c_w, ?_⟩
  intro h
  have h1 := h FreeTerm.zero (FreeTerm.succ FreeTerm.zero) FreeTerm.zero
  rw [recursiveDrop_counterGain_eq_one] at h1
  have e1 : recursiveDropMeasure (FreeTerm.succ (FreeTerm.zero : FreeTerm Empty)) = 1 := rfl
  omega

end OperatorKO7.Methods.OrientationClosure.CouplingControls
