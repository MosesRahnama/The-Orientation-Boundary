import Mathlib.Tactic

/-!
# Increment and wrapper-cost theorems

Arithmetic statements used by the Orientation Boundary independently of any
particular term datatype.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.IncrementCost

universe u

/-- Iteration with the newest application on the outside. -/
def iterate {α : Type u} (U : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => U (iterate U k x)

@[simp] theorem iterate_zero {α : Type u} (U : α → α) (x : α) :
    iterate U 0 x = x := rfl

@[simp] theorem iterate_succ {α : Type u} (U : α → α) (k : Nat) (x : α) :
    iterate U (k + 1) x = U (iterate U k x) := rfl

/-- Additive wrapper orientation is the comparison between wrapper cost and the
recursor increment. -/
theorem nat_wrapper_orientation_iff
    (W : Nat → Nat → Nat) (R : Nat → Nat → Nat → Nat)
    (U : Nat → Nat) (C : Nat → Nat)
    (hwrap : ∀ s y, W s y = y + C s)
    (b s n : Nat) :
    W s (R b s n) < R b s (U n) ↔
      R b s n + C s < R b s (U n) := by
  rw [hwrap]

/-- Over an ordered additive group, the same comparison is a strict bound on
wrapper cost by the recursor increment. -/
theorem ordered_wrapper_orientation_iff
    {α : Type u} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (W : α → α → α) (R : α → α → α → α)
    (U : α → α) (C : α → α)
    (hwrap : ∀ s y, W s y = y + C s)
    (b s n : α) :
    W s (R b s n) < R b s (U n) ↔
      C s < R b s (U n) - R b s n := by
  rw [hwrap]
  constructor
  · intro h
    exact (lt_sub_iff_add_lt).2 (by simpa [add_comm] using h)
  · intro h
    have h' := (lt_sub_iff_add_lt).1 h
    simpa [add_comm] using h'

/-- A payload value is available to the arithmetic comparison. -/
def Attained (P : Nat → Prop) (s : Nat) : Prop := P s

/-- A payload-independent upper bound on the recursor increment conflicts with
unbounded attained wrapper costs. -/
theorem no_uniform_orientation_of_bounded_increment_unbounded_cost
    (R : Nat → Nat → Nat → Nat) (U : Nat → Nat) (C : Nat → Nat)
    (P : Nat → Prop) (b₀ n₀ K : Nat)
    (hbound : ∀ s, P s → R b₀ s (U n₀) ≤ R b₀ s n₀ + K)
    (hunbounded : ∀ M, ∃ s, P s ∧ M ≤ C s) :
    ¬ (∀ s, P s → R b₀ s n₀ + C s < R b₀ s (U n₀)) := by
  intro horient
  obtain ⟨s, hs, hK⟩ := hunbounded K
  have hlt := horient s hs
  have hle := hbound s hs
  omega

/-- Natural strict orientation gives a one-unit discrete margin. -/
theorem nat_one_step_lower_bound_of_orientation
    (R : Nat → Nat → Nat → Nat) (U : Nat → Nat) (C : Nat → Nat)
    (b s : Nat)
    (horient : ∀ n, R b s n + C s < R b s (U n)) :
    ∀ n, R b s n + (C s + 1) ≤ R b s (U n) := by
  intro n
  have h := horient n
  omega

/-- The one-step wrapper cost accumulates across repeated counter updates. -/
theorem iterated_cost_lower_bound
    (R : Nat → Nat → Nat → Nat) (U : Nat → Nat) (C : Nat → Nat)
    (b s n : Nat)
    (hstep : ∀ m, R b s m + (C s + 1) ≤ R b s (U m)) :
    ∀ k, R b s n + k * (C s + 1) ≤ R b s (iterate U k n) := by
  intro k
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
      have hs := hstep (iterate U k n)
      calc
        R b s n + (k + 1) * (C s + 1) =
            (R b s n + k * (C s + 1)) + (C s + 1) := by ring
        _ ≤ R b s (iterate U k n) + (C s + 1) :=
          Nat.add_le_add_right ih (C s + 1)
        _ ≤ R b s (U (iterate U k n)) := hs
        _ = R b s (iterate U (k + 1) n) := rfl

/-- Recursive geometric sum, oriented to the affine recurrence used below. -/
def geomSum (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => a * geomSum a k + 1

@[simp] theorem geomSum_zero (a : Nat) : geomSum a 0 = 0 := rfl

@[simp] theorem geomSum_succ (a k : Nat) :
    geomSum a (k + 1) = a * geomSum a k + 1 := rfl

/-- At multiplier one, the geometric accumulation is the iteration count. -/
theorem geomSum_one (k : Nat) : geomSum 1 k = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [geomSum, ih]

/-- At multiplier zero, every positive iteration retains one copy of the
additive margin. -/
theorem geomSum_zero_multiplier (k : Nat) : geomSum 0 (k + 1) = 1 := by
  simp [geomSum]

/-- An affine one-step recurrence unfolds to a power term plus its recursive
geometric accumulation. -/
theorem iterated_affine_lower_bound
    (R : Nat → Nat → Nat → Nat) (U : Nat → Nat)
    (a d b s n : Nat)
    (hstep : ∀ m, a * R b s m + d ≤ R b s (U m)) :
    ∀ k, a ^ k * R b s n + d * geomSum a k ≤ R b s (iterate U k n) := by
  intro k
  induction k with
  | zero => simp [iterate, geomSum]
  | succ k ih =>
      have hmul :
          a * (a ^ k * R b s n + d * geomSum a k) ≤
            a * R b s (iterate U k n) := Nat.mul_le_mul_left a ih
      have hadd := Nat.add_le_add_right hmul d
      have hs := hstep (iterate U k n)
      calc
        a ^ (k + 1) * R b s n + d * geomSum a (k + 1) =
            a * (a ^ k * R b s n + d * geomSum a k) + d := by
          simp [geomSum, pow_succ]
          ring
        _ ≤ a * R b s (iterate U k n) + d := hadd
        _ ≤ R b s (U (iterate U k n)) := hs
        _ = R b s (iterate U (k + 1) n) := rfl

/-- The additive accumulation theorem is the multiplier-one specialization of
its affine version. -/
theorem affine_one_specialization
    (R : Nat → Nat → Nat → Nat) (U : Nat → Nat)
    (d b s n k : Nat)
    (hstep : ∀ m, R b s m + d ≤ R b s (U m)) :
    R b s n + d * k ≤ R b s (iterate U k n) := by
  have h := iterated_affine_lower_bound R U 1 d b s n (by
    intro m
    simpa using hstep m) k
  simpa [geomSum_one, Nat.one_pow, Nat.one_mul] using h


/-! ## Controls -/

/-- P2.1 control: over naturals the difference form of orientation is unsound because
subtraction truncates. The collapsing wrapper `W s y = 0` with constant recursor value `5`
orients one instance; the truncated difference comparison fails there, and the integer
difference comparison holds. -/
theorem truncated_subtraction_misuse_control :
    ∃ (W : Nat → Nat → Nat) (R : Nat → Nat → Nat → Nat) (U : Nat → Nat) (b s n : Nat),
      W s (R b s n) < R b s (U n) ∧
        ¬ (W s (R b s n) - R b s n < R b s (U n) - R b s n) ∧
        ((W s (R b s n) : Int) - (R b s n : Int) < (R b s (U n) : Int) - (R b s n : Int)) :=
  ⟨fun _ _ => 0, fun _ _ _ => 5, id, 0, 0, 0, by decide, by decide, by decide⟩

/-- Recursor with increment two at every counter value. -/
def twoStepRecursor (_b _s n : Nat) : Nat := 2 * n

/-- Constant wrapper cost one. -/
def unitCost (_s : Nat) : Nat := 1

/-- Wrapper cost equal to the payload value. -/
def identityCost (s : Nat) : Nat := s

/-- Wrapper cost `s + 1` of the wrapper `W s y = y + s + 1`. -/
def successorCost (s : Nat) : Nat := s + 1

/-- Coupled recursor `(n + 1) * (s + b + 2)`. -/
def coupledRecursor (b s n : Nat) : Nat := (n + 1) * (s + b + 2)

/-- P2.2 control, bounded cost: over all payloads, the increment bound `2` holds and
orientation holds, while cost unboundedness fails. -/
theorem boundedCost_control :
    (∀ s, twoStepRecursor 0 s (0 + 1) ≤ twoStepRecursor 0 s 0 + 2) ∧
      ¬ (∀ M, ∃ s, M ≤ unitCost s) ∧
      (∀ s, twoStepRecursor 0 s 0 + unitCost s < twoStepRecursor 0 s (0 + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    simp [twoStepRecursor]
  · intro h
    obtain ⟨s, hs⟩ := h 2
    simp [unitCost] at hs
  · intro s
    simp [twoStepRecursor, unitCost]

/-- P2.2 control, coupled increment (C08): the coupled recursor has unbounded cost and orients
every instance, while every payload-independent increment bound fails. -/
theorem coupledIncrement_control :
    (∀ M, ∃ s, M ≤ successorCost s) ∧
      ¬ (∃ K, ∀ s, coupledRecursor 0 s (0 + 1) ≤ coupledRecursor 0 s 0 + K) ∧
      (∀ b s n, coupledRecursor b s n + successorCost s < coupledRecursor b s (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M
    exact ⟨M, by simp [successorCost]⟩
  · rintro ⟨K, hK⟩
    have h := hK K
    simp only [coupledRecursor] at h
    omega
  · intro b s n
    simp only [coupledRecursor, successorCost]
    nlinarith

/-- P2.2 control, collapsed payload set (C02): the cost `s` is unbounded over all naturals,
but the attained payload set `{0}` collapses it; the increment bound and orientation hold on
attained payloads, and attained-cost unboundedness fails. -/
theorem collapsedPayloadSet_control :
    (∀ M, ∃ s, M ≤ identityCost s) ∧
      (∀ s, s = 0 → twoStepRecursor 0 s (0 + 1) ≤ twoStepRecursor 0 s 0 + 2) ∧
      ¬ (∀ M, ∃ s, s = 0 ∧ M ≤ identityCost s) ∧
      (∀ s, s = 0 → twoStepRecursor 0 s 0 + identityCost s < twoStepRecursor 0 s (0 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M
    exact ⟨M, le_refl M⟩
  · intro s _
    simp [twoStepRecursor]
  · intro h
    obtain ⟨s, hs0, hs⟩ := h 1
    subst hs0
    simp [identityCost] at hs
  · intro s hs
    subst hs
    simp [twoStepRecursor, identityCost]

end OperatorKO7.Methods.OrientationClosure.IncrementCost
