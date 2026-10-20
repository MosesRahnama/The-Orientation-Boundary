import OperatorKO7.Meta.PumpedBarrierClasses_Schema
import OperatorKO7.Meta.ProjectedPrimaryBarrier
import OperatorKO7.Meta.MatrixBarrierLexPermD_Schema
import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.ArcticBarrier_Schema
import OperatorKO7.Meta.TropicalBarrier_Schema
import OperatorKO7.Meta.WPO_PolynomialBarrier_Schema

set_option autoImplicit false

/-!
# Pump Discharge: the growth hypotheses of the direct barrier stack are redundant

Every scalar and vector barrier in the orientation-boundary stack was stated with an
explicit growth hypothesis: `HasUnboundedRange`, a positive successor pump, or a positive
wrap/base pump. This module proves that the hypothesis is discharged by the wrapper
interface itself.

The mechanism is the self-nested wrapper chain `t, wrap t t, wrap (wrap t t) (wrap t t), ...`
(`wrapDouble`). Every family in the stack requires both wrapper coefficients to be at least
one (`h_wrap_left_pos`, `h_wrap_right_pos`), so the value at `wrap t t` is at least twice the
value at `t`. Hence a measure with a single positive value is unbounded, and a measure with no
positive value is identically zero and cannot strictly orient anything. Strict orientation of
the duplicating step at `(base, base, base)` already produces a positive value, so the
strict barriers become unconditional:

* `no_affine_orients_dup_step`, `no_quadratic_counter_orients_dup_step`,
  `no_max_orients_dup_step` (max-plus needs no positive value at all, since the right
  wrapper offset is positive),
* `no_cross_quadratic_orients_dup_step_of_bounded`,
  `no_multilinear_orients_dup_step_of_dominated`,
  `no_polynomial_orients_dup_step_of_dominated`,
  `no_wpoPolynomialDirect_orients_dup_step_of_dominated`: only the load-bearing
  base-dominance hypothesis survives,
* `no_matrixD_orients_dup_step`, `no_matrix2_orients_dup_step`,
  `no_matrixFunctional_orients_dup_step`, `no_matrixMix2_orients_dup_step`: strict
  componentwise orders force a positive tracked scalar, so they are unconditional,
* `no_matrixLexD_orients_dup_step_of_primary_pos`,
  `no_matrixLexPermD_orients_dup_step_of_primary_pos`,
  `no_matrix2_lex_orients_dup_step_of_fst_pos`,
  `no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos`,
  `no_orients_dup_step_of_projected_primary_dominance_of_pos`: orders that only force
  nonincrease of the tracked scalar keep one premise, that the tracked scalar is positive
  somewhere. `zeroAffineMeasure` shows this premise cannot be dropped: the identically-zero
  measure makes every duplicating step nonincreasing.

Relation: the schema duplicating step `recur b s (succ n) → wrap s (recur b s n)` at the root,
and `GlobalOrients` on any system containing it.
Closure: root; global versions quantify over every step of the system.
External trust: none. Mathlib only. The dichotomy lemma
`affine_zero_or_hasUnboundedRange` uses classical case analysis; every barrier theorem below
avoids it by extracting the positive value from the orientation hypothesis directly.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Self-nested wrapper chain `t, wrap t t, wrap (wrap t t) (wrap t t), ...`. -/
def wrapDouble (S : StepDuplicatingSchema) (t : S.T) : Nat → S.T
  | 0 => t
  | k + 1 => S.wrap (wrapDouble S t k) (wrapDouble S t k)

@[simp] theorem wrapDouble_zero (S : StepDuplicatingSchema) (t : S.T) :
    wrapDouble S t 0 = t := rfl

@[simp] theorem wrapDouble_succ (S : StepDuplicatingSchema) (t : S.T) (k : Nat) :
    wrapDouble S t (k + 1) = S.wrap (wrapDouble S t k) (wrapDouble S t k) := rfl

/-! ## Affine measures -/

/-- Along the self-nested wrapper chain an affine measure at least doubles at every level,
so one positive value yields `k + 1` at level `k`. -/
theorem eval_wrapDouble_ge_affine {S : StepDuplicatingSchema} (M : AffineMeasure S)
    {t : S.T} (ht : 1 ≤ M.eval t) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_right_pos
      omega

/-- One positive value makes an affine measure with positive wrapper coefficients unbounded. -/
theorem affine_hasUnboundedRange_of_exists_pos {S : StepDuplicatingSchema}
    (M : AffineMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    HasUnboundedRange M := by
  rcases hpos with ⟨t, ht⟩
  intro k
  refine ⟨wrapDouble S t k, ?_⟩
  have := eval_wrapDouble_ge_affine M ht k
  omega

/-- Dichotomy: an affine measure with positive wrapper coefficients is identically zero or
unbounded. Uses classical case analysis on the existence of a positive value. -/
theorem affine_zero_or_hasUnboundedRange {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    (∀ t : S.T, M.eval t = 0) ∨ HasUnboundedRange M := by
  by_cases h : ∃ t : S.T, 1 ≤ M.eval t
  · exact Or.inr (affine_hasUnboundedRange_of_exists_pos M h)
  · left
    intro t
    have : ¬ 1 ≤ M.eval t := fun h1 => h ⟨t, h1⟩
    omega

/-- **Unconditional affine barrier.** No constructor-local affine measure with positive
wrapper coefficients strictly orients the duplicating step. The growth hypothesis of
`no_affine_orients_dup_step_of_unbounded` is discharged: orientation at
`(base, base, base)` yields a positive value, and one positive value is unbounded. -/
theorem no_affine_orients_dup_step {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := h S.base S.base S.base
    omega
  exact no_affine_orients_dup_step_of_unbounded M
    (affine_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) h

/-- Nonstrict form: an affine measure with one positive value cannot even be nonincreasing
across the duplicating step. The positivity premise is necessary
(`zeroAffineMeasure_nonstrict_orients`). -/
theorem no_affine_primary_nonstrict_orients_dup_step_of_exists_pos
    {S : StepDuplicatingSchema} (M : AffineMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n))) :=
  no_affine_primary_nonstrict_orients_dup_step_of_unbounded M
    (affine_hasUnboundedRange_of_exists_pos M hpos)

/-- The identically-zero affine measure. It satisfies every field of `AffineMeasure`,
including both wrapper positivity fields. -/
def zeroAffineMeasure (S : StepDuplicatingSchema) : AffineMeasure S where
  eval := fun _ => 0
  c_base := 0
  succ_bias := 0
  succ_scale := 0
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 0
  eval_base := rfl
  eval_succ := fun _ => by simp
  eval_wrap := fun _ _ => by simp
  eval_recur := fun _ _ _ => by simp
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-- The zero measure is nonincreasing across every duplicating step. -/
theorem zeroAffineMeasure_nonstrict_orients (S : StepDuplicatingSchema) :
    ∀ (b s n : S.T),
      (zeroAffineMeasure S).eval (S.wrap s (S.recur b s n)) ≤
        (zeroAffineMeasure S).eval (S.recur b s (S.succ n)) :=
  fun _ _ _ => le_refl 0

/-- The positivity premise of the nonstrict barrier cannot be dropped. -/
theorem nonstrict_affine_barrier_positivity_premise_necessary (S : StepDuplicatingSchema) :
    ¬ (∀ M : AffineMeasure S,
      ¬ (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n)))) :=
  fun h => h (zeroAffineMeasure S) (zeroAffineMeasure_nonstrict_orients S)

/-- Unconditional global affine barrier. -/
theorem no_global_orients_affine {Sys : StepDuplicatingSystem}
    (M : AffineMeasure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact no_affine_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

/-- No global orienter is representable by any affine measure of the class, with no growth
premise on the representing measure. -/
theorem global_orienter_not_affine_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ M : AffineMeasure Sys.toStepDuplicatingSchema, M.eval = μ := by
  rintro ⟨M, hM⟩
  subst hM
  exact no_global_orients_affine M horient

/-! ## Restricted quadratic measures -/

theorem eval_wrapDouble_ge_quadratic {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) {t : S.T} (ht : 1 ≤ M.eval t) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_right_pos
      omega

theorem quadratic_hasUnboundedRange_of_exists_pos {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    HasUnboundedRangeQ M := by
  rcases hpos with ⟨t, ht⟩
  intro k
  refine ⟨wrapDouble S t k, ?_⟩
  have := eval_wrapDouble_ge_quadratic M ht k
  omega

/-- **Unconditional restricted quadratic barrier.** -/
theorem no_quadratic_counter_orients_dup_step {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := h S.base S.base S.base
    omega
  exact no_quadratic_counter_orients_dup_step_of_unbounded M
    (quadratic_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) h

theorem no_global_orients_quadratic {Sys : StepDuplicatingSystem}
    (M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact no_quadratic_counter_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

theorem global_orienter_not_quadratic_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema, M.eval = μ := by
  rintro ⟨M, hM⟩
  subst hM
  exact no_global_orients_quadratic M horient

/-! ## Bounded cross-term quadratic measures -/

theorem eval_wrapDouble_ge_cross {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) {t : S.T} (ht : 1 ≤ M.eval t) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_right_pos
      omega

theorem crossTerm_hasUnboundedRange_of_exists_pos {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    HasUnboundedRangeX M := by
  rcases hpos with ⟨t, ht⟩
  intro k
  refine ⟨wrapDouble S t k, ?_⟩
  have := eval_wrapDouble_ge_cross M ht k
  omega

/-- Bounded cross-term barrier with the growth hypothesis discharged; only the base-point
coupling bound remains. -/
theorem no_cross_quadratic_orients_dup_step_of_bounded {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (hbounded : CrossTermBoundedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := h S.base S.base S.base
    omega
  exact no_cross_quadratic_orients_dup_step_of_unbounded M
    (crossTerm_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) hbounded h

theorem no_global_orients_cross_quadratic_of_bounded {Sys : StepDuplicatingSystem}
    (M : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact no_cross_quadratic_orients_dup_step_of_bounded (S := Sys.toStepDuplicatingSchema)
    M hbounded (fun b s n => h (Sys.dup_step b s n))

/-! ## Bounded multilinear measures -/

theorem eval_wrapDouble_ge_multilinear {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) {t : S.T} (ht : 1 ≤ M.eval t) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_right_pos
      omega

theorem multilinear_hasUnboundedRange_of_exists_pos {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    HasUnboundedRangeML M := by
  rcases hpos with ⟨t, ht⟩
  intro k
  refine ⟨wrapDouble S t k, ?_⟩
  have := eval_wrapDouble_ge_multilinear M ht k
  omega

/-- Bounded multilinear barrier with the growth hypothesis discharged; only the frozen
base-point dominance remains. -/
theorem no_multilinear_orients_dup_step_of_dominated {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := h S.base S.base S.base
    omega
  exact no_multilinear_orients_dup_step_of_unbounded M
    (multilinear_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) hdom h

theorem no_global_orients_multilinear_of_dominated {Sys : StepDuplicatingSystem}
    (M : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact no_multilinear_orients_dup_step_of_dominated (S := Sys.toStepDuplicatingSchema)
    M hdom (fun b s n => h (Sys.dup_step b s n))

/-! ## Generalized degree-bounded polynomial measures -/

theorem eval_wrapDouble_ge_poly {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) {t : S.T} (ht : 1 ≤ M.eval t) (k : Nat) :
    k + 1 ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hl := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_left_pos
      have hr := Nat.le_mul_of_pos_left (M.eval (wrapDouble S t k)) M.h_wrap_right_pos
      omega

theorem polynomial_hasUnboundedRange_of_exists_pos {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    HasUnboundedRangePoly M := by
  rcases hpos with ⟨t, ht⟩
  intro k
  refine ⟨wrapDouble S t k, ?_⟩
  have := eval_wrapDouble_ge_poly M ht k
  omega

/-- Generalized polynomial barrier with the growth hypothesis discharged; only eventual
frozen base-point dominance remains. -/
theorem no_polynomial_orients_dup_step_of_dominated {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (hdom : EventuallyDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := h S.base S.base S.base
    omega
  exact no_polynomial_orients_dup_step_of_unbounded M
    (polynomial_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) hdom h

/-- Every successful orienter in the generalized polynomial family violates frozen base
dominance, with no growth premise. -/
theorem polynomial_orienter_violates_base_dominance {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S)
    (horient : ∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :
    ¬ EventuallyDominatedAtBase M :=
  fun hdom => no_polynomial_orients_dup_step_of_dominated M hdom horient

theorem no_global_orients_polynomial_of_dominated {Sys : StepDuplicatingSystem}
    (M : BoundedPolynomialMeasure Sys.toStepDuplicatingSchema)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact no_polynomial_orients_dup_step_of_dominated (S := Sys.toStepDuplicatingSchema)
    M hdom (fun b s n => h (Sys.dup_step b s n))

/-- WPO-facing polynomial branch with the growth hypothesis discharged. -/
theorem no_wpoPolynomialDirect_orients_dup_step_of_dominated {S : StepDuplicatingSchema}
    (W : WPOPolynomialDirectOrder S) (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ (∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) := by
  intro h
  exact no_polynomial_orients_dup_step_of_dominated W.measure hdom
    (fun b s n => W.sound (h b s n))

theorem no_global_orients_wpoPolynomialDirect_of_dominated {Sys : StepDuplicatingSystem}
    (W : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => W.gt y x) := by
  intro h
  exact no_wpoPolynomialDirect_orients_dup_step_of_dominated
    (S := Sys.toStepDuplicatingSchema) W hdom (fun b s n => h (Sys.dup_step b s n))

/-! ## Max-plus measures: unbounded with no positive value at all -/

/-- The right wrapper offset is positive, so the self-nested chain from any term grows by at
least one per level. -/
theorem eval_wrapDouble_ge_max {S : StepDuplicatingSchema} (M : MaxMeasure S) (t : S.T)
    (k : Nat) :
    k ≤ M.eval (wrapDouble S t k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      rw [wrapDouble_succ, M.eval_wrap]
      have hmax :=
        le_max_right (M.wrap_left + M.eval (wrapDouble S t k))
          (M.wrap_right + M.eval (wrapDouble S t k))
      have := M.h_wrap_right_pos
      omega

/-- Every max-plus measure of the class has unbounded range. -/
theorem max_hasUnboundedRange {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    HasUnboundedRangeMax M :=
  fun k => ⟨wrapDouble S S.base k, eval_wrapDouble_ge_max M S.base k⟩

/-- **Unconditional max-plus barrier.** -/
theorem no_max_orients_dup_step {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  no_max_orients_dup_step_of_unbounded M (max_hasUnboundedRange M)

theorem no_global_orients_max {Sys : StepDuplicatingSystem}
    (M : MaxMeasure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) :=
  no_global_orients_max_of_unbounded M (max_hasUnboundedRange M)

/-- Unconditional arctic primary-projection barrier. -/
theorem no_arctic_primary_orients_dup_step {S : StepDuplicatingSchema}
    (M : ArcticPrimaryMeasure S) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_arctic_primary_orients_dup_step_of_unbounded M (max_hasUnboundedRange M.projectedMax)

/-- Unconditional tropical primary-projection barrier. -/
theorem no_tropical_primary_orients_dup_step {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_tropical_primary_orients_dup_step_of_unbounded M (max_hasUnboundedRange M.projectedMax)

/-! ## Projected-primary meta-barriers -/

/-- Projected-primary dominance with the growth hypothesis reduced to one positive value of
the tracked scalar. -/
theorem no_orients_dup_step_of_projected_primary_dominance_of_pos
    {S : StepDuplicatingSchema} {α : Type}
    (μ : S.T → α) (R : α → α → Prop) (π : α → Nat)
    (hdom : ∀ {u v : α}, R u v → π u ≤ π v)
    (M : AffineMeasure S)
    (heval : ∀ t : S.T, M.eval t = π (μ t))
    (hpos : ∃ t : S.T, 1 ≤ M.eval t) :
    ¬ (∀ (b s n : S.T), R (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance μ R π hdom M heval
    (affine_hasUnboundedRange_of_exists_pos M hpos)

/-- Projected-primary barrier for orders whose strict comparison forces strict decrease of
the tracked scalar: unconditional, since orientation at `(base, base, base)` supplies the
positive value. -/
theorem no_orients_dup_step_of_projected_primary_strict
    {S : StepDuplicatingSchema} {α : Type}
    (μ : S.T → α) (R : α → α → Prop) (π : α → Nat)
    (hstrict : ∀ {u v : α}, R u v → π u < π v)
    (M : AffineMeasure S)
    (heval : ∀ t : S.T, M.eval t = π (μ t)) :
    ¬ (∀ (b s n : S.T), R (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))) := by
  intro h
  have hpos : 1 ≤ M.eval (S.recur S.base S.base (S.succ S.base)) := by
    have := hstrict (h S.base S.base S.base)
    rw [heval]
    omega
  exact no_orients_dup_step_of_projected_primary_dominance μ R π
    (fun huv => Nat.le_of_lt (hstrict huv)) M heval
    (affine_hasUnboundedRange_of_exists_pos M ⟨_, hpos⟩) h

theorem no_global_orients_of_projected_primary_dominance_of_pos
    {Sys : StepDuplicatingSystem} {α : Type}
    (μ : Sys.toStepDuplicatingSchema.T → α) (R : α → α → Prop) (π : α → Nat)
    (hdom : ∀ {u v : α}, R u v → π u ≤ π v)
    (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (heval : ∀ t : Sys.toStepDuplicatingSchema.T, M.eval t = π (μ t))
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t) :
    ¬ GlobalOrients Sys μ R := by
  intro h
  exact no_orients_dup_step_of_projected_primary_dominance_of_pos μ R π hdom M heval hpos
    (fun b s n => h (Sys.dup_step b s n))

theorem no_global_orients_of_projected_primary_strict
    {Sys : StepDuplicatingSystem} {α : Type}
    (μ : Sys.toStepDuplicatingSchema.T → α) (R : α → α → Prop) (π : α → Nat)
    (hstrict : ∀ {u v : α}, R u v → π u < π v)
    (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (heval : ∀ t : Sys.toStepDuplicatingSchema.T, M.eval t = π (μ t)) :
    ¬ GlobalOrients Sys μ R := by
  intro h
  exact no_orients_dup_step_of_projected_primary_strict μ R π hstrict M heval
    (fun b s n => h (Sys.dup_step b s n))

/-! ## Vector and pair families -/

/-- **Unconditional tracked componentwise barrier**, any finite dimension. -/
theorem no_matrixD_orients_dup_step {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_strict
    (μ := M.eval) (R := VecLt) (π := fun v => v tracked)
    (fun h => h tracked) M.trackedAffine (fun _ => rfl)

theorem no_global_orients_matrixD {Sys : StepDuplicatingSystem} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD Sys.toStepDuplicatingSchema d tracked) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact no_matrixD_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

/-- **Unconditional tracked-primary pair barrier** for strict componentwise order. -/
theorem no_matrix2_orients_dup_step {S : StepDuplicatingSchema} (M : MatrixMeasure2 S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_strict
    (μ := M.eval) (R := PairLt) (π := Prod.fst)
    (fun h => h.1) M.fstAffine (fun _ => rfl)

theorem no_global_orients_matrix2 {Sys : StepDuplicatingSystem}
    (M : MatrixMeasure2 Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  intro h
  exact no_matrix2_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

/-- Lexicographic pair barrier: one positive first component replaces the pump. -/
theorem no_matrix2_lex_orients_dup_step_of_fst_pos {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S) (hpos : ∃ t : S.T, 1 ≤ (M.eval t).1) :
    ¬ (∀ (b s n : S.T),
      PairLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance_of_pos
    (μ := M.eval) (R := PairLexLt) (π := Prod.fst)
    (fun h => fst_le_of_pairLexLt h) M.fstAffine (fun _ => rfl) hpos

theorem no_global_orients_matrix2_lex_of_fst_pos {Sys : StepDuplicatingSystem}
    (M : MatrixMeasure2 Sys.toStepDuplicatingSchema)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ (M.eval t).1) :
    ¬ GlobalOrients Sys M.eval PairLexLt := by
  intro h
  exact no_matrix2_lex_orients_dup_step_of_fst_pos (S := Sys.toStepDuplicatingSchema) M hpos
    (fun b s n => h (Sys.dup_step b s n))

/-- **Unconditional weighted scalar-projection barrier.** -/
theorem no_matrixFunctional_orients_dup_step {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_strict
    (μ := M.eval) (R := VecLt) (π := weightedSum M.weight)
    (fun h => weightedSum_lt_of_vecLt M.h_weight_support h)
    M.projectedAffine (fun _ => rfl)

theorem no_global_orients_matrixFunctional {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixFunctionalMeasure Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact no_matrixFunctional_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

/-- **Unconditional balanced mixed-coordinate barrier.** -/
theorem no_matrixMix2_orients_dup_step {S : StepDuplicatingSchema} (M : MatrixMix2Measure S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_strict
    (μ := M.eval) (R := PairLt) (π := vecSum)
    (fun h => vecSum_lt_of_pairLt h) M.sumAffine (fun _ => rfl)

theorem no_global_orients_matrixMix2 {Sys : StepDuplicatingSystem}
    (M : MatrixMix2Measure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  intro h
  exact no_matrixMix2_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
    (fun b s n => h (Sys.dup_step b s n))

/-- Finite tracked-primary lexicographic barrier: one positive primary value replaces the
pump. -/
theorem no_matrixLexD_orients_dup_step_of_primary_pos {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureD S d) (hpos : ∃ t : S.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance_of_pos
    (μ := M.eval) (R := VecLexLt) (π := fun v => v (primaryIdx d))
    (fun h => primary_le_of_vecLexLt h) M.primaryAffine (fun _ => rfl) hpos

theorem no_global_orients_matrixLexD_of_primary_pos {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixLexMeasureD Sys.toStepDuplicatingSchema d)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients Sys M.eval VecLexLt := by
  intro h
  exact no_matrixLexD_orients_dup_step_of_primary_pos (S := Sys.toStepDuplicatingSchema) M hpos
    (fun b s n => h (Sys.dup_step b s n))

/-- Permutation-priority lexicographic barrier: one positive primary value replaces the
pump. -/
theorem no_matrixLexPermD_orients_dup_step_of_primary_pos {S : StepDuplicatingSchema}
    {d : Nat} (M : MatrixLexPermMeasureD S d)
    (hpos : ∃ t : S.T, 1 ≤ M.eval t (permPrimaryIdx M.priority)) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt M.priority (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance_of_pos
    (μ := M.eval) (R := VecPermLexLt M.priority) (π := fun v => v (permPrimaryIdx M.priority))
    (fun h => permPrimary_le_of_vecPermLexLt h) M.primaryAffine (fun _ => rfl) hpos

theorem no_global_orients_matrixLexPermD_of_primary_pos {Sys : StepDuplicatingSystem}
    {d : Nat} (M : MatrixLexPermMeasureD Sys.toStepDuplicatingSchema d)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ M.eval t (permPrimaryIdx M.priority)) :
    ¬ GlobalOrients Sys M.eval (VecPermLexLt M.priority) := by
  intro h
  exact no_matrixLexPermD_orients_dup_step_of_primary_pos (S := Sys.toStepDuplicatingSchema)
    M hpos (fun b s n => h (Sys.dup_step b s n))

/-- Scalar-dominance mixed-matrix barrier: one positive scalarized value replaces the pump. -/
theorem no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight R)
    (hpos : ∃ t : S.T, 1 ≤ matrixScalarize M.weight (M.eval t)) :
    ¬ (∀ (b s n : S.T),
      R (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) :=
  no_orients_dup_step_of_projected_primary_dominance_of_pos
    (μ := M.eval) (R := R) (π := matrixScalarize M.weight)
    (fun h => D.nonstrict h) M.scalarAffine (fun _ => rfl) hpos

theorem no_global_orients_matrixArbitrary_of_scalar_dominance_of_pos
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixArbitraryMeasure Sys.toStepDuplicatingSchema d)
    {R : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight R)
    (hpos : ∃ t : Sys.toStepDuplicatingSchema.T, 1 ≤ matrixScalarize M.weight (M.eval t)) :
    ¬ GlobalOrients Sys M.eval R := by
  intro h
  exact no_matrixArbitrary_orients_dup_step_of_scalar_dominance_of_pos
    (S := Sys.toStepDuplicatingSchema) M D hpos (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
