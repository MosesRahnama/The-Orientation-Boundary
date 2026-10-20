import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.Core

/-!
# KO7 `StepStar` / exact-length `Reach Step` bridge

The kernel and quantitative Distinction stack use separate reflexive-transitive
closure encodings. This file proves both directions explicitly rather than
silently identifying them.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7ExactClosureBridge

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Kernel `StepStar` implies exact-length existential `Reach Step`. -/
theorem stepStar_to_reach {x y : Trace} (h : StepStar x y) : Reach Step x y := by
  induction h with
  | refl t => exact reach_refl t
  | @tail a b c hab hbc ih =>
      exact reach_trans (reach_step hab) ih

/-- An exact-length `Steps Step n` path gives kernel `StepStar`. -/
theorem steps_to_stepStar {n : Nat} {x y : Trace} (h : Steps Step n x y) : StepStar x y := by
  induction h with
  | zero => exact StepStar.refl _
  | @succ n a b c hab hbc ih => exact StepStar.tail hab ih

/-- Exact-length existential `Reach Step` implies kernel `StepStar`. -/
theorem reach_to_stepStar {x y : Trace} (h : Reach Step x y) : StepStar x y := by
  rcases h with ⟨n, hn⟩
  exact steps_to_stepStar hn

/-- The two closure encodings are extensionally equivalent. -/
theorem stepStar_iff_reach {x y : Trace} :
    StepStar x y ↔ Reach Step x y :=
  ⟨stepStar_to_reach, reach_to_stepStar⟩

/-- Kernel normal form equals the quantitative one-step normal-form predicate. -/
theorem kernelNormalForm_iff_quantNormalForm {x : Trace} :
    OperatorKO7.NormalForm x ↔
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.NormalForm Step x := by
  constructor
  · intro h y hy
    exact h ⟨y, hy⟩
  · intro h
    rintro ⟨y, hy⟩
    exact h y hy

/-- The existing kernel normal-form forward theorem is recovered through the
exact closure bridge. -/
theorem quant_normal_reach_eq
    {x y : Trace}
    (hnf : OperatorKO7.NormalForm x)
    (hxy : Reach Step x y) : x = y :=
  nf_no_stepstar_forward hnf (reach_to_stepStar hxy)

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7ExactClosureBridge
