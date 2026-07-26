import OperatorKO7.Meta.PolynomialBarrierGeneral

namespace OperatorKO7.NonlinearDominanceWitnesses

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- The successor-identity conditions together with an additional empty-monomial premise. -/
def TrivialMonomialDominanceWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  M.monomials = [] ∧ M.succ_bias = 0 ∧ M.succ_scale = 1

/-- Supplied affine formulas for the source and target frozen evaluations, together with
coefficientwise inequalities. -/
def WrapDominantFrozenAffineWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  ∃ sourceConst sourceCoeff targetConst targetCoeff : Nat,
    (∀ Sval, M.sourceFrozenAtBase Sval = sourceConst + sourceCoeff * Sval) ∧
    (∀ Sval, M.targetFrozenAtBase Sval = targetConst + targetCoeff * Sval) ∧
    sourceConst ≤ targetConst ∧
    sourceCoeff ≤ targetCoeff

/-- The two successor parameters are fixed to bias zero and scale one. -/
def SuccessorIdentityDominanceWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  M.succ_bias = 0 ∧ M.succ_scale = 1

/-- The supplied affine formulas and coefficient inequalities imply base-level eventual dominance. -/
theorem wrap_dominant_eventually_dominated_at_base
    (M : BoundedPolynomialMeasure ko7Schema)
    (hwitness : WrapDominantFrozenAffineWitness M) :
    EventuallyDominatedAtBase M := by
  rcases hwitness with ⟨sourceConst, sourceCoeff, targetConst, targetCoeff,
    hsource, htarget, hconst, hcoeff⟩
  refine ⟨0, ?_⟩
  intro Sval _hSval
  rw [hsource Sval, htarget Sval]
  exact Nat.add_le_add hconst (Nat.mul_le_mul_right Sval hcoeff)

/-- Bias zero and scale one make the target frozen evaluation the wrapped source evaluation plus
nonnegative terms. -/
theorem successor_identity_eventually_dominated_at_base
    (M : BoundedPolynomialMeasure ko7Schema)
    (h_succ_bias : M.succ_bias = 0)
    (h_succ_scale : M.succ_scale = 1) :
    EventuallyDominatedAtBase M := by
  refine ⟨0, ?_⟩
  intro Sval _hSval
  have hwrap :
      M.targetFrozenAtBase Sval =
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * M.sourceFrozenAtBase Sval := by
    simp [BoundedPolynomialMeasure.targetFrozenAtBase,
      BoundedPolynomialMeasure.sourceFrozenAtBase,
      h_succ_bias, h_succ_scale, Nat.add_assoc, Nat.mul_assoc, Nat.left_distrib]
  rw [hwrap]
  have hsource_le_scaled :
      M.sourceFrozenAtBase Sval ≤ M.wrap_right * M.sourceFrozenAtBase Sval := by
    calc
      M.sourceFrozenAtBase Sval = 1 * M.sourceFrozenAtBase Sval := by simp
      _ ≤ M.sourceFrozenAtBase Sval * M.wrap_right := by
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_left (M.sourceFrozenAtBase Sval) M.h_wrap_right_pos
      _ = M.wrap_right * M.sourceFrozenAtBase Sval := by rw [Nat.mul_comm]
  exact le_trans hsource_le_scaled (Nat.le_add_left _ _)

/-- A compatibility wrapper around `successor_identity_eventually_dominated_at_base`. The
empty-monomial premise is retained in this signature but is not needed by the proof. -/
theorem trivial_monomial_eventually_dominated_at_base
    (M : BoundedPolynomialMeasure ko7Schema)
    (_hmonomials : M.monomials = [])
    (h_succ_bias : M.succ_bias = 0)
    (h_succ_scale : M.succ_scale = 1) :
    EventuallyDominatedAtBase M := by
  exact successor_identity_eventually_dominated_at_base M h_succ_bias h_succ_scale

/-- Union of three sufficient witness predicates. The first predicate is contained in the third. -/
def TransparentDominanceWitnessClass
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  TrivialMonomialDominanceWitness M ∨
    WrapDominantFrozenAffineWitness M ∨
    SuccessorIdentityDominanceWitness M

/-- Each branch of `TransparentDominanceWitnessClass` implies base-level eventual dominance. -/
theorem transparent_dominance_witness_class_eventually_dominated_at_base
    (M : BoundedPolynomialMeasure ko7Schema)
    (hwitness : TransparentDominanceWitnessClass M) :
    EventuallyDominatedAtBase M := by
  rcases hwitness with htrivial | hwrap | hsucc
  · rcases htrivial with ⟨hmonomials, h_succ_bias, h_succ_scale⟩
    exact
      trivial_monomial_eventually_dominated_at_base M hmonomials h_succ_bias h_succ_scale
  · exact wrap_dominant_eventually_dominated_at_base M hwrap
  · rcases hsucc with ⟨h_succ_bias, h_succ_scale⟩
    exact successor_identity_eventually_dominated_at_base M h_succ_bias h_succ_scale

end OperatorKO7.NonlinearDominanceWitnesses
