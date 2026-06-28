import OperatorKO7.Meta.PolynomialBarrierGeneral

namespace OperatorKO7.NonlinearDominanceWitnesses

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- Smallest syntactic witness family for the transparent polynomial row. -/
def TrivialMonomialDominanceWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  M.monomials = [] ∧ M.succ_bias = 0 ∧ M.succ_scale = 1

/-- Explicit frozen-affine witness class: the source and target frozen polynomials
are both affine in the pumped step value, and the target dominates coefficientwise. -/
def WrapDominantFrozenAffineWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  ∃ sourceConst sourceCoeff targetConst targetCoeff : Nat,
    (∀ Sval, M.sourceFrozenAtBase Sval = sourceConst + sourceCoeff * Sval) ∧
    (∀ Sval, M.targetFrozenAtBase Sval = targetConst + targetCoeff * Sval) ∧
    sourceConst ≤ targetConst ∧
    sourceCoeff ≤ targetCoeff

/-- Broader transparent family: the successor contributes no extra base drift, so the
target frozen polynomial subsumes the source frozen polynomial directly. -/
def SuccessorIdentityDominanceWitness
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  M.succ_bias = 0 ∧ M.succ_scale = 1

/-- T.2: an explicit coefficientwise frozen-affine dominance witness closes the row. -/
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

/-- T.3: if the successor is transparent at the base, the target frozen polynomial is
the wrapped source frozen polynomial plus nonnegative drift. -/
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

/-- T.1: the trivial monomial family is eventually dominated at the base. -/
theorem trivial_monomial_eventually_dominated_at_base
    (M : BoundedPolynomialMeasure ko7Schema)
    (_hmonomials : M.monomials = [])
    (h_succ_bias : M.succ_bias = 0)
    (h_succ_scale : M.succ_scale = 1) :
    EventuallyDominatedAtBase M := by
  exact successor_identity_eventually_dominated_at_base M h_succ_bias h_succ_scale

/-- T.4: concrete witness class used by the transparent-row universal closure. -/
def TransparentDominanceWitnessClass
    (M : BoundedPolynomialMeasure ko7Schema) : Prop :=
  TrivialMonomialDominanceWitness M ∨
    WrapDominantFrozenAffineWitness M ∨
    SuccessorIdentityDominanceWitness M

/-- Any member of the concrete witness class carries the missing base-dominance witness. -/
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
