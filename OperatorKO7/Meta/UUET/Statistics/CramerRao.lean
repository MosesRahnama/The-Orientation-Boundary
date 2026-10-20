import OperatorKO7.Meta.UUET.Statistics.UnbiasedEstimator
import OperatorKO7.QEC.Bounds.CramerRao

set_option autoImplicit false

/-!
# Native finite Cramer-Rao theorem

Relation: variance and Fisher information are weighted square norms.
Closure: local unbiasedness supplies unit score covariance.
Trust: kernel-only finite Cauchy-Schwarz and ordered-field algebra.
Scope: regular finite local families with positive Fisher information.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

noncomputable def estimatorVariance {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (T : Ω -> ℝ) : ℝ :=
  ∑ ω, F.probability ω * (T ω - F.parameter) ^ 2

theorem weighted_cauchy_schwarz {Ω : Type} [Fintype Ω]
    (w : Ω -> ℝ) (a b : Ω -> ℝ) (hw : forall ω, 0 <= w ω) :
    (∑ ω, w ω * a ω * b ω) ^ 2 <=
      (∑ ω, w ω * (a ω) ^ 2) * (∑ ω, w ω * (b ω) ^ 2) := by
  let u : Ω -> ℝ := fun ω => Real.sqrt (w ω) * a ω
  let v : Ω -> ℝ := fun ω => Real.sqrt (w ω) * b ω
  have hcross : (∑ ω, u ω * v ω) = ∑ ω, w ω * a ω * b ω := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [u, v]
    calc
      (Real.sqrt (w ω) * a ω) * (Real.sqrt (w ω) * b ω) =
          (Real.sqrt (w ω)) ^ 2 * a ω * b ω := by ring
      _ = w ω * a ω * b ω := by rw [Real.sq_sqrt (hw ω)]
  have hleft : (∑ ω, (u ω) ^ 2) = ∑ ω, w ω * (a ω) ^ 2 := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [u]
    calc
      (Real.sqrt (w ω) * a ω) ^ 2 =
          (Real.sqrt (w ω)) ^ 2 * (a ω) ^ 2 := by ring
      _ = w ω * (a ω) ^ 2 := by rw [Real.sq_sqrt (hw ω)]
  have hright : (∑ ω, (v ω) ^ 2) = ∑ ω, w ω * (b ω) ^ 2 := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [v]
    calc
      (Real.sqrt (w ω) * b ω) ^ 2 =
          (Real.sqrt (w ω)) ^ 2 * (b ω) ^ 2 := by ring
      _ = w ω * (b ω) ^ 2 := by rw [Real.sq_sqrt (hw ω)]
  have h := OperatorKO7.QEC.Bounds.CramerRao.finite_cauchy_schwarz u v
  rwa [hcross, hleft, hright] at h

theorem cramer_rao_bound {Ω : Type} [Fintype Ω]
    {F : ParametricFamily Ω} (E : UnbiasedEstimator F)
    (hf : 0 < fisherInformation F) :
    1 / fisherInformation F <= estimatorVariance F E.estimate := by
  have hcs := weighted_cauchy_schwarz F.probability
    (fun ω => E.estimate ω - F.parameter) (score F)
    F.probability_nonnegative
  have hmain : 1 <= estimatorVariance F E.estimate * fisherInformation F := by
    calc
      1 = (scoreCovariance F E.estimate) ^ 2 := by
        rw [unbiased_score_identity E]
        norm_num
      _ <= (∑ ω, F.probability ω * (E.estimate ω - F.parameter) ^ 2) *
          (∑ ω, F.probability ω * (score F ω) ^ 2) := hcs
      _ = estimatorVariance F E.estimate * fisherInformation F := rfl
  rw [div_le_iff₀ hf]
  exact hmain

/-- Negative fixture: zero-Fisher models are outside the division theorem. -/
theorem constant_family_outside_positive_fisher :
    Not (0 < fisherInformation constantBinaryFamily) := by
  rw [constant_family_fisher_zero]
  norm_num

/-! Imported NameGate and TypeGate. -/
#check @OperatorKO7.QEC.Bounds.CramerRao.finite_cauchy_schwarz
#check @Real.sq_sqrt
#check @estimatorVariance
#check @weighted_cauchy_schwarz

#check @cramer_rao_bound
#check @constant_family_outside_positive_fisher
#print axioms weighted_cauchy_schwarz
#print axioms cramer_rao_bound
#print axioms constant_family_outside_positive_fisher

end OperatorKO7.Meta.UUET.Statistics
