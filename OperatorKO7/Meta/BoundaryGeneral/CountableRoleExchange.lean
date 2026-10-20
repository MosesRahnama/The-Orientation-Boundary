import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Order
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# Countable role exchange

The finite role-exchange result uses a uniform reference law on a finite role alphabet. On countably infinite support, no uniform probability law exists, so `countableRoleDivergence ν ρ` measures divergence from a chosen reference law `ρ`. The `tsum` definition applies to any index type.

For finite types, `countableRoleDivergence_fintype` reduces this sum to the finite sum. With a uniform reference on a finite alphabet, `countableRoleDivergence_uniform` identifies it with `klFromUniform`. The `countableRoleDivergence_nonneg_of_equal_mass` theorem proves nonnegativity when both laws have equal total mass, the first law is nonnegative, the reference law is strictly positive, and the divergence series converges. The `countableRoleDivergence_nonneg` theorem is its probability-mass-one specialization.

Convergence of the divergence series is required for the countable nonnegativity theorem. On countable support, the series can diverge, and the theorem states the hypothesis explicitly.

`countable_recovers_finite_role_exchange` proves that on a finite alphabet, divergence from the uniform law equals the finite role gap and vanishes exactly for the uniform law.

Trust: proofs use Mathlib and Lean kernel checking; no external tool output is used as a proof certificate.
-/

namespace OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-- Divergence of a role law from a reference law, at any index type. -/
noncomputable def countableRoleDivergence {C : Type} (nu rho : C → Real) : Real :=
  ∑' c, nu c * Real.log (nu c / rho c)

/-- On a finite alphabet the countable divergence is the finite sum. -/
theorem countableRoleDivergence_fintype {C : Type} [Fintype C] (nu rho : C → Real) :
    countableRoleDivergence nu rho = ∑ c, nu c * Real.log (nu c / rho c) := by
  simp [countableRoleDivergence, tsum_fintype]

/-- On a finite alphabet, divergence from the uniform reference equals `klFromUniform`. -/
theorem countableRoleDivergence_uniform {C : Type} [Fintype C] [Nonempty C] (nu : C → Real) :
    countableRoleDivergence nu (uniformMass C) = klFromUniform nu := by
  rw [countableRoleDivergence_fintype]
  unfold klFromUniform uniformMass
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hcard : (Fintype.card C : Real) ≠ 0 := ne_of_gt (card_cast_pos C)
  congr 1
  field_simp

/-- Termwise Gibbs: the negated divergence summand is bounded by the difference of the laws. -/
theorem neg_divergence_term_le {C : Type} (nu rho : C → Real)
    (hnu0 : ∀ c, 0 ≤ nu c) (hrho0 : ∀ c, 0 < rho c) (c : C) :
    -(nu c * Real.log (nu c / rho c)) ≤ rho c - nu c := by
  rcases eq_or_lt_of_le (hnu0 c) with h | h
  · simp [← h]
    exact le_of_lt (hrho0 c)
  · have hpos : 0 < rho c / nu c := div_pos (hrho0 c) h
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hflip : Real.log (rho c / nu c) = -Real.log (nu c / rho c) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hflip] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
    have hcancel : nu c * (rho c / nu c - 1) = rho c - nu c := by
      field_simp
    rw [hcancel] at hmul
    calc -(nu c * Real.log (nu c / rho c)) = nu c * -Real.log (nu c / rho c) := by ring
      _ ≤ rho c - nu c := hmul

/-- **Gibbs at equal countable mass.** The divergence of a nonnegative law from a strictly positive
reference law is nonnegative whenever the two laws have the same total mass and the divergence
series converges.  Probability laws are the mass-one specialization. -/
theorem countableRoleDivergence_nonneg_of_equal_mass {C : Type} (nu rho : C → Real) (m : Real)
    (hnu0 : ∀ c, 0 ≤ nu c) (hrho0 : ∀ c, 0 < rho c)
    (hnuMass : HasSum nu m) (hrhoMass : HasSum rho m)
    (hsum : Summable (fun c => nu c * Real.log (nu c / rho c))) :
    0 ≤ countableRoleDivergence nu rho := by
  have hdiff : HasSum (fun c => rho c - nu c) 0 := by
    simpa using hrhoMass.sub hnuMass
  have hle :
      ∑' c, -(nu c * Real.log (nu c / rho c)) ≤ ∑' c, (rho c - nu c) :=
    Summable.tsum_le_tsum (fun c => neg_divergence_term_le nu rho hnu0 hrho0 c)
      hsum.neg hdiff.summable
  rw [hdiff.tsum_eq, tsum_neg] at hle
  simpa [countableRoleDivergence] using hle

/-- **Gibbs at countable probability support.** The mass-one specialization of
`countableRoleDivergence_nonneg_of_equal_mass`. -/
theorem countableRoleDivergence_nonneg {C : Type} (nu rho : C → Real)
    (hnu0 : ∀ c, 0 ≤ nu c) (hrho0 : ∀ c, 0 < rho c)
    (hnu1 : HasSum nu 1) (hrho1 : HasSum rho 1)
    (hsum : Summable (fun c => nu c * Real.log (nu c / rho c))) :
    0 ≤ countableRoleDivergence nu rho :=
  countableRoleDivergence_nonneg_of_equal_mass nu rho 1 hnu0 hrho0 hnu1 hrho1 hsum

/-- The divergence vanishes at the reference law itself, with no positivity hypothesis.  At a
zero coordinate the totalized summand is zero; at a nonzero coordinate the ratio is one. -/
theorem countableRoleDivergence_self {C : Type} (rho : C → Real) :
    countableRoleDivergence rho rho = 0 := by
  unfold countableRoleDivergence
  have hzero : ∀ c : C, rho c * Real.log (rho c / rho c) = 0 := by
    intro c
    by_cases h : rho c = 0
    · simp [h]
    · rw [div_self h]
      simp
  simp only [hzero]
  exact tsum_zero

/-- For a finite probability law, divergence from the uniform law equals the finite role gap and vanishes exactly at the uniform law. -/
theorem countable_recovers_finite_role_exchange {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (nu : C → Real) (hnu0 : ∀ c, 0 ≤ nu c) (hnu1 : ∑ c, nu c = 1) :
    countableRoleDivergence nu (uniformMass C) = klFromUniform nu
      ∧ (countableRoleDivergence nu (uniformMass C) = 0 ↔ nu = uniformMass C) := by
  refine ⟨countableRoleDivergence_uniform nu, ?_⟩
  rw [countableRoleDivergence_uniform nu]
  exact klFromUniform_eq_zero_iff_uniform nu hnu0 hnu1

end OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
