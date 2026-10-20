import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Order
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# The role exchange at countable support

The Distinction finite-role-exchange theorem is stated for a finite role alphabet and a finite
terminal support, where the residual gap is `log₂|C| − H(ν)`, the divergence of the role law from
the uniform law. At countable support there is no `|C|`, so the uniform reference is not available
and the residual has to be stated against a chosen reference law. That is what this module does.

`countableRoleDivergence ν ρ` is the divergence of the role law `ν` from the reference law `ρ`,
written as a `tsum` so it makes sense on any index type. Three theorems carry the finite result
across:

* `countableRoleDivergence_fintype` is the finite reduction: on a `Fintype` the `tsum` is the
  finite sum, definitionally the same object the finite theorem uses.
* `countableRoleDivergence_uniform` is the recovery: against the uniform reference on a finite
  alphabet the countable divergence is exactly `klFromUniform`, the quantity the finite role-gap
  theorem computes. The finite theorem is therefore the countable one at a particular reference,
  and not an analogy.
* `countableRoleDivergence_nonneg` is Gibbs at countable support: the divergence is nonnegative
  whenever both laws are summable to one, the reference is strictly positive, and the divergence
  series itself converges.

The summability hypothesis on the divergence series is load-bearing and not decoration: on a
countable alphabet the series can diverge, and no rearrangement makes it converge. It is stated,
not hidden.

Relation: the role channel of the overproduction gap. Closure: root.
External trust: none. Mathlib only.
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

/-- **The recovery.** Against the uniform reference on a finite alphabet the countable divergence
is exactly the finite one the role-gap theorem computes. -/
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

/-- **The finite theorem is the countable one at the uniform reference.** Both halves are stated
together so the recovery is checked and not asserted: on a finite alphabet the countable divergence
against the uniform law is the finite role gap, and it vanishes exactly at the uniform law. -/
theorem countable_recovers_finite_role_exchange {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (nu : C → Real) (hnu0 : ∀ c, 0 ≤ nu c) (hnu1 : ∑ c, nu c = 1) :
    countableRoleDivergence nu (uniformMass C) = klFromUniform nu
      ∧ (countableRoleDivergence nu (uniformMass C) = 0 ↔ nu = uniformMass C) := by
  refine ⟨countableRoleDivergence_uniform nu, ?_⟩
  rw [countableRoleDivergence_uniform nu]
  exact klFromUniform_eq_zero_iff_uniform nu hnu0 hnu1

end OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange
