import OperatorKO7.Meta.Analysis.CompactUniformSeparation

set_option autoImplicit false

/-!
# Metric diagonal grade D1u

D1u is compact-uniform eventual separation from zero on every compact subset of
the stated open domain. The definition is identified with the compiled
`CompactUniformSeparation` predicate. The family `1/(n+1)` supplies the strict
pointwise-versus-uniform witness.

Relation: analytic family indexed by `Nat`.
Closure: compact subsets of the stated domain.
Strategy: not applicable.
External trust: none.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalGrade

open Filter Set Topology
open OperatorKO7.Analysis.UniformSeparation

/-- Metric grade D1u: compact-uniform eventual separation from zero. -/
def D1u (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  CompactUniformSeparation F U

/-- The metric grade is the compiled compact-uniform separation predicate. -/
theorem d1u_iff_compactUniformSeparation
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    D1u F U ↔ CompactUniformSeparation F U :=
  Iff.rfl

/-- The `1/(n+1)` family fails D1u. -/
theorem guardExpiry_not_d1u :
    ¬ D1u guardExpiryFamily Set.univ :=
  guardExpiry_not_separated

/-- Pointwise nonvanishing is strictly weaker than D1u on the compiled
`1/(n+1)` family. -/
theorem guardExpiry_pointwise_nonzero_and_not_d1u :
    (∀ n z, guardExpiryFamily n z ≠ 0) ∧
      ¬ D1u guardExpiryFamily Set.univ :=
  ⟨guardExpiry_pointwise_ne_zero, guardExpiry_not_d1u⟩

/-- D1u plus locally uniform convergence gives locally uniform convergence of
reciprocals through the existing reciprocal theorem. -/
theorem d1u_reciprocal_transport
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hsep : D1u F U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    TendstoLocallyUniformlyOn
      (fun n z => (F n z)⁻¹) (fun z => (f z)⁻¹) atTop U :=
  reciprocal_tendstoLocallyUniformlyOn hU hsep hlim

#check @D1u
#check @d1u_iff_compactUniformSeparation
#check @guardExpiry_not_d1u
#check @guardExpiry_pointwise_nonzero_and_not_d1u
#check @d1u_reciprocal_transport

#print axioms D1u
#print axioms d1u_iff_compactUniformSeparation
#print axioms guardExpiry_not_d1u
#print axioms guardExpiry_pointwise_nonzero_and_not_d1u
#print axioms d1u_reciprocal_transport

end OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalGrade
