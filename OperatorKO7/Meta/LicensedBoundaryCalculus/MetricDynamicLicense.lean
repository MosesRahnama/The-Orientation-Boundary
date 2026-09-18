import OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalGrade

set_option autoImplicit false

/-!
# Metric persistent licensing adapter

The analytic fiber already has the substantive theorem: metric grade `D1u` is
exactly `CompactUniformSeparation`, the guard-expiry family is pointwise
nonvanishing while failing that license, and the license transports reciprocal
local-uniform convergence.

This module does not reprove those facts. It exposes them as the metric
persistent-license computation rule of Licensed Boundary Calculus.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.MetricDynamicLicense

open Filter Set Topology
open OperatorKO7.Analysis.UniformSeparation
open OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalGrade

/-- LBC's metric persistent license is the already-compiled dynamic grade D1u. -/
abbrev MetricPersistentLicense (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  D1u F U

/-- Exact analytic computation rule: the metric persistent license is compact-
uniform separation from zero. -/
theorem metricPersistentLicense_iff_compactUniformSeparation
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    MetricPersistentLicense F U ↔ CompactUniformSeparation F U :=
  d1u_iff_compactUniformSeparation F U

/-- Negative computation rule: pointwise nonvanishing does not manufacture the
metric persistent license. -/
theorem guardExpiry_pointwise_nonzero_but_unlicensed :
    (∀ n z, guardExpiryFamily n z ≠ 0) ∧
      ¬ MetricPersistentLicense guardExpiryFamily Set.univ :=
  guardExpiry_pointwise_nonzero_and_not_d1u

/-- Completion/transport rule for the analytic fiber: once the metric license
and local-uniform convergence are both present, reciprocals converge locally
uniformly as well. -/
theorem metricPersistentLicense_reciprocal_transport
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hlicense : MetricPersistentLicense F U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    TendstoLocallyUniformlyOn
      (fun n z => (F n z)⁻¹) (fun z => (f z)⁻¹) atTop U :=
  d1u_reciprocal_transport hU hlicense hlim

#check MetricPersistentLicense
#check metricPersistentLicense_iff_compactUniformSeparation
#check guardExpiry_pointwise_nonzero_but_unlicensed
#check metricPersistentLicense_reciprocal_transport
#print axioms metricPersistentLicense_iff_compactUniformSeparation
#print axioms guardExpiry_pointwise_nonzero_but_unlicensed
#print axioms metricPersistentLicense_reciprocal_transport

end OperatorKO7.Meta.LicensedBoundaryCalculus.MetricDynamicLicense
