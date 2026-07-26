import Mathlib

set_option autoImplicit false

/-!
# Illustrative Refusal-Certificate Cost Fixture

## Formal Scope

The displayed rational values form a dimensionless illustrative fixture. Units, empirical calibration, and an operational event-to-cost adapter are outside the declarations.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative

structure RefusalCertificateCost where
  generation : ℚ
  reading : ℚ
  verification : ℚ
  storage : ℚ
  deriving DecidableEq, Repr

def refusalCertificateTotalCost (C : RefusalCertificateCost) : ℚ :=
  C.generation + C.reading + C.verification + C.storage

def RefusalCostNonnegative (C : RefusalCertificateCost) : Prop :=
  0 <= C.generation ∧ 0 <= C.reading ∧ 0 <= C.verification ∧ 0 <= C.storage

theorem refusalCertificateTotalCost_nonneg
    (C : RefusalCertificateCost) (h : RefusalCostNonnegative C) :
    0 <= refusalCertificateTotalCost C := by
  unfold refusalCertificateTotalCost
  linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

def canonicalRefusalCost : RefusalCertificateCost where
  generation := 2
  reading := 1
  verification := 3
  storage := 1

theorem canonicalRefusalCost_total :
    refusalCertificateTotalCost canonicalRefusalCost = 7
      ∧ RefusalCostNonnegative canonicalRefusalCost := by
  norm_num [refusalCertificateTotalCost, RefusalCostNonnegative,
    canonicalRefusalCost]

#print axioms refusalCertificateTotalCost_nonneg
#print axioms canonicalRefusalCost_total

end OperatorKO7.Meta.DistinctionBoundary.Quantitative
