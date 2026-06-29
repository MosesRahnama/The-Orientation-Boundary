import OperatorKO7.Meta.DistinctionBoundary.CostDual

/-!
# Bulk-versus-boundary scaling laws

This module packages the finite scaling divergence used by the paper: the
orientation side is triangular, hence quadratic after doubling, while the
distinction side is one unit per boundary event.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.CostScalingDimension

/-- Orientation bulk charge at depth `K` and payload length `L`. -/
def orientationBulkCharge (K L : Nat) : Nat :=
  CostDual.totalCharge (CostDual.orientationChargeLaw L)
    (CostDual.orientationEvents K)

/-- Distinction boundary charge for `N` diagonal-refusal events. -/
def distinctionBoundaryCharge (N : Nat) : Nat :=
  CostDual.totalCharge CostDual.distinctionChargeLaw (List.replicate N ())

theorem orientation_bulk_quadratic_doubled (K L : Nat) :
    2 * orientationBulkCharge K L = (K + 1) * (K + 2) * L := by
  exact CostDual.orientation_two_mul_totalCharge K L

theorem distinction_boundary_linear (N : Nat) :
    distinctionBoundaryCharge N = N := by
  exact CostDual.distinction_totalCharge_eq_N N

theorem distinction_per_event_constant (N : Nat) :
    distinctionBoundaryCharge (N + 1) - distinctionBoundaryCharge N = 1 := by
  simp [distinction_boundary_linear]

/-- At any positive payload length, the bulk side is unbounded while the
distinction side remains exactly linear in event count. -/
theorem bulk_boundary_scaling_diverge (L : Nat) (hL : 1 <= L) :
    (forall M, exists K, M <= orientationBulkCharge K L)
      ∧ (forall N, distinctionBoundaryCharge N = N)
      ∧ (forall N,
        distinctionBoundaryCharge (N + 1) - distinctionBoundaryCharge N = 1) := by
  refine ⟨?_, distinction_boundary_linear, distinction_per_event_constant⟩
  intro M
  simpa [orientationBulkCharge] using CostDual.orientation_totalCharge_unbounded L hL M

#print axioms orientation_bulk_quadratic_doubled
#print axioms distinction_boundary_linear
#print axioms distinction_per_event_constant
#print axioms bulk_boundary_scaling_diverge

end OperatorKO7.Meta.DistinctionBoundary.CostScalingDimension
