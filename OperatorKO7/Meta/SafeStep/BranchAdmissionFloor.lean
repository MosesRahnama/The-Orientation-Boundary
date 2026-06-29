import Mathlib

/-!
# Public branch-admission floor

This module factors the signature-neutral arithmetic part of
`BranchDecisionFloor.lean` into a public-safe confluence-axis surface. It omits
the Helstrom and quantum-discrimination readings carried by the reviewer-NDA
module and keeps only the finite licensed-branch admission floor:

* a licensed decision with confidence at least `tau` has error at most `1 - tau`;
* the same bound holds for finite weighted cohorts;
* the conditional weighted mean has the same bound under positive total weight;
* the bound is tight on a one-element cohort.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.BranchAdmissionFloor

theorem licensed_error_le {tau confidence : ℝ} (h : tau ≤ confidence) :
    1 - confidence ≤ 1 - tau := by
  linarith

theorem licensed_cohort_error_le {Omega : Type} (cohort : Finset Omega)
    (conf weight : Omega -> ℝ) (tau : ℝ)
    (hw : ∀ omega ∈ cohort, 0 ≤ weight omega)
    (hlic : ∀ omega ∈ cohort, tau ≤ conf omega) :
    (∑ omega ∈ cohort, weight omega * (1 - conf omega))
      ≤ (1 - tau) * ∑ omega ∈ cohort, weight omega := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  nlinarith [hw omega homega, licensed_error_le (hlic omega homega)]

theorem licensed_cohort_mean_error_le {Omega : Type} (cohort : Finset Omega)
    (conf weight : Omega -> ℝ) (tau : ℝ)
    (hw : ∀ omega ∈ cohort, 0 ≤ weight omega)
    (hpos : 0 < ∑ omega ∈ cohort, weight omega)
    (hlic : ∀ omega ∈ cohort, tau ≤ conf omega) :
    (∑ omega ∈ cohort, weight omega * (1 - conf omega))
        / (∑ omega ∈ cohort, weight omega)
      ≤ 1 - tau := by
  rw [div_le_iff₀ hpos]
  exact licensed_cohort_error_le cohort conf weight tau hw hlic

theorem floor_saturated_witness (tau : ℝ) :
    (∑ _omega ∈ ({0} : Finset (Fin 1)), (1 : ℝ) * (1 - tau))
        / (∑ _omega ∈ ({0} : Finset (Fin 1)), (1 : ℝ)) = 1 - tau := by
  simp

#print axioms licensed_error_le
#print axioms licensed_cohort_error_le
#print axioms licensed_cohort_mean_error_le
#print axioms floor_saturated_witness

end OperatorKO7.Meta.SafeStep.BranchAdmissionFloor
