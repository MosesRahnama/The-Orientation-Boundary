import OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

/-!
# Reach and axiom gate: the surgical relation and its conservative repairs

Covers every public declaration of `OperatorKO7.Meta.EqGuardedConfluence` and
of `OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair`, including the
inductive constructors and the structure projections, per the reach-and-axiom
parity rule.

`EqGuardedConfluence` carries `open Classical`, so every axiom set in that
module is printed here rather than sampled.

This file contains `#check` and `#print axioms` commands only. No `sorry`, no
`axiom`, no new declarations.
-/

namespace OperatorKO7.Test.DistinctionBoundaryConservativeRepairReach

open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.ConservativeRepair

/-! ## `Meta/EqGuardedConfluence.lean`: relation, closure, and confluence -/

#check @EqGuardedStep
#check @EqGuardedStep.R_int_delta
#check @EqGuardedStep.R_merge_void_left
#check @EqGuardedStep.R_merge_void_right
#check @EqGuardedStep.R_merge_cancel
#check @EqGuardedStep.R_rec_zero
#check @EqGuardedStep.R_rec_succ
#check @EqGuardedStep.R_eq_refl
#check @EqGuardedStep.R_eq_diff
#check @EqGuardedStepRev
#check @EqGuardedStepStar
#check @EqGuardedStepStar.refl
#check @EqGuardedStepStar.tail
#check @LocalJoinEqGuarded
#check @ConfluentEqGuarded
#check @eqgstar_trans
#check @eqgstar_destruct
#check @eqGuarded_sub_step
#check @wf_EqGuardedStepRev
#check @safeStep_sub_eqGuarded
#check @eqGuarded_not_subset_safe
#check @eqGuarded_unique_target
#check @localJoin_all_eqGuarded
#check @confluentEqGuarded

#print axioms EqGuardedStep
#print axioms EqGuardedStep.R_int_delta
#print axioms EqGuardedStep.R_merge_void_left
#print axioms EqGuardedStep.R_merge_void_right
#print axioms EqGuardedStep.R_merge_cancel
#print axioms EqGuardedStep.R_rec_zero
#print axioms EqGuardedStep.R_rec_succ
#print axioms EqGuardedStep.R_eq_refl
#print axioms EqGuardedStep.R_eq_diff
#print axioms EqGuardedStepRev
#print axioms EqGuardedStepStar
#print axioms EqGuardedStepStar.refl
#print axioms EqGuardedStepStar.tail
#print axioms LocalJoinEqGuarded
#print axioms ConfluentEqGuarded
#print axioms eqgstar_trans
#print axioms eqgstar_destruct
#print axioms eqGuarded_sub_step
#print axioms wf_EqGuardedStepRev
#print axioms safeStep_sub_eqGuarded
#print axioms eqGuarded_not_subset_safe
#print axioms eqGuarded_unique_target
#print axioms localJoin_all_eqGuarded
#print axioms confluentEqGuarded

/-! ## `ConservativeRepair.lean`, T-B: the greatest safe admission predicate -/

#check @DiagSafe
#check @OffDiagonalComplete
#check @diagSafe_le_disequality
#check @disequality_diagSafe
#check @disequality_offDiagonalComplete
#check @diagSafe_offDiagonalComplete_iff_disequality
#check @disequality_greatest_diagSafe
#check @bot_diagSafe_not_offDiagonalComplete

#print axioms DiagSafe
#print axioms OffDiagonalComplete
#print axioms diagSafe_le_disequality
#print axioms disequality_diagSafe
#print axioms disequality_offDiagonalComplete
#print axioms diagSafe_offDiagonalComplete_iff_disequality
#print axioms disequality_greatest_diagSafe
#print axioms bot_diagSafe_not_offDiagonalComplete

/-! ## T-C: the exact relation difference -/

#check @DiagonalDifferenceEdge
#check @step_and_not_eqGuarded_iff
#check @eqGuardedStep_subset_step
#check @eqGuardedStep_strict_subset_step
#check @safeStep_strict_subset_eqGuardedStep

#print axioms DiagonalDifferenceEdge
#print axioms step_and_not_eqGuarded_iff
#print axioms eqGuardedStep_subset_step
#print axioms eqGuardedStep_strict_subset_step
#print axioms safeStep_strict_subset_eqGuardedStep

/-! ## Root determinism, named -/

#check @eqGuardedStep_root_deterministic
#check @eqGuardedStep_localJoin_of_deterministic

#print axioms eqGuardedStep_root_deterministic
#print axioms eqGuardedStep_localJoin_of_deterministic

/-! ## T-D and T-ConsRepair: admissible repairs -/

#check @JoinIn
#check @AdmissibleRepair
#check @AdmissibleRepair.mk
#check @AdmissibleRepair.sub
#check @AdmissibleRepair.retainsNonDiagonal
#check @AdmissibleRepair.retainsReflexive
#check @AdmissibleRepair.localConfluent
#check @no_step_from_void
#check @no_step_from_integrate_merge_self
#check @star_eq_of_no_step
#check @admissible_refuses_diagonal_difference
#check @admissible_subset_eqGuardedStep
#check @eqGuardedStep_admissible
#check @eqGuardedStep_unique_greatest_admissible
#check @conservative_repair_forces_exact_distinction
#check @admissible_guard_is_disequality

#print axioms JoinIn
#print axioms AdmissibleRepair
#print axioms AdmissibleRepair.mk
#print axioms AdmissibleRepair.sub
#print axioms AdmissibleRepair.retainsNonDiagonal
#print axioms AdmissibleRepair.retainsReflexive
#print axioms AdmissibleRepair.localConfluent
#print axioms no_step_from_void
#print axioms no_step_from_integrate_merge_self
#print axioms star_eq_of_no_step
#print axioms admissible_refuses_diagonal_difference
#print axioms admissible_subset_eqGuardedStep
#print axioms eqGuardedStep_admissible
#print axioms eqGuardedStep_unique_greatest_admissible
#print axioms conservative_repair_forces_exact_distinction
#print axioms admissible_guard_is_disequality

/-! ## Non-vacuity and non-triviality -/

#check @admissibleRepair_nonempty
#check @step_not_admissible
#check @eqGuardedStep_strictly_above_safeStep

#print axioms admissibleRepair_nonempty
#print axioms step_not_admissible
#print axioms eqGuardedStep_strictly_above_safeStep

end OperatorKO7.Test.DistinctionBoundaryConservativeRepairReach
