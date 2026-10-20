import OperatorKO7.Meta.UniqueNormalization.CertificateFamilyInstances

/-!
# Reach and axiom check for `Meta/UniqueNormalization/CertificateFamilyInstances.lean`

Pins every public declaration, structure constructor, field and parent projection, and
inductive constructor of the paired module, each with a paired axiom query, followed by the
package controls. Baseline axioms only. -/

#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.nonOmegaOverlapping_append
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.nonOmegaOverlapping_append
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.rhsDetermined_append
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.rhsDetermined_append
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.modelRefutesOverlaps_append
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.modelRefutesOverlaps_append
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.AppHeadsIn
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.AppHeadsIn
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.RootHeadIn
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.RootHeadIn
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.not_omega_of_heads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.not_omega_of_heads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.no_instance_of_heads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.no_instance_of_heads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.appHeadsIn_of_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.appHeadsIn_of_cases
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule1
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule1
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule2
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule2
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_trs_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_trs_eq
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule2_subterm_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45Rule2_subterm_cases
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_lhs_not_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_lhs_not_omegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_lhs_not_omegaUnifiable_symm
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_lhs_not_omegaUnifiable_symm
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_nonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_class_and_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_class_and_UNconv
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleZ
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleZ
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_rules
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_rules
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rules
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rules
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleP_mem_family
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleP_mem_family
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_subset_family
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_subset_family
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_nonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_nonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleZ_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleZ_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_varCondition
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_varCondition
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_step_zTower
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_step_zTower
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower_size
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower_size
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zTower_injective
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_infinite_reduction
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_infinite_reduction
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.RuleDuplicates
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.RuleDuplicates
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.flatMap_replicate_var
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.flatMap_replicate_var
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_rhs_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_rhs_varOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rhs_occurrence_count
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rhs_occurrence_count
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_duplicates_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleD_duplicates_iff
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_nonlinear_and_collapsing
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_nonlinear_and_collapsing
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.mk
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.toSplitRay
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.toSplitRay
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.prev_base
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.prev_base
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.top
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.top
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.next_top
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.next_top
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.prev_top
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.prev_top
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.lastOr
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.lastOr
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.lastOr_append_singleton
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.lastOr_append_singleton
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.next_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.next_injective
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_F
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_F
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_G
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_G
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_A
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_A
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_B
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_B
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_S
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_S
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_P
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_P
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_C
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_C
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_Z
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_Z
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_D
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_D
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_J
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_J
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_H_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_H_eq
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_H_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_H_ne
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.base_ne_B
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.base_ne_B
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.B_not_fixed
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.B_not_fixed
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_rulesHold
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF1
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF1
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF2
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF2
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubZ
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubZ
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubD
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubD
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.maxNatList_replicate_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.maxNatList_replicate_zero
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_f45Rule1
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_f45Rule1
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_f45Rule2
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_f45Rule2
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_f45Rule1
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_f45Rule1
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_f45Rule2
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_f45Rule2
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_rules_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_rules_eq
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_ruleD
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.ruleFreshBase_ruleD
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_ruleZ
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_ruleZ
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_ruleD
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubCRule_ruleD
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_rules_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_rules_eq
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_hub_rules_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_hub_rules_eq
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_hub_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_hub_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_hub_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.capacity_hub_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF2_subterm_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.hubF2_subterm_cases
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.f45_hub_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_appHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_appHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_rootHeads
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.zd_hub_rootHeads
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.familyRay_refutes_F_overlap
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.familyRay_refutes_F_overlap
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes_f45
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes_f45
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes_zd
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes_zd
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.interp_refutes
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.optionRay
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.optionRay
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_countable_interp
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_countable_interp
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_countable_values
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_countable_values
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_rulesHold
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_model_refutes
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_model_refutes
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_UNconv
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.shiftEmbedding
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.shiftEmbedding
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.not_mem_shift
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.not_mem_shift
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.ofEmbedding
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.FamilyRay.ofEmbedding
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_certificate_of_familyRay
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_certificate_of_familyRay
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_splitRay_of_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_splitRay_of_certificate
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_embedding
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_embedding
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_certificate_iff_infinite
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_certificate_iff_infinite
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_minimal_carrier
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_minimal_carrier
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_no_finite_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_no_finite_certificate
#check @OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_unit_rulesHold
#print axioms OperatorKO7.Meta.UniqueNormalization.CertificateFamily.family_unit_rulesHold

open OperatorKO7.Meta.Rewriting OperatorKO7.Meta.UniqueNormalization OperatorKO7.Meta.UniqueNormalization.CertificateCapacity OperatorKO7.Meta.UniqueNormalization.CertificateFamily

/-! Controls: uniqueness and a countable certificate at sample duplication counts, finite
carriers refuted although finite rule models exist, the duplication count at `r = 0` and `r = 1`,
and the F45 class membership. -/

example : UNconv (family_rules 3) := family_UNconv 3

example : HasCertificate (family_rules 2) (Option Nat) := (family_minimal_carrier.{0} 2).1

example : ¬ HasCertificate (family_rules 0) Bool := family_no_finite_certificate 0

example : unitInterp.RulesHold (family_rules 5) := family_unit_rulesHold 5

example : RuleDuplicates (ruleD 1) := (ruleD_duplicates_iff 1).2 Nat.one_pos

example : ¬ RuleDuplicates (ruleD 0) := fun h => Nat.lt_irrefl 0 ((ruleD_duplicates_iff 0).1 h)

example : NonOmegaOverlapping F45Certificate.trs := f45_nonOmegaOverlapping

example : family_countable_interp.op 9 [] = none := family_countable_values.2.2.2
