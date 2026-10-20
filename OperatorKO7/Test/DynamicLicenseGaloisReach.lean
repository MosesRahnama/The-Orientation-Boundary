import OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois

/-! Paired reach and axiom gate for the dynamic license Galois connection. -/

set_option autoImplicit false

namespace OperatorKO7.Test.DynamicLicenseGaloisReach

open OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois

#check @RulePreserves
#check @preservedPredicates
#check @preservingRules
#check @mem_preservedPredicates_iff
#check @mem_preservingRules_iff
#check @rule_le_preservingRules_iff
#check @rulePredicate_galoisConnection
#check @preservedPredicates_antitone
#check @preservingRules_antitone
#check @ruleClosure
#check @predicateClosure
#check @subset_ruleClosure
#check @subset_predicateClosure
#check @ruleClosure_monotone
#check @predicateClosure_monotone
#check @ruleClosure_idempotent
#check @predicateClosure_idempotent
#check @invariantRepair
#check @invariantExclusion
#check @mem_invariantRepair_iff
#check @mem_invariantExclusion_iff
#check @invariantRepair_subset
#check @invariantRepair_preserves
#check @invariantRepair_greatest
#check @invariantExclusion_least
#check @familyInvariantRepair
#check @familyInvariantExclusion
#check @invariantRepair_eq_familyInvariantRepair
#check @invariantExclusion_eq_familyInvariantExclusion
#check @mem_familyInvariantRepair_iff
#check @mem_familyInvariantExclusion_iff
#check @familyInvariantRepair_subset
#check @familyInvariantRepair_preserves
#check @familyInvariantRepair_greatest
#check @familyInvariantExclusion_least
#check @familyInvariantRepair_idempotent
#check @familyInvariantRepair_union_exclusion
#check @familyInvariantRepair_exclusion_disjoint
#check @invariantFamilyRepair_complete
#check @positional_confluenceRepair_universal
#check @recDOnly_not_confluent
#check @dynamic_license_galois_complete

#print axioms RulePreserves
#print axioms preservedPredicates
#print axioms preservingRules
#print axioms mem_preservedPredicates_iff
#print axioms mem_preservingRules_iff
#print axioms rule_le_preservingRules_iff
#print axioms rulePredicate_galoisConnection
#print axioms preservedPredicates_antitone
#print axioms preservingRules_antitone
#print axioms ruleClosure
#print axioms predicateClosure
#print axioms subset_ruleClosure
#print axioms subset_predicateClosure
#print axioms ruleClosure_monotone
#print axioms predicateClosure_monotone
#print axioms ruleClosure_idempotent
#print axioms predicateClosure_idempotent
#print axioms invariantRepair
#print axioms invariantExclusion
#print axioms mem_invariantRepair_iff
#print axioms mem_invariantExclusion_iff
#print axioms invariantRepair_subset
#print axioms invariantRepair_preserves
#print axioms invariantRepair_greatest
#print axioms invariantExclusion_least
#print axioms familyInvariantRepair
#print axioms familyInvariantExclusion
#print axioms invariantRepair_eq_familyInvariantRepair
#print axioms invariantExclusion_eq_familyInvariantExclusion
#print axioms mem_familyInvariantRepair_iff
#print axioms mem_familyInvariantExclusion_iff
#print axioms familyInvariantRepair_subset
#print axioms familyInvariantRepair_preserves
#print axioms familyInvariantRepair_greatest
#print axioms familyInvariantExclusion_least
#print axioms familyInvariantRepair_idempotent
#print axioms familyInvariantRepair_union_exclusion
#print axioms familyInvariantRepair_exclusion_disjoint
#print axioms invariantFamilyRepair_complete
#print axioms positional_confluenceRepair_universal
#print axioms recDOnly_not_confluent
#print axioms dynamic_license_galois_complete

end OperatorKO7.Test.DynamicLicenseGaloisReach
