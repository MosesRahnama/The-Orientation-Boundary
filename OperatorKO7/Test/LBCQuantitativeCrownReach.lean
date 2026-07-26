import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7ExactProfile
import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.ScalarPolicyFirewall

/-!
# LBC quantitative declaration and axiom-surface audit

This file checks that the named structural, semantic, accounting, and scalar-policy declarations
remain importable and prints the axioms of their theorem declarations.
-/

set_option autoImplicit false

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism
open OperatorKO7.Meta.LicensedBoundaryCalculus.KO7DistinctionAdapter

#check @structuralProfile
#check @structural_composition_universal
#check @semanticProfile
#check @semanticProfile_eq_computed
#check @guardedRate_eq_none_iff
#check no_unique_total_rate_extension
#check @structuralHartleyCollapse?_eq_none_iff
#check raw_semanticProfile_exact
#check licensed_semanticProfile_exact
#check ko7_profile_drop_exact
#check @countEvents_append
#check @AdditiveValuation.evaluate_add
#check monotone_nonzero_scalar_policies_disagree
#check no_policy_independent_scalar_on_mixed_fixture

#print axioms structural_composition_universal
#print axioms semanticProfile_eq_computed
#print axioms guardedRate_eq_none_iff
#print axioms no_unique_total_rate_extension
#print axioms structuralHartleyCollapse?_eq_none_iff
#print axioms raw_semanticProfile_exact
#print axioms licensed_semanticProfile_exact
#print axioms ko7_profile_drop_exact
#print axioms countEvents_append
#print axioms AdditiveValuation.evaluate_add
#print axioms monotone_nonzero_scalar_policies_disagree
#print axioms no_policy_independent_scalar_on_mixed_fixture
