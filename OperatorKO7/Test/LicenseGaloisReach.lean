import OperatorKO7.Meta.OperationalInexpressibility.LicenseGalois

/-! Paired reach and axiom gate for the license Galois connection. -/

set_option autoImplicit false

namespace OperatorKO7.Test.LicenseGaloisReach

open OperatorKO7.Meta.OperationalInexpressibility.LicenseGalois

#check @licensedBy
#check @kerFamily
#check @kerFamily_rel_iff
#check @mem_licensedBy_iff
#check @setoid_le_kerFamily_iff
#check @licenseFamily_galoisConnection
#check @licensedBy_antitone
#check @kerFamily_antitone
#check @kerFamily_singleton
#check @setoid_le_targetKernel_iff
#check @setoidClassIndicator
#check @setoidClassIndicator_licensed
#check @setoidClassIndicator_separates
#check @kerFamily_licensedBy_eq
#check @licenseClosure
#check @subset_licenseClosure
#check @licenseClosure_mono
#check @licenseClosure_idempotent
#check @licenseClosure_eq_self_iff
#check @licensedBy_injective
#check @setoid_le_iff_licensedBy_reverse_inclusion
#check @licensedBy_strict_of_setoid_lt
#check @kerFamily_observer_licenseTheory_eq_kernel
#check @same_kernel_iff_same_boolean_license_family
#check @bool_license_families_are_distinct
#check @license_galois_complete

#print axioms licensedBy
#print axioms kerFamily
#print axioms kerFamily_rel_iff
#print axioms mem_licensedBy_iff
#print axioms setoid_le_kerFamily_iff
#print axioms licenseFamily_galoisConnection
#print axioms licensedBy_antitone
#print axioms kerFamily_antitone
#print axioms kerFamily_singleton
#print axioms setoid_le_targetKernel_iff
#print axioms setoidClassIndicator
#print axioms setoidClassIndicator_licensed
#print axioms setoidClassIndicator_separates
#print axioms kerFamily_licensedBy_eq
#print axioms licenseClosure
#print axioms subset_licenseClosure
#print axioms licenseClosure_mono
#print axioms licenseClosure_idempotent
#print axioms licenseClosure_eq_self_iff
#print axioms licensedBy_injective
#print axioms setoid_le_iff_licensedBy_reverse_inclusion
#print axioms licensedBy_strict_of_setoid_lt
#print axioms kerFamily_observer_licenseTheory_eq_kernel
#print axioms same_kernel_iff_same_boolean_license_family
#print axioms bool_license_families_are_distinct
#print axioms license_galois_complete

end OperatorKO7.Test.LicenseGaloisReach
