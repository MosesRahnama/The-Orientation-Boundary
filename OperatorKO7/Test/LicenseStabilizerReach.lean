import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! Paired reach and axiom gate for observer-relative license stabilizers. -/

set_option autoImplicit false

namespace OperatorKO7.Test.LicenseStabilizerReach

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

#check @licenseStabilizer
#check @mem_licenseStabilizer_iff
#check @observerSwap
#check @swap_mem_licenseStabilizer_of_eq
#check @licensed_iff_stabilizer_invariant
#check @same_fiber_iff_stabilizer_orbit
#check @observerRefines_iff_licenseStabilizer_le
#check @same_kernel_iff_licenseStabilizer_eq
#check @licenseStabilizer_eq_bot_iff_injective
#check @observerRefines_strict_iff_licenseStabilizer_lt
#check @ObserverFiber
#check @rangeFiberEquiv
#check @licenseStabilizerDomEquiv
#check @licenseStabilizerFiberMulEquiv
#check @natCard_licenseStabilizer_eq_prod_factorial
#check @PointedBit
#check @pointedAutomorphismGroup
#check @pointedBitConstantObserver
#check @pointedAutomorphisms_le_observerStabilizer
#check @pointedBitSwap_mem_observerStabilizer
#check @pointedBitSwap_not_mem_pointedAutomorphismGroup
#check @pointedAutomorphismGroup_lt_observerStabilizer
#check @license_stabilizer_complete

#print axioms licenseStabilizer
#print axioms mem_licenseStabilizer_iff
#print axioms observerSwap
#print axioms swap_mem_licenseStabilizer_of_eq
#print axioms licensed_iff_stabilizer_invariant
#print axioms same_fiber_iff_stabilizer_orbit
#print axioms observerRefines_iff_licenseStabilizer_le
#print axioms same_kernel_iff_licenseStabilizer_eq
#print axioms licenseStabilizer_eq_bot_iff_injective
#print axioms observerRefines_strict_iff_licenseStabilizer_lt
#print axioms ObserverFiber
#print axioms rangeFiberEquiv
#print axioms licenseStabilizerDomEquiv
#print axioms licenseStabilizerFiberMulEquiv
#print axioms natCard_licenseStabilizer_eq_prod_factorial
#print axioms PointedBit
#print axioms pointedAutomorphismGroup
#print axioms pointedBitConstantObserver
#print axioms pointedAutomorphisms_le_observerStabilizer
#print axioms pointedBitSwap_mem_observerStabilizer
#print axioms pointedBitSwap_not_mem_pointedAutomorphismGroup
#print axioms pointedAutomorphismGroup_lt_observerStabilizer
#print axioms license_stabilizer_complete

end OperatorKO7.Test.LicenseStabilizerReach
