import OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

namespace RDRSRecursiveFamilyBoundaryReach

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

-- Force elaboration of every public declaration in the module.

#check @RecursiveFamily
#check @RecursiveFamily.base
#check @RecursiveFamily.step
#check @RecursiveFamily.mk'
#check @recursorOrbitOf
#check @UniformCostDirectMeasure
#check @UniformCostDirectMeasure.system
#check @UniformCostDirectMeasure.mu_delta
#check @UniformCostDirectMeasure.mu_rec
#check @UniformCostDirectMeasure.mu_merge
#check @IsOutsideDirectMeasureBoundary
#check @mu_recursorOrbitOf
#check @recursiveFamily_orbit_is_linear_under_uniform_cost
#check @rdrs_recursive_family_boundary_unconditional
#check @recursiveFamily_indistinguishable_from_circular_reference
#check @RecursiveFamilyBoundaryCatalog
#check @RecursiveFamilyBoundaryCatalog.families
#check @RecursiveFamilyBoundaryCatalog.boundary_witness
#check @RecursiveFamilyBoundaryCatalog.size
#check @RecursiveFamilyBoundaryCatalog.member_isOutsideBoundary
#check @emptyRecursiveFamilyBoundaryCatalog
#check @recursiveFamilyBoundaryCatalogOfList
#check @emptyRecursiveFamilyBoundaryCatalog_size
#check @recursiveFamilyBoundaryCatalogOfList_size

-- Smoke instantiations.
example : RecursiveFamily := RecursiveFamily.mk' void void
example : RecursiveFamilyBoundaryCatalog := emptyRecursiveFamilyBoundaryCatalog
example : RecursiveFamilyBoundaryCatalog :=
  recursiveFamilyBoundaryCatalogOfList [RecursiveFamily.mk' void void]

-- The unconditional foundational theorem is reachable as a value.
example : ∀ F : RecursiveFamily, IsOutsideDirectMeasureBoundary F :=
  rdrs_recursive_family_boundary_unconditional

-- The empty catalog has size 0.
example : emptyRecursiveFamilyBoundaryCatalog.size = 0 :=
  emptyRecursiveFamilyBoundaryCatalog_size

end RDRSRecursiveFamilyBoundaryReach
