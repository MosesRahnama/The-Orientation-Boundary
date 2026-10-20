import OperatorKO7.Meta.ConstructionRouteCatalog

namespace ConstructionRouteCatalogReach

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog

#check CanonicalConstructionWitness
#check canonicalWitnessRoute
#check canonicalWitnessW1ImportClass?
#check canonicalWitnessW2TransformClass?
#check canonical_w1_route_catalog
#check canonical_w2_route_catalog
#check canonical_construction_route_catalog
#check canonical_witness_route_not_w0
#check fullDuplicating_canonical_route_tags_are_non_w0
#check fullDuplicating_w1_w2_both_separate_from_direct_search

example : canonicalWitnessRoute .w1ImportedWhole ≠ .W0 := by
  exact canonical_witness_route_not_w0 .w1ImportedWhole

example : canonicalWitnessRoute .w2FullDuplicating ≠ .W0 := by
  exact fullDuplicating_canonical_route_tags_are_non_w0.2

end ConstructionRouteCatalogReach
