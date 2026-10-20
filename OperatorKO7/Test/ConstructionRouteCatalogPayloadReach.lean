import OperatorKO7.Meta.ConstructionRouteCatalog_Payload

namespace ConstructionRouteCatalogPayloadReach

open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogPayload

#check canonicalWitnessW1Success?
#check canonicalWitnessW2Success?
#check CanonicalW1SuccessPayloadCatalog
#check CanonicalW2SuccessPayloadCatalog
#check canonical_w1_success_payload_catalog
#check canonical_w2_success_payload_catalog
#check canonical_route_payload_catalog
#check canonical_w1_payloads_have_permitted_imports
#check canonical_w2_payloads_have_permitted_transforms
#check fullDuplicating_route_payloads_separate_from_direct_search

example : canonicalWitnessW1Success? .w1MPO = some OperatorKO7.ConstructionMethodClassification.mpo_w1_success := by
  rfl

example :
    canonicalWitnessW2Success? .w2FullDuplicating =
      some OperatorKO7.TransformedCallClassification.fullDuplicating_w2_success := by
  rfl

end ConstructionRouteCatalogPayloadReach
