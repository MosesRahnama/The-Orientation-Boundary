import OperatorKO7.Meta.DistinctionBoundary.GodelAccCodeSelfNumbering

namespace OperatorKO7.Test.GodelAccCodeSelfNumberingReach
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial

#check @encodeAcc
#print axioms encodeAcc
#check @decodeAcc?
#print axioms decodeAcc?
#check @decodeAcc?_encode
#print axioms decodeAcc?_encode
#check @encodeAcc_injective
#print axioms encodeAcc_injective
#check @smnAcc
#print axioms smnAcc
#check @smnAcc_spec
#print axioms smnAcc_spec
#check @AccCodeSMN
#print axioms AccCodeSMN
#check @AccCodeSMN.mk
#print axioms AccCodeSMN.mk
#check @AccCodeSMN.compiler
#print axioms AccCodeSMN.compiler
#check @AccCodeSMN.spec
#print axioms AccCodeSMN.spec
#check @accCode_smn
#print axioms accCode_smn
#check @IsUniversalAccWith
#print axioms IsUniversalAccWith
#check @apply_tracks_quote
#print axioms apply_tracks_quote
#check @consVoid_outputs_obstruct_partialCode
#print axioms consVoid_outputs_obstruct_partialCode
#check @apply_not_universalAcc
#print axioms apply_not_universalAcc
#check @AccCodeSelfNumberingRoute
#print axioms AccCodeSelfNumberingRoute
#check @AccCodeSelfNumberingRoute.mk
#print axioms AccCodeSelfNumberingRoute.mk
#check @AccCodeSelfNumberingRoute.decoderCorrect
#print axioms AccCodeSelfNumberingRoute.decoderCorrect
#check @AccCodeSelfNumberingRoute.universalApply
#print axioms AccCodeSelfNumberingRoute.universalApply
#check @AccCodeSelfNumberingRoute.smn
#print axioms AccCodeSelfNumberingRoute.smn
#check @accCodeSelfNumberingRoute_impossible
#print axioms accCodeSelfNumberingRoute_impossible
#check @AccCodeSelfNumberingDisposition
#print axioms AccCodeSelfNumberingDisposition
#check @AccCodeSelfNumberingDisposition.mk
#print axioms AccCodeSelfNumberingDisposition.mk
#check @AccCodeSelfNumberingDisposition.faithfulCode
#print axioms AccCodeSelfNumberingDisposition.faithfulCode
#check @AccCodeSelfNumberingDisposition.injectiveCode
#print axioms AccCodeSelfNumberingDisposition.injectiveCode
#check @AccCodeSelfNumberingDisposition.arbitrarySMN
#print axioms AccCodeSelfNumberingDisposition.arbitrarySMN
#check @AccCodeSelfNumberingDisposition.applyUniversalImpossible
#print axioms AccCodeSelfNumberingDisposition.applyUniversalImpossible
#check @AccCodeSelfNumberingDisposition.declaredRouteImpossible
#print axioms AccCodeSelfNumberingDisposition.declaredRouteImpossible
#check @accCode_self_numbering_disposition
#print axioms accCode_self_numbering_disposition

end OperatorKO7.Test.GodelAccCodeSelfNumberingReach
