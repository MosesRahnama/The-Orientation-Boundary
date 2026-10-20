import OperatorKO7.Meta.Recursor.SignatureDerivabilitySharpness

/-! Paired reach and axiom gate for SignatureDerivabilitySharpness. -/

set_option autoImplicit false

namespace OperatorKO7.Test.SignatureDerivabilitySharpnessReach

open OperatorKO7.Meta.Recursor.SignatureDerivabilitySharpness

#check @RecTerm
#check @RecAlgebra
#check @fold
#check @witnessLeft
#check @witnessRight
#check @witnessPair_distinct
#check @constantThirdArgument_identifies_witnessPair
#check @counterHeightAlgebra
#check @counterHeightAlgebra_separates_witnessPair
#check @counterHeightAlgebra_reads_third_argument
#check @signature_nonDerivability_is_relative_to_the_constant_class

#print axioms witnessPair_distinct
#print axioms constantThirdArgument_identifies_witnessPair
#print axioms counterHeightAlgebra_separates_witnessPair
#print axioms counterHeightAlgebra_reads_third_argument
#print axioms signature_nonDerivability_is_relative_to_the_constant_class

end OperatorKO7.Test.SignatureDerivabilitySharpnessReach
