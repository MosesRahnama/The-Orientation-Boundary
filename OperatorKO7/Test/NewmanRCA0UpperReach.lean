import OperatorKO7.Meta.ReverseMath.NewmanRCA0Upper

/-! Paired reach and axiom gate for NewmanRCA0Upper. -/

set_option autoImplicit false

namespace OperatorKO7.Test.NewmanRCA0UpperReach

open OperatorKO7.ReverseMath

#check @stdModel_newmanSentence
#check @stdModel_models_rca0BasicAxioms_and_newman
#check @rca0Basic_consistent_with_newman

#print axioms stdModel_newmanSentence
#print axioms stdModel_models_rca0BasicAxioms_and_newman
#print axioms rca0Basic_consistent_with_newman

end OperatorKO7.Test.NewmanRCA0UpperReach
