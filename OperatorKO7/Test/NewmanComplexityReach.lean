import OperatorKO7.Meta.ReverseMath.NewmanComplexity

/-! Paired reach and axiom gate for NewmanComplexity. -/

set_option autoImplicit false

namespace OperatorKO7.Test.NewmanComplexityReach

open OperatorKO7.ReverseMath

#check @IsArithmetical
#check @IsArithmetical.not
#check @IsArithmetical.inf
#check @IsArithmetical.sup
#check @newmanConclusion
#check @newmanInductiveStep
#check @newmanBody
#check @newmanSentence
#check @IsSetGuardedArithmetical
#check @IsPi11Set
#check @newmanConclusion_isArithmetical
#check @newmanInductiveStep_isArithmetical
#check @newmanBody_inner_isArithmetical
#check @newmanBody_isSetGuardedArithmetical
#check @newmanSentence_isPi11
#check @cpJoinabilitySentence
#check @cpJoinability_isLow
#check @cpJoinability_isSigma0

#print axioms IsArithmetical.not
#print axioms IsArithmetical.inf
#print axioms IsArithmetical.sup
#print axioms newmanConclusion_isArithmetical
#print axioms newmanInductiveStep_isArithmetical
#print axioms newmanBody_inner_isArithmetical
#print axioms newmanBody_isSetGuardedArithmetical
#print axioms newmanSentence_isPi11
#print axioms cpJoinability_isLow
#print axioms cpJoinability_isSigma0

end OperatorKO7.Test.NewmanComplexityReach
