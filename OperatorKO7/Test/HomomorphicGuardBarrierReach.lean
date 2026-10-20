import OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier

/-! Paired reach and axiom gate for HomomorphicGuardBarrier. -/

set_option autoImplicit false

namespace OperatorKO7.Test.HomomorphicGuardBarrierReach

open OperatorKO7.Meta.SafeStep.HomomorphicGuardBarrier

#check @KO7Op
#check @ko7Signature
#check @ko7SigmaAlgebra
#check @binaryVarSigma
#check @compileKO7Term
#check @ko7SubstitutionHom
#check @evalKO7Term_eq_evalSigma_compile
#check @ko7VariableCollapseHom
#check @ko7PositiveTruth
#check @ko7VariableCollapseHom_fixes_positiveTruth
#check @sigma_varA_ne_varB
#check @ko7VariableCollapseHom_identifies_variables
#check @ko7GuardObstruction
#check @ko7_sevenConstructor_disequality_not_termDefinable
#check @legacy_voidTest_disequality_not_sigma_expressible

#print axioms evalKO7Term_eq_evalSigma_compile
#print axioms ko7VariableCollapseHom_fixes_positiveTruth
#print axioms sigma_varA_ne_varB
#print axioms ko7VariableCollapseHom_identifies_variables
#print axioms ko7_sevenConstructor_disequality_not_termDefinable
#print axioms legacy_voidTest_disequality_not_sigma_expressible

end OperatorKO7.Test.HomomorphicGuardBarrierReach
