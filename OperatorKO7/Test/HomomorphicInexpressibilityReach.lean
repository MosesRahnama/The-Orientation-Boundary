import OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility

/-! Paired reach and axiom gate for HomomorphicInexpressibility. -/

set_option autoImplicit false

namespace OperatorKO7.Test.HomomorphicInexpressibilityReach

open OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility

#check @FinitarySignature
#check @FinitaryAlgebra
#check @AlgebraHom
#check @FreeTerm
#check @FreeTerm.eval
#check @FreeTerm.bind
#check @FreeTerm.substitutionComposition
#check @FreeTerm.bind_bind
#check @FreeTerm.eval_bind
#check @FreeTerm.eval_natural
#check @BinaryVar
#check @binaryVal
#check @TermDefinesBinaryPredicate
#check @HomomorphicPredicateObstruction
#check @ProjectionFactorsThrough
#check @projection_not_factorsThrough_of_hom_collapse
#check @predicate_not_termDefinable_of_hom_collapse
#check @HomomorphicPredicateObstruction.not_termDefinable
#check @disequality_not_termDefinable_of_hom_collapse

#print axioms FreeTerm.bind_bind
#print axioms FreeTerm.eval_bind
#print axioms FreeTerm.eval_natural
#print axioms projection_not_factorsThrough_of_hom_collapse
#print axioms predicate_not_termDefinable_of_hom_collapse
#print axioms HomomorphicPredicateObstruction.not_termDefinable
#print axioms disequality_not_termDefinable_of_hom_collapse

end OperatorKO7.Test.HomomorphicInexpressibilityReach
