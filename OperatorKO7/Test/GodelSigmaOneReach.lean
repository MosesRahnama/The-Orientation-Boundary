import OperatorKO7.Meta.DistinctionBoundary.GodelSigmaOne

namespace OperatorKO7.Test.GodelSigmaOneReach

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

#check @weakEvalTerm
#print axioms weakEvalTerm
#check @weakEq
#print axioms weakEq
#check @weakEvalForm
#print axioms weakEvalForm
#check @weakEval_existsF
#print axioms weakEval_existsF
#check @weakEval_andF
#print axioms weakEval_andF
#check @weakEval_orF
#print axioms weakEval_orF
#check @weakEvalTerm_subst
#print axioms weakEvalTerm_subst
#check @isClosedTerm_weakEvalTerm_indep
#print axioms isClosedTerm_weakEvalTerm_indep
#check @weakEvalForm_env_eq
#print axioms weakEvalForm_env_eq
#check @weakEvalForm_subst_closed
#print axioms weakEvalForm_subst_closed
#check @weakEvalForm_subst_selfSucc
#print axioms weakEvalForm_subst_selfSucc
#check @weak_q1
#print axioms weak_q1
#check @weak_q2
#print axioms weak_q2
#check @weak_q3
#print axioms weak_q3
#check @weak_q4
#print axioms weak_q4
#check @weak_q5
#print axioms weak_q5
#check @weak_q6
#print axioms weak_q6
#check @weak_q7
#print axioms weak_q7
#check @weakEval_isQAxiom
#print axioms weakEval_isQAxiom
#check @weakEval_isAxiom
#print axioms weakEval_isAxiom
#check @weakEval_inductionAxiom
#print axioms weakEval_inductionAxiom
#check @weakEval_isAxiomI
#print axioms weakEval_isAxiomI
#check @checkI_weak_sound
#print axioms checkI_weak_sound
#check @provableI_weak_sound
#print axioms provableI_weak_sound
#check @IsSigma1
#print axioms IsSigma1
#check @sigmaOneCounterexample
#print axioms sigmaOneCounterexample
#check @sigmaOneCounterexample_isSigma1
#print axioms sigmaOneCounterexample_isSigma1
#check @sigmaOneCounterexample_sentence
#print axioms sigmaOneCounterexample_sentence
#check @sigmaOneCounterexample_true
#print axioms sigmaOneCounterexample_true
#check @sigmaOneCounterexample_weak_false
#print axioms sigmaOneCounterexample_weak_false
#check @sigmaOneCounterexample_not_provableI
#print axioms sigmaOneCounterexample_not_provableI
#check @Sigma1Completeness
#print axioms Sigma1Completeness
#check @sigma1_complete_impossible
#print axioms sigma1_complete_impossible
#check @SigmaOneRouteKill
#print axioms SigmaOneRouteKill
#check @sigmaOne_route_killed
#print axioms sigmaOne_route_killed
#check @IsSigma1.bounded
#print axioms IsSigma1.bounded
#check @IsSigma1.and
#print axioms IsSigma1.and
#check @IsSigma1.or
#print axioms IsSigma1.or
#check @IsSigma1.exists
#print axioms IsSigma1.exists
#check @IsSigma1.boundedExists
#print axioms IsSigma1.boundedExists
#check @IsSigma1.boundedAll
#print axioms IsSigma1.boundedAll
#check @SigmaOneRouteKill.mk
#print axioms SigmaOneRouteKill.mk
#check @SigmaOneRouteKill.standardTrue
#print axioms SigmaOneRouteKill.standardTrue
#check @SigmaOneRouteKill.sigmaOne
#print axioms SigmaOneRouteKill.sigmaOne
#check @SigmaOneRouteKill.closed
#print axioms SigmaOneRouteKill.closed
#check @SigmaOneRouteKill.notDerivable
#print axioms SigmaOneRouteKill.notDerivable
#check @SigmaOneRouteKill.externalCompletenessImpossible
#print axioms SigmaOneRouteKill.externalCompletenessImpossible

end OperatorKO7.Test.GodelSigmaOneReach
