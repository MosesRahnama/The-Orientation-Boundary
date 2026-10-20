import OperatorKO7.Meta.UniqueNormalization.Section7GuardedClosure

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @OnGuard
#check @forall₂_onGuard_elim
#check @SigmaClosedOn.onGuard_sigmaClosed
#check @SigmaClosedOn.eq_of_CT
#check @TermTargetedPGraph.eqvOn_of_CT_of_complete

#print axioms OnGuard
#print axioms forall₂_onGuard_elim
#print axioms SigmaClosedOn.onGuard_sigmaClosed
#print axioms SigmaClosedOn.eq_of_CT
#print axioms TermTargetedPGraph.eqvOn_of_CT_of_complete
