import OperatorKO7.Meta.LicensedBoundaryCalculus.GuardFreezeGrammar

set_option autoImplicit false

open OperatorKO7.Meta.LicensedBoundaryCalculus

#check @GuardGrammar
#check @GuardGrammar.deny
#check @GuardGrammar.allow
#check @GuardGrammar.disequality
#check @GuardGrammar.meet
#check @GuardGrammar.join
#check @interpretGuard
#check @interpretGuard_meet
#check @interpretGuard_join
#check @disequality_guard_exact_safeStepGuard
#check @EqualityStatusInvariant
#check @interpretGuard_equalityStatusInvariant
#check @leftVoidGuard
#check @leftVoidGuard_not_equalityStatusInvariant
#check @guardGrammar_not_semantically_complete
#check @FreezeAtom
#check @FreezeAtom.void
#check @FreezeAtom.delta
#check @FreezeAtom.integrate
#check @FreezeAtom.merge
#check @FreezeAtom.appL
#check @FreezeAtom.appR
#check @FreezeAtom.recD
#check @FreezeAtom.eqW
#check @freezeAtomPosition
#check @interpretFreezeAtom
#check @freezeAtom_complete
#check @FreezePolicyGrammar
#check @FreezePolicyGrammar.empty
#check @FreezePolicyGrammar.atom
#check @FreezePolicyGrammar.union
#check @FreezePolicyGrammar.inter
#check @FreezePolicyGrammar.writeClose
#check @FreezePolicyGrammar.repair
#check @interpretFreezePolicy
#check @interpretFreezePolicy_union
#check @interpretFreezePolicy_inter
#check @interpretFreezePolicy_writeClose
#check @interpretFreezePolicy_repair
#check @freezePolicy_writeClose_closed
#check @freezePolicy_repair_confluent
#check @selectedAtom
#check @interpret_selectedAtom
#check @compileFreezePolicy
#check @freezePolicy_semantic_complete
#check @recDPolicy
#check @recDPolicy_exact
#check @repairedRecDPolicy_confluent

#print axioms GuardGrammar
#print axioms GuardGrammar.deny
#print axioms GuardGrammar.allow
#print axioms GuardGrammar.disequality
#print axioms GuardGrammar.meet
#print axioms GuardGrammar.join
#print axioms interpretGuard
#print axioms interpretGuard_meet
#print axioms interpretGuard_join
#print axioms disequality_guard_exact_safeStepGuard
#print axioms EqualityStatusInvariant
#print axioms interpretGuard_equalityStatusInvariant
#print axioms leftVoidGuard
#print axioms leftVoidGuard_not_equalityStatusInvariant
#print axioms guardGrammar_not_semantically_complete
#print axioms FreezeAtom
#print axioms FreezeAtom.void
#print axioms FreezeAtom.delta
#print axioms FreezeAtom.integrate
#print axioms FreezeAtom.merge
#print axioms FreezeAtom.appL
#print axioms FreezeAtom.appR
#print axioms FreezeAtom.recD
#print axioms FreezeAtom.eqW
#print axioms freezeAtomPosition
#print axioms interpretFreezeAtom
#print axioms freezeAtom_complete
#print axioms FreezePolicyGrammar
#print axioms FreezePolicyGrammar.empty
#print axioms FreezePolicyGrammar.atom
#print axioms FreezePolicyGrammar.union
#print axioms FreezePolicyGrammar.inter
#print axioms FreezePolicyGrammar.writeClose
#print axioms FreezePolicyGrammar.repair
#print axioms interpretFreezePolicy
#print axioms interpretFreezePolicy_union
#print axioms interpretFreezePolicy_inter
#print axioms interpretFreezePolicy_writeClose
#print axioms interpretFreezePolicy_repair
#print axioms freezePolicy_writeClose_closed
#print axioms freezePolicy_repair_confluent
#print axioms selectedAtom
#print axioms interpret_selectedAtom
#print axioms compileFreezePolicy
#print axioms freezePolicy_semantic_complete
#print axioms recDPolicy
#print axioms recDPolicy_exact
#print axioms repairedRecDPolicy_confluent
