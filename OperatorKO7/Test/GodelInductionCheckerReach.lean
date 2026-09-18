import OperatorKO7.Meta.DistinctionBoundary.GodelInductionChecker

namespace OperatorKO7.Test.GodelInductionCheckerReach

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

#check @inductionStepTerm
#print axioms inductionStepTerm
#check @inductionAxiom
#print axioms inductionAxiom
#check @isIndAxiom
#print axioms isIndAxiom
#check @isIndAxiom_iff
#print axioms isIndAxiom_iff
#check @isAxiomI
#print axioms isAxiomI
#check @checkI
#print axioms checkI
#check @ProvableI
#print axioms ProvableI
#check @isAxiom_implies_isAxiomI
#print axioms isAxiom_implies_isAxiomI
#check @check_to_checkI
#print axioms check_to_checkI
#check @provable_to_provableI
#print axioms provable_to_provableI
#check @evalTerm_subst_selfSucc
#print axioms evalTerm_subst_selfSucc
#check @envUpdate_selfSucc_comm
#print axioms envUpdate_selfSucc_comm
#check @evalForm_subst_selfSucc
#print axioms evalForm_subst_selfSucc
#check @eval_inductionAxiom
#print axioms eval_inductionAxiom
#check @eval_isAxiomI
#print axioms eval_isAxiomI
#check @checkI_sound
#print axioms checkI_sound
#check @provableI_sound
#print axioms provableI_sound
#check @induction_checker_consistent
#print axioms induction_checker_consistent
#check @inductionAxiom_provableI
#print axioms inductionAxiom_provableI
#check @CompiledIAxiom
#print axioms CompiledIAxiom
#check @CompiledIDerives
#print axioms CompiledIDerives
#check @compiledIDerives_to_provableI
#print axioms compiledIDerives_to_provableI
#check @proofTree_checkI_to_compiledIDerives
#print axioms proofTree_checkI_to_compiledIDerives
#check @compiledIDerives_iff_provableI
#print axioms compiledIDerives_iff_provableI
#check @compiledQDerives_to_compiledIDerives
#print axioms compiledQDerives_to_compiledIDerives
#check @compiledI_all_q_axioms
#print axioms compiledI_all_q_axioms
#check @compiledI_induction
#print axioms compiledI_induction
#check @CompiledIDerives.ax
#print axioms CompiledIDerives.ax
#check @CompiledIDerives.mp
#print axioms CompiledIDerives.mp
#check @CompiledIDerives.gen
#print axioms CompiledIDerives.gen
#check @CompiledIDerives.spec
#print axioms CompiledIDerives.spec

end OperatorKO7.Test.GodelInductionCheckerReach
