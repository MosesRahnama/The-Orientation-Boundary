import OperatorKO7.Meta.ReverseMath.RCA0Derivations

/-! Full reach and axiom coverage for the `RCA0Derivations` module. Permanent. -/

#check @OperatorKO7.ReverseMath.axSuccInj
#check @OperatorKO7.ReverseMath.axAddSucc
#check @OperatorKO7.ReverseMath.axMulZero
#check @OperatorKO7.ReverseMath.axMulSucc
#check @OperatorKO7.ReverseMath.axNotLtZero
#check @OperatorKO7.ReverseMath.axLtSuccIff
#check @OperatorKO7.ReverseMath.rca0SimpsonBasic
#check @OperatorKO7.ReverseMath.numberRelativizedSimpsonArithmetic
#check @OperatorKO7.ReverseMath.IND
#check @OperatorKO7.ReverseMath.IsBoundedQ
#check @OperatorKO7.ReverseMath.IsBoundedQ.falsum
#check @OperatorKO7.ReverseMath.IsBoundedQ.equal
#check @OperatorKO7.ReverseMath.IsBoundedQ.rel
#check @OperatorKO7.ReverseMath.IsBoundedQ.imp
#check @OperatorKO7.ReverseMath.IsBoundedQ.ex_bounded
#check @OperatorKO7.ReverseMath.IsBoundedQ.not
#check @OperatorKO7.ReverseMath.IsBoundedQ.inf
#check @OperatorKO7.ReverseMath.IsBoundedQ.sup
#check @OperatorKO7.ReverseMath.IsBoundedQ.iff
#check @OperatorKO7.ReverseMath.boundedZeroOrSuccPredecessorBody
#check @OperatorKO7.ReverseMath.indFormulaZeroOrSucc
#check @OperatorKO7.ReverseMath.indFormulaLtIrrefl
#check @OperatorKO7.ReverseMath.isBoundedQ_indFormulaZeroOrSucc
#check @OperatorKO7.ReverseMath.isBoundedQ_indFormulaLtIrrefl
#check @OperatorKO7.ReverseMath.simpsonArithmetic_derives_axLtSucc
#check @OperatorKO7.ReverseMath.derivableFO_of_subtheory
#check @OperatorKO7.ReverseMath.zeroOrSuccInductionFragment
#check @OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_axLtSucc
#check @OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_axZeroOrSucc
#check @OperatorKO7.ReverseMath.axZeroOrSucc_derivable_of_contains
#check @OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_numberPredecessorDescent
#check @OperatorKO7.ReverseMath.numberPredecessorDescent_derivable_of_contains
#check @OperatorKO7.ReverseMath.numberRelativizedBoundedInductionTheory
#check @OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_subset_boundedInductionTheory
#check @OperatorKO7.ReverseMath.boundedInductionTheory_derives_numberPredecessorDescent

#print axioms OperatorKO7.ReverseMath.axSuccInj
#print axioms OperatorKO7.ReverseMath.axAddSucc
#print axioms OperatorKO7.ReverseMath.axMulZero
#print axioms OperatorKO7.ReverseMath.axMulSucc
#print axioms OperatorKO7.ReverseMath.axNotLtZero
#print axioms OperatorKO7.ReverseMath.axLtSuccIff
#print axioms OperatorKO7.ReverseMath.rca0SimpsonBasic
#print axioms OperatorKO7.ReverseMath.numberRelativizedSimpsonArithmetic
#print axioms OperatorKO7.ReverseMath.IND
#print axioms OperatorKO7.ReverseMath.IsBoundedQ
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.falsum
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.equal
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.rel
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.imp
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.ex_bounded
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.not
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.inf
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.sup
#print axioms OperatorKO7.ReverseMath.IsBoundedQ.iff
#print axioms OperatorKO7.ReverseMath.boundedZeroOrSuccPredecessorBody
#print axioms OperatorKO7.ReverseMath.indFormulaZeroOrSucc
#print axioms OperatorKO7.ReverseMath.indFormulaLtIrrefl
#print axioms OperatorKO7.ReverseMath.isBoundedQ_indFormulaZeroOrSucc
#print axioms OperatorKO7.ReverseMath.isBoundedQ_indFormulaLtIrrefl
#print axioms OperatorKO7.ReverseMath.simpsonArithmetic_derives_axLtSucc
#print axioms OperatorKO7.ReverseMath.derivableFO_of_subtheory
#print axioms OperatorKO7.ReverseMath.zeroOrSuccInductionFragment
#print axioms OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_axLtSucc
#print axioms OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_axZeroOrSucc
#print axioms OperatorKO7.ReverseMath.axZeroOrSucc_derivable_of_contains
#print axioms OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_derives_numberPredecessorDescent
#print axioms OperatorKO7.ReverseMath.numberPredecessorDescent_derivable_of_contains
#print axioms OperatorKO7.ReverseMath.numberRelativizedBoundedInductionTheory
#print axioms OperatorKO7.ReverseMath.zeroOrSuccInductionFragment_subset_boundedInductionTheory
#print axioms OperatorKO7.ReverseMath.boundedInductionTheory_derives_numberPredecessorDescent
