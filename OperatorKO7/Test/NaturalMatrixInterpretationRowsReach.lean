import OperatorKO7.Meta.Methods.NaturalMatrixInterpretationRows

set_option autoImplicit false

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.NaturalMatrixInterpretationRows

#check @matrixAct_mono
#print axioms matrixAct_mono

#check @matrixAct_strict
#print axioms matrixAct_strict

#check @matrixAct_strict_iff
#print axioms matrixAct_strict_iff

#check @vecAdd_strict
#print axioms vecAdd_strict

#check @vectorOrder_wellFounded
#print axioms vectorOrder_wellFounded

#check @vectorOrder_compatible
#print axioms vectorOrder_compatible

#check @vectorOrder_weak_strict
#print axioms vectorOrder_weak_strict

#check @vectorOrder_compatibility
#print axioms vectorOrder_compatibility

#check @MatrixOperation
#print axioms MatrixOperation

#check @MatrixOperation.eval
#print axioms MatrixOperation.eval

#check @MatrixOperation.weak_mono
#print axioms MatrixOperation.weak_mono

#check @MatrixOperation.strict_mono_of_weak
#print axioms MatrixOperation.strict_mono_of_weak

#check @MatrixOperation.strict_mono
#print axioms MatrixOperation.strict_mono

#check @MatrixArgument
#print axioms MatrixArgument

#check @argumentMatrix
#print axioms argumentMatrix

#check @NaturalMatrixMethod
#print axioms NaturalMatrixMethod

#check @NaturalMatrixMethod.argument_strict
#print axioms NaturalMatrixMethod.argument_strict

#check @NaturalMatrixMethod.not_orients
#print axioms NaturalMatrixMethod.not_orients

#check @TriangularMatrixMethod
#print axioms TriangularMatrixMethod

#check @TriangularMatrixMethod.not_orients
#print axioms TriangularMatrixMethod.not_orients

#check @identityMatrix
#print axioms identityMatrix

#check @identityMatrix_act
#print axioms identityMatrix_act

#check @sizeMatrixMeasure
#print axioms sizeMatrixMeasure

#check @sizeNaturalMatrixMethod
#print axioms sizeNaturalMatrixMethod

#check @sizeTriangularMatrixMethod
#print axioms sizeTriangularMatrixMethod

#check @sizeNaturalMatrixMethod_strict_witness
#print axioms sizeNaturalMatrixMethod_strict_witness

#check @natural_matrix_classes_inhabited
#print axioms natural_matrix_classes_inhabited

#check @NaturalMatrixExactRowClaim
#print axioms NaturalMatrixExactRowClaim

#check @naturalMatrix_exact_row
#print axioms naturalMatrix_exact_row

#check @TriangularMatrixExactRowClaim
#print axioms TriangularMatrixExactRowClaim

#check @triangularMatrix_exact_row
#print axioms triangularMatrix_exact_row

example : Nonempty (NaturalMatrixMethod freeSchema 1) :=
  (natural_matrix_classes_inhabited 1).1

example : Nonempty (TriangularMatrixMethod freeSchema 3) :=
  (natural_matrix_classes_inhabited 3).2.1

example : WellFounded (VecLeLt (0 : Fin 2)) := vectorOrder_wellFounded _

example : IsEmpty (Fin 0) := inferInstance
