import OperatorKO7.Meta.MatrixResidualTaxonomy

namespace MatrixResidualTaxonomyReach

open OperatorKO7.MatrixResidualTaxonomy

#check MatrixResidualFamily
#check MatrixClosureStatus
#check matrixResidualFamilies
#check matrixResidualClosureStatus
#check matrixResidualFamilies_nodup
#check matrixResidualFamilies_length
#check matrixResidualFamilies_complete_exact
#check matrixResidualClosureStatus_catalog

#print axioms MatrixResidualFamily
#print axioms MatrixClosureStatus
#print axioms matrixResidualFamilies
#print axioms matrixResidualClosureStatus
#print axioms matrixResidualFamilies_nodup
#print axioms matrixResidualFamilies_length
#print axioms matrixResidualFamilies_complete_exact
#print axioms matrixResidualClosureStatus_catalog

example : MatrixResidualFamily.componentwiseWeakStrict ∈ matrixResidualFamilies := by
  decide

example : MatrixResidualFamily.tropicalFull ∈ matrixResidualFamilies := by
  decide

example : matrixResidualClosureStatus MatrixResidualFamily.scalarizableWeight =
    MatrixClosureStatus.reducedToExistingTheorem := by
  rfl

example : matrixResidualClosureStatus MatrixResidualFamily.unconstrainedRelation =
    MatrixClosureStatus.notYetMethodClass := by
  rfl

example : MatrixResidualFamily.importDependentMatrix ∈ matrixResidualFamilies ↔
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.componentwiseWeakStrict ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.paretoProduct ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.lexPriority ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.permutationLexPriority ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.scalarizableWeight ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.arcticFull ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.tropicalFull ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.importDependentMatrix ∨
    MatrixResidualFamily.importDependentMatrix = MatrixResidualFamily.unconstrainedRelation ∨
    MatrixResidualFamily.importDependentMatrix =
      MatrixResidualFamily.unconstrainedRelationClosed := by
  exact matrixResidualFamilies_complete_exact _

end MatrixResidualTaxonomyReach
