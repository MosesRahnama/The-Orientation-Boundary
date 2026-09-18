import OperatorKO7.Meta.MatrixOrderInterfaces

namespace MatrixOrderInterfacesReach

open OperatorKO7.MatrixOrderInterfaces
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

def tracked0 : Fin 1 := ⟨0, by decide⟩

def compOrder : ComponentwiseWeakStrictOrder 1 where
  rel := VecLeLt tracked0
  tracked := tracked0
  weak_all := by
    intro u v h i
    exact h.1 i
  strict_tracked := by
    intro u v h
    exact h.2

def paretoOrder : ParetoProductOrder 1 where
  rel := fun u v => (∀ i : Fin 1, u i ≤ v i) ∧ ∃ i : Fin 1, u i < v i
  weak_all := by
    intro u v h i
    exact h.1 i
  some_strict := by
    intro u v h
    exact h.2

def lexOrder : LexPriorityOrder 1 where
  rel := VecLeLt tracked0
  priority := [tracked0]
  priority_nodup := by
    decide
  trackedPrimary := tracked0
  trackedPrimary_mem := by
    simp [tracked0]
  trackedPrimary_head := by
    rfl
  weak_all := by
    intro u v h i
    exact h.1 i
  strict_trackedPrimary := by
    intro u v h
    exact h.2

def permLexOrder : PermutationLexPriorityOrder 1 where
  rel := VecLeLt tracked0
  priority := [tracked0]
  priority_nodup := by
    decide
  priority_complete := by
    intro i
    simpa [Subsingleton.elim i tracked0]
  trackedPrimary := tracked0
  trackedPrimary_head := by
    rfl
  weak_all := by
    intro u v h i
    exact h.1 i
  strict_trackedPrimary := by
    intro u v h
    exact h.2

def scalarOrder : ScalarizableMatrixOrder 1 where
  rel := VecLt
  weight := fun _ => 1
  dominance := MatrixScalarDominance.of_pointwise_lt (weight := fun _ => 1)

def importOrder : ImportDependentMatrixOrder 1 where
  rel := fun _ _ => True
  license := MatrixImportLicense.externalCertificate
  importedWitness := Unit
  importedWitness_nonempty := ⟨()⟩

#check ComponentwiseWeakStrictOrder
#check ParetoProductOrder
#check LexPriorityOrder
#check PermutationLexPriorityOrder
#check ScalarizableMatrixOrder
#check ImportDependentMatrixOrder
#check componentwise_strict_has_strict_coordinate
#check pareto_product_has_strict_coordinate
#check scalarizable_order_yields_scalar_dominance
#check lex_priority_exposes_tracked_primary
#check permutation_lex_priority_exposes_tracked_primary
#check ComponentwiseWeakStrictProjectionPayload
#check ParetoProductProjectionPayload
#check LexPriorityProjectionPayload
#check PermutationLexPriorityProjectionPayload
#check ScalarizableWeightReductionPayload
#check import_dependent_matrix_is_licensed_escape
#check ImportDependentMatrixLicensedEscapePayload
#check unconstrained_relation_not_method_class
#check UnconstrainedRelationNotYetMethodClassPayload

example (u v : MatrixVec 1) (h : compOrder.rel u v) :
    ∃ i : Fin 1, u i < v i := by
  exact componentwise_strict_has_strict_coordinate compOrder h

example (u v : MatrixVec 1) (h : paretoOrder.rel u v) :
    ∃ i : Fin 1, u i < v i := by
  exact pareto_product_has_strict_coordinate paretoOrder h

example (u v : MatrixVec 1) (h : scalarOrder.rel u v) :
    matrixScalarize scalarOrder.weight u ≤ matrixScalarize scalarOrder.weight v := by
  exact scalarizable_order_yields_scalar_dominance scalarOrder h

example (u v : MatrixVec 1) (h : lexOrder.rel u v) :
    lexOrder.priority.head? = some lexOrder.trackedPrimary ∧
      u lexOrder.trackedPrimary < v lexOrder.trackedPrimary := by
  exact lex_priority_exposes_tracked_primary lexOrder h

example (u v : MatrixVec 1) (h : permLexOrder.rel u v) :
    permLexOrder.priority.head? = some permLexOrder.trackedPrimary ∧
      u permLexOrder.trackedPrimary < v permLexOrder.trackedPrimary := by
  exact permutation_lex_priority_exposes_tracked_primary permLexOrder h

example : matrixResidualClosureStatus importOrder.family = MatrixClosureStatus.licensedEscape := by
  exact import_dependent_matrix_is_licensed_escape importOrder

example : matrixResidualClosureStatus MatrixResidualFamily.unconstrainedRelation =
    MatrixClosureStatus.notYetMethodClass := by
  exact unconstrained_relation_not_method_class

example (u v : MatrixVec 1) (h : compOrder.rel u v) :
    matrixScalarize (fun _ => 1) u ≤ matrixScalarize (fun _ => 1) v := by
  exact (componentwiseWeakStrict_projection_payload compOrder (fun _ => 1)).nonstrict h

example (u v : MatrixVec 1) (h : paretoOrder.rel u v) :
    matrixScalarize (fun _ => 1) u ≤ matrixScalarize (fun _ => 1) v := by
  exact (paretoProduct_projection_payload paretoOrder (fun _ => 1)).nonstrict h

example (u v : MatrixVec 1) (h : lexOrder.rel u v) :
    matrixScalarize (fun _ => 1) u ≤ matrixScalarize (fun _ => 1) v := by
  exact (lexPriority_projection_payload lexOrder (fun _ => 1)).nonstrict h

example : ImportDependentMatrixLicensedEscapePayload := by
  exact importDependentMatrix_licensedEscape_payload

example : UnconstrainedRelationNotYetMethodClassPayload := by
  exact unconstrainedRelation_notYetMethodClass_payload

end MatrixOrderInterfacesReach
