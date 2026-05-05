import OperatorKO7.Meta.MatrixResidualTaxonomy
import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema

namespace OperatorKO7.MatrixOrderInterfaces

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixResidualTaxonomy

/-- Theorem-visible interface for a componentwise weak order with one designated strict
coordinate. -/
structure ComponentwiseWeakStrictOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  tracked : Fin d
  weak_all : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i
  strict_tracked : ∀ {u v : MatrixVec d}, rel u v → u tracked < v tracked

def ComponentwiseWeakStrictOrder.family {d : Nat}
    (_ : ComponentwiseWeakStrictOrder d) : MatrixResidualFamily :=
  .componentwiseWeakStrict

/-- Theorem-visible interface for finite Pareto/product orders. -/
structure ParetoProductOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  weak_all : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i
  some_strict : ∀ {u v : MatrixVec d}, rel u v → ∃ i : Fin d, u i < v i

def ParetoProductOrder.family {d : Nat}
    (_ : ParetoProductOrder d) : MatrixResidualFamily :=
  .paretoProduct

/-- Theorem-visible interface for lex-priority orders whose primary tracked coordinate is
explicit. -/
structure LexPriorityOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  priority : List (Fin d)
  priority_nodup : priority.Nodup
  trackedPrimary : Fin d
  trackedPrimary_mem : trackedPrimary ∈ priority
  trackedPrimary_head : priority.head? = some trackedPrimary
  weak_all : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i
  strict_trackedPrimary : ∀ {u v : MatrixVec d}, rel u v → u trackedPrimary < v trackedPrimary

def LexPriorityOrder.family {d : Nat}
    (_ : LexPriorityOrder d) : MatrixResidualFamily :=
  .lexPriority

/-- Theorem-visible interface for lex orders whose priority list is a full permutation of the
available coordinates. -/
structure PermutationLexPriorityOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  priority : List (Fin d)
  priority_nodup : priority.Nodup
  priority_complete : ∀ i : Fin d, i ∈ priority
  trackedPrimary : Fin d
  trackedPrimary_head : priority.head? = some trackedPrimary
  weak_all : ∀ {u v : MatrixVec d}, rel u v → ∀ i : Fin d, u i ≤ v i
  strict_trackedPrimary : ∀ {u v : MatrixVec d}, rel u v → u trackedPrimary < v trackedPrimary

def PermutationLexPriorityOrder.family {d : Nat}
    (_ : PermutationLexPriorityOrder d) : MatrixResidualFamily :=
  .permutationLexPriority

/-- Scalarizable matrix orders are the exact subfamily already reducible to the existing
scalar-dominance theorem. -/
structure ScalarizableMatrixOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  weight : MatrixVec d
  dominance : MatrixScalarDominance weight rel

def ScalarizableMatrixOrder.family {d : Nat}
    (_ : ScalarizableMatrixOrder d) : MatrixResidualFamily :=
  .scalarizableWeight

/-- Imported matrix orders are classified only through their external witness/certificate
dependency. -/
inductive MatrixImportLicense
  | externalCertificate
  | globalWeightSearch
  | semiringEmbedding
  | oracleWitness
  deriving DecidableEq, Repr

structure ImportDependentMatrixOrder (d : Nat) where
  rel : MatrixVec d → MatrixVec d → Prop
  license : MatrixImportLicense
  importedWitness : Type
  importedWitness_nonempty : Nonempty importedWitness

def ImportDependentMatrixOrder.family {d : Nat}
    (_ : ImportDependentMatrixOrder d) : MatrixResidualFamily :=
  .importDependentMatrix

/-- Theorem-visible projection/scalarization payload for the componentwise weak-strict
matrix family. -/
abbrev ComponentwiseWeakStrictProjectionPayload : Prop :=
  ∀ {d : Nat} (O : ComponentwiseWeakStrictOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem componentwiseWeakStrict_projection_payload :
    ComponentwiseWeakStrictProjectionPayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.weak_all h)

/-- Theorem-visible projection/scalarization payload for finite Pareto/product orders. -/
abbrev ParetoProductProjectionPayload : Prop :=
  ∀ {d : Nat} (O : ParetoProductOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem paretoProduct_projection_payload : ParetoProductProjectionPayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.weak_all h)

/-- Theorem-visible projection/scalarization payload for lex-priority orders. -/
abbrev LexPriorityProjectionPayload : Prop :=
  ∀ {d : Nat} (O : LexPriorityOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem lexPriority_projection_payload : LexPriorityProjectionPayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.weak_all h)

/-- Theorem-visible projection/scalarization payload for permutation lex-priority orders. -/
abbrev PermutationLexPriorityProjectionPayload : Prop :=
  ∀ {d : Nat} (O : PermutationLexPriorityOrder d) (weight : MatrixVec d),
    MatrixScalarDominance weight O.rel

theorem permutationLexPriority_projection_payload :
    PermutationLexPriorityProjectionPayload := by
  intro d O weight
  refine ⟨?_⟩
  intro u v h
  exact matrixScalarize_le_of_pointwise_le weight u v (O.weak_all h)

/-- The scalarizable-weight family already carries the exact scalar-dominance certificate
needed by the arbitrary-matrix barrier. -/
abbrev ScalarizableWeightReductionPayload : Prop :=
  ∀ {d : Nat} (O : ScalarizableMatrixOrder d),
    MatrixScalarDominance O.weight O.rel

theorem scalarizableWeight_reduction_payload :
    ScalarizableWeightReductionPayload := by
  intro d O
  exact O.dominance

theorem componentwise_strict_has_strict_coordinate
    {d : Nat} (O : ComponentwiseWeakStrictOrder d)
    {u v : MatrixVec d} (h : O.rel u v) :
    ∃ i : Fin d, u i < v i := by
  exact ⟨O.tracked, O.strict_tracked h⟩

theorem pareto_product_has_strict_coordinate
    {d : Nat} (O : ParetoProductOrder d)
    {u v : MatrixVec d} (h : O.rel u v) :
    ∃ i : Fin d, u i < v i := by
  exact O.some_strict h

theorem scalarizable_order_yields_scalar_dominance
    {d : Nat} (O : ScalarizableMatrixOrder d)
    {u v : MatrixVec d} (h : O.rel u v) :
    matrixScalarize O.weight u ≤ matrixScalarize O.weight v := by
  exact O.dominance.nonstrict h

theorem lex_priority_exposes_tracked_primary
    {d : Nat} (O : LexPriorityOrder d)
    {u v : MatrixVec d} (h : O.rel u v) :
    O.priority.head? = some O.trackedPrimary ∧ u O.trackedPrimary < v O.trackedPrimary := by
  exact ⟨O.trackedPrimary_head, O.strict_trackedPrimary h⟩

theorem permutation_lex_priority_exposes_tracked_primary
    {d : Nat} (O : PermutationLexPriorityOrder d)
    {u v : MatrixVec d} (h : O.rel u v) :
    O.priority.head? = some O.trackedPrimary ∧ u O.trackedPrimary < v O.trackedPrimary := by
  exact ⟨O.trackedPrimary_head, O.strict_trackedPrimary h⟩

theorem import_dependent_matrix_is_licensed_escape
    {d : Nat} (O : ImportDependentMatrixOrder d) :
    matrixResidualClosureStatus O.family = MatrixClosureStatus.licensedEscape := by
  rfl

/-- Theorem-visible licensed-escape payload for imported matrix orders. -/
abbrev ImportDependentMatrixLicensedEscapePayload : Prop :=
  ∀ {d : Nat} (O : ImportDependentMatrixOrder d),
    matrixResidualClosureStatus O.family = MatrixClosureStatus.licensedEscape

theorem importDependentMatrix_licensedEscape_payload :
    ImportDependentMatrixLicensedEscapePayload := by
  intro d O
  exact import_dependent_matrix_is_licensed_escape O

theorem unconstrained_relation_not_method_class :
    matrixResidualClosureStatus MatrixResidualFamily.unconstrainedRelation =
      MatrixClosureStatus.notYetMethodClass := by
  rfl

/-- Theorem-visible explicit-open payload for the unconstrained residual row. -/
abbrev UnconstrainedRelationNotYetMethodClassPayload : Prop :=
  matrixResidualClosureStatus MatrixResidualFamily.unconstrainedRelation =
    MatrixClosureStatus.notYetMethodClass

theorem unconstrainedRelation_notYetMethodClass_payload :
    UnconstrainedRelationNotYetMethodClassPayload :=
  unconstrained_relation_not_method_class

end OperatorKO7.MatrixOrderInterfaces
