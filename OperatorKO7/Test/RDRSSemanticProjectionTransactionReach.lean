import OperatorKO7.Meta.RDRSSemanticProjectionTransaction

/-!
# RDRS Semantic Projection Transaction Reach Test

Audit reach file for S4. Keeps `#check` and `#print axioms` commands out
of the production module while preserving the Lean safety-bible theorem
inspection surface. Every public declaration of the module, the structure
constructors and projections included, has a paired `#check @` and
`#print axioms`.
-/

set_option autoImplicit false

open OperatorKO7.RDRSSemanticProjectionTransaction

#check @SemanticProjectionTransaction
#print axioms SemanticProjectionTransaction
#check @SemanticProjectionTransaction.mk
#print axioms SemanticProjectionTransaction.mk
#check @SemanticProjectionTransaction.T'
#print axioms SemanticProjectionTransaction.T'
#check @SemanticProjectionTransaction.pi
#print axioms SemanticProjectionTransaction.pi
#check @SemanticProjectionTransaction.Rproj
#print axioms SemanticProjectionTransaction.Rproj
#check @SemanticProjectionTransaction.pi_commutes_lhs
#print axioms SemanticProjectionTransaction.pi_commutes_lhs
#check @SemanticProjectionTransaction.pi_commutes_rhs
#print axioms SemanticProjectionTransaction.pi_commutes_rhs
#check @SemanticProjectionTransaction.semanticMeasure
#print axioms SemanticProjectionTransaction.semanticMeasure
#check @SemanticProjectionTransactionEscape
#print axioms SemanticProjectionTransactionEscape
#check @SemanticProjectionTransactionEscape.mk
#print axioms SemanticProjectionTransactionEscape.mk
#check @SemanticProjectionTransactionEscape.transaction
#print axioms SemanticProjectionTransactionEscape.transaction
#check @SemanticProjectionTransactionEscape.projected_orientation
#print axioms SemanticProjectionTransactionEscape.projected_orientation
#check @SemanticProjectionTransactionEscape.liftedMeasure
#print axioms SemanticProjectionTransactionEscape.liftedMeasure
#check @SemanticProjectionTransactionEscape.lifted_orients
#print axioms SemanticProjectionTransactionEscape.lifted_orients
#check @factorsThroughSeedCollapse_of_identity
#print axioms factorsThroughSeedCollapse_of_identity
#check @semanticProjectionTransactionEscape_of_commuting_projection
#print axioms semanticProjectionTransactionEscape_of_commuting_projection
#check @semanticProjectionTransactionEscape_nonempty_iff
#print axioms semanticProjectionTransactionEscape_nonempty_iff
#check @semantic_projection_escape_requires_sigma
#print axioms semantic_projection_escape_requires_sigma
#check @semantic_projection_escape_requires_seed_collapse
#print axioms semantic_projection_escape_requires_seed_collapse
#check @semantic_projection_escape_requires_projected_orientation
#print axioms semantic_projection_escape_requires_projected_orientation
#check @semantic_projection_escape_requires_wellFounded
#print axioms semantic_projection_escape_requires_wellFounded
#check @trivialNatStep
#print axioms trivialNatStep
#check @natSemanticMeasure
#print axioms natSemanticMeasure
#check @trivialSemanticTransaction
#print axioms trivialSemanticTransaction
#check @trivialSemanticTransactionEscape
#print axioms trivialSemanticTransactionEscape
#check @SemanticProjectionTransaction_nonempty
#print axioms SemanticProjectionTransaction_nonempty
#check @SemanticProjectionTransactionEscape_nonempty
#print axioms SemanticProjectionTransactionEscape_nonempty
#check @rdrs_semantic_projection_transaction_anchor
#print axioms rdrs_semantic_projection_transaction_anchor
