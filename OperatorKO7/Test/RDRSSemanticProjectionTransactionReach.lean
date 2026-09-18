import OperatorKO7.Meta.RDRSSemanticProjectionTransaction

/-!
# RDRS Semantic Projection Transaction Reach Test

Audit reach file for S4. Keeps `#check` and `#print axioms` commands out
of the production module while preserving the Lean safety-bible theorem
inspection surface.
-/

set_option autoImplicit false

open OperatorKO7.RDRSSemanticProjectionTransaction

#check @SemanticProjectionTransaction
#check @SemanticProjectionTransactionEscape
#check @semantic_projection_escape_requires_sigma
#check @semantic_projection_escape_requires_seed_collapse
#check @semantic_projection_escape_requires_projected_orientation
#check @semantic_projection_escape_requires_wellFounded
#check @SemanticProjectionTransactionEscape.liftedMeasure
#check @SemanticProjectionTransactionEscape.lifted_orients
#check @SemanticProjectionTransaction_nonempty
#check @SemanticProjectionTransactionEscape_nonempty

#print axioms semantic_projection_escape_requires_sigma
#print axioms semantic_projection_escape_requires_seed_collapse
#print axioms semantic_projection_escape_requires_projected_orientation
#print axioms semantic_projection_escape_requires_wellFounded
#print axioms SemanticProjectionTransactionEscape.lifted_orients
#print axioms SemanticProjectionTransaction_nonempty
#print axioms SemanticProjectionTransactionEscape_nonempty
