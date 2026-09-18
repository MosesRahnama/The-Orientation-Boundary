import OperatorKO7.Meta.RDRSSemanticClassifier

/-! Reach/audit file for the S5 semantic classifier. -/

set_option autoImplicit false

open OperatorKO7.RDRSSemanticClassifier

#check @SemanticCertificateClass
#check @NormalizedSemanticCertificate
#check @semanticClassify
#check @semantic_classifier_total
#check @semantic_temporary_unclassified_count_is_zero
#check @semantic_payload_sensitive_blocked_sound
#check @semantic_projection_transaction_escape_sound
#check @semantic_construction_escape_outside_direct
#check @semantic_transform_escape_outside_direct
#check @semantic_not_direct_sound

#print axioms semantic_classifier_total
#print axioms semantic_temporary_unclassified_count_is_zero
#print axioms semantic_payload_sensitive_blocked_sound
#print axioms semantic_projection_transaction_escape_sound
#print axioms semantic_construction_escape_outside_direct
#print axioms semantic_transform_escape_outside_direct
#print axioms semantic_not_direct_sound
