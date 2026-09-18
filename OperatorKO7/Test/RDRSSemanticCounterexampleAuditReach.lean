import OperatorKO7.Meta.RDRSSemanticCounterexampleAudit

/-! Reach/audit file for the S6 semantic counterexample audit. -/

set_option autoImplicit false

open OperatorKO7.RDRSSemanticCounterexampleAudit

#check @SemanticAuditRow
#check @auditClassify
#check @allAuditRows
#check @audit_classify_total
#check @audit_no_temporary_unclassified
#check @audit_partition_total
#check @SemanticCounterexampleAuditClosed
#check @semantic_counterexample_audit_closed
#check @counterFirstLex_row_evidence
#check @termAlgebraRewriteClosure_row_evidence
#check @nonlinearCounterPayloadCoupling_row_evidence
#check @dpProjection_row_evidence

#print axioms audit_classify_total
#print axioms audit_no_temporary_unclassified
#print axioms allAuditRows_length
#print axioms blockedRows_length
#print axioms projectionEscapeRows_length
#print axioms constructionEscapeRows_length
#print axioms transformEscapeRows_length
#print axioms notDirectRows_length
#print axioms temporaryUnclassifiedRows_length
#print axioms audit_partition_total
#print axioms counterFirstLex_class
#print axioms dpProjection_class
#print axioms semanticLabeling_class
#print axioms semantic_counterexample_audit_closed
#print axioms counterFirstLex_row_evidence
#print axioms termAlgebraRewriteClosure_row_evidence
#print axioms nonlinearCounterPayloadCoupling_row_evidence
#print axioms dpProjection_row_evidence
