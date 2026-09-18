import OperatorKO7.Meta.SafeTrace_CertificateAudit

namespace SafeTraceCertificateAuditReach

open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateAudit
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open MetaSN_KO7

#check SafeTraceCertificateAuditRow
#check safeTraceCertificateAuditRows
#check SafeTraceExternalizedRecoveryEvidence
#check SafeTraceCertificateAuditRowEvidence
#check safeTraceCertificateAuditRows_length
#check safeTraceCertificateAuditRows_nodup
#check safeTraceCertificateAuditRows_mem_iff
#check safeTraceCertificateAuditRows_complete
#check safeTraceCertificateAudit_row_projects_evidence
#check SafeTraceCertificateAuditCatalog
#check safe_trace_certificate_audit_catalog
#check safeTraceCertificateAudit_catalog_projects_evidence

example : safeTraceCertificateAuditRows.length = 8 :=
  safeTraceCertificateAuditRows_length

example : safeTraceCertificateAuditRows.Nodup :=
  safeTraceCertificateAuditRows_nodup

example (row : SafeTraceCertificateAuditRow) :
    row ∈ safeTraceCertificateAuditRows :=
  safeTraceCertificateAuditRows_complete row

example : SafeTraceCertificateAuditCatalog :=
  safe_trace_certificate_audit_catalog

example (row : SafeTraceCertificateAuditRow) :
    SafeTraceCertificateAuditRowEvidence row :=
  safeTraceCertificateAudit_catalog_projects_evidence
    safe_trace_certificate_audit_catalog row

end SafeTraceCertificateAuditReach
