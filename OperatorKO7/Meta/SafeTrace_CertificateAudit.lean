import OperatorKO7.Meta.SafeTrace_ComplexityBridge

/-!
# Safe-Trace Certificate Audit

This module packages the accepted safe-trace certificate surfaces into a finite
theorem-facing audit catalog. Each audit row names one certified surface, and
the catalog projects the corresponding evidence without asserting any ambient
trace surjectivity beyond the already-proved boundaries.
-/

namespace OperatorKO7.SafeTraceCertificateAudit

open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open MetaSN_KO7

/-- Finite audit rows for the safe-trace certificate and complexity surfaces. -/
inductive SafeTraceCertificateAuditRow where
  | rootEndpoint
  | contextChain
  | externalizedImageRecovery
  | realizedImageExactness
  | fullCarrierObstruction
  | contextExactDrop
  | mwCtxBound
  | fgEnvelopeBound
deriving DecidableEq

/-- Canonical finite audit list for the safe-trace certificate surfaces. -/
def safeTraceCertificateAuditRows : List SafeTraceCertificateAuditRow :=
  [ .rootEndpoint
  , .contextChain
  , .externalizedImageRecovery
  , .realizedImageExactness
  , .fullCarrierObstruction
  , .contextExactDrop
  , .mwCtxBound
  , .fgEnvelopeBound
  ]

/-- The externalized-image recovery audit row carries all recovery/equality/order/bound facts. -/
def SafeTraceExternalizedRecoveryEvidence : Prop :=
  (∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      ∃ t : Trace,
        traceToFullTripleLexCarrier t = (externalizedTraceImageToRealizableCarrier X x).1) ∧
    (∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier},
      (externalizedTraceImageRealization X).code x =
          (externalizedTraceImageRealization X).code y ↔
        externalizedTraceImageToRealizableCarrier X x =
          externalizedTraceImageToRealizableCarrier X y) ∧
    (∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier),
      (externalizedTraceImageRealization X).order x y ↔
        traceRealizableCarrierRealization.order
          (externalizedTraceImageToRealizableCarrier X x)
          (externalizedTraceImageToRealizableCarrier X y)) ∧
    (∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      traceRealizableCarrierRealization.code
          (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound)

/-- Evidence carried by each finite audit row. -/
def SafeTraceCertificateAuditRowEvidence : SafeTraceCertificateAuditRow → Prop
  | .rootEndpoint =>
    ∀ {a b : Trace}, SafeStep a b → Nonempty (SafeStepEndpointComplexityPackage a b)
  | .contextChain =>
    ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u → Nonempty (SafeStepCtxComplexityPackage n t u)
  | .externalizedImageRecovery =>
      SafeTraceExternalizedRecoveryEvidence
  | .realizedImageExactness =>
      TraceRealizableCarrierExactnessPackage
  | .fullCarrierObstruction =>
      ¬ Function.Surjective traceToFullTripleLexCarrier
  | .contextExactDrop =>
      ∀ {n : Nat} {t u : Trace} (_ : SafeStepCtxPow n t u),
        OperatorKO7.OrdinalHierarchy.ExactControlledPow
          (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
          (ctxExactNote u).1 (ctxFuel t - ctxFuel u)
  | .mwCtxBound =>
      ∀ {n : Nat} {t u : Trace} (_ : SafeStepCtxPow n t u), n ≤ mwCtxBound t
  | .fgEnvelopeBound =>
      ∀ {n : Nat} {t u : Trace} (_ : SafeStepCtxPow n t u),
        n ≤ fgOmegaEnvelope (termSize t)

/-- The finite audit list has the expected eight rows. -/
@[simp] theorem safeTraceCertificateAuditRows_length :
    safeTraceCertificateAuditRows.length = 8 := by
  rfl

/-- The finite audit list has no duplicate rows. -/
theorem safeTraceCertificateAuditRows_nodup :
    safeTraceCertificateAuditRows.Nodup := by
  simp [safeTraceCertificateAuditRows]

/-- Membership in the audit list is exactly membership in the finite eight-row partition. -/
theorem safeTraceCertificateAuditRows_mem_iff (row : SafeTraceCertificateAuditRow) :
    row ∈ safeTraceCertificateAuditRows ↔
      row = .rootEndpoint ∨
      row = .contextChain ∨
      row = .externalizedImageRecovery ∨
      row = .realizedImageExactness ∨
      row = .fullCarrierObstruction ∨
      row = .contextExactDrop ∨
      row = .mwCtxBound ∨
      row = .fgEnvelopeBound := by
  cases row <;> simp [safeTraceCertificateAuditRows]

/-- Every finite audit row appears in the canonical audit list. -/
theorem safeTraceCertificateAuditRows_complete :
    ∀ row : SafeTraceCertificateAuditRow, row ∈ safeTraceCertificateAuditRows := by
  intro row
  cases row <;> simp [safeTraceCertificateAuditRows]

/-- Every row in the finite audit list projects the corresponding theorem-backed evidence. -/
def safeTraceCertificateAudit_row_projects_evidence :
    ∀ row : SafeTraceCertificateAuditRow,
      row ∈ safeTraceCertificateAuditRows → SafeTraceCertificateAuditRowEvidence row := by
  intro row _
  cases row with
  | rootEndpoint =>
      exact fun _ => ⟨safeStepEndpointComplexityPackage ‹_›⟩
  | contextChain =>
      exact fun _ => ⟨safeStepCtxComplexityPackage ‹_›⟩
  | externalizedImageRecovery =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro K X x
        exact externalizedTraceImageToRealizableCarrier_realizes X x
      · intro K X x y
        exact externalizedTraceImageRecovery_code_eq_iff_realizable_eq X
      · intro K X x y
        exact externalizedTraceImageRecovery_order_iff_realizable_order X x y
      · intro K X x
        exact externalizedTraceImageRecovery_upper_bound X x
  | realizedImageExactness =>
      exact traceRealizableCarrierExactnessPackage
  | fullCarrierObstruction =>
      exact traceToFullTripleLexCarrier_not_surjective
  | contextExactDrop =>
      exact fun {n} {t} {u} h =>
        safeStepCtxComplexityPackage_exact_drop (safeStepCtxComplexityPackage h)
  | mwCtxBound =>
      exact fun {n} {t} {u} h =>
        safeStepCtxComplexityPackage_length_le_mwCtxBound (safeStepCtxComplexityPackage h)
  | fgEnvelopeBound =>
      exact fun {n} {t} {u} h =>
        safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope (safeStepCtxComplexityPackage h)

/-- The finite safe-trace certificate audit catalog. -/
structure SafeTraceCertificateAuditCatalog where
  complete : ∀ row : SafeTraceCertificateAuditRow, row ∈ safeTraceCertificateAuditRows
  projectsEvidence :
    ∀ row : SafeTraceCertificateAuditRow,
      row ∈ safeTraceCertificateAuditRows → SafeTraceCertificateAuditRowEvidence row

/-- Canonical theorem-backed audit catalog for the safe-trace certificate surfaces. -/
def safe_trace_certificate_audit_catalog : SafeTraceCertificateAuditCatalog where
  complete := safeTraceCertificateAuditRows_complete
  projectsEvidence := safeTraceCertificateAudit_row_projects_evidence

/-- Any row in the canonical audit catalog projects the corresponding theorem-backed evidence. -/
def safeTraceCertificateAudit_catalog_projects_evidence
    (hCat : SafeTraceCertificateAuditCatalog) (row : SafeTraceCertificateAuditRow) :
    SafeTraceCertificateAuditRowEvidence row :=
  hCat.projectsEvidence row (hCat.complete row)

end OperatorKO7.SafeTraceCertificateAudit
