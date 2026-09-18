import OperatorKO7.Meta.SafeTrace_CertificateAudit

/-!
# Safe-Trace Roadmap Closeout

This module closes the M3 safe-trace roadmap on the theorem side. It packages a
finite closeout taxonomy over the already-landed image-subtype, obstruction,
bridge, complexity, and audit surfaces without asserting ambient-trace
surjectivity beyond the established boundary.
-/

namespace OperatorKO7.SafeTraceRoadmapCloseout

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.OrdinalHierarchy
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateAudit
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open NONote
open MetaSN_KO7

/-- The theorem-visible root-endpoint closeout boundary packages both certified root bounds. -/
def SafeTraceRootEndpointBoundsEvidence : Prop :=
  ∀ {a b u : Trace} {n : Nat}, SafeStep a b → SafeStepPow a n u →
    n ≤ tau a ∧ n ≤ mwRootBound a

/-- The theorem-visible contextual exact-drop closeout boundary. -/
def SafeTraceContextExactDropEvidence : Prop :=
  ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u →
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
      (ctxExactNote u).1 (ctxFuel t - ctxFuel u)

/-- The theorem-visible MW contextual bound closeout boundary. -/
def SafeTraceMWCtxBoundEvidence : Prop :=
  ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u → n ≤ mwCtxBound t

/-- The theorem-visible fast-growing contextual bound closeout boundary. -/
def SafeTraceFGEnvelopeBoundEvidence : Prop :=
  ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u →
    n ≤ fgOmegaEnvelope (termSize t)

/-- The theorem-backed M3 safe-trace surfaces intended for the root API export boundary. -/
structure SafeTraceRootAPIExportBundle where
  imageSubtypeStatus : TraceImageSubtypeStatus
  fullCarrierObstruction : ¬ Function.Surjective traceToFullTripleLexCarrier
  certificateBridgeCatalog : SafeTraceCertificateBridgeCatalog
  complexityBridgeCatalog : SafeTraceComplexityBridgeCatalog
  certificateAuditCatalog : SafeTraceCertificateAuditCatalog

/-- Canonical theorem-backed bundle for the root API export boundary. -/
def safe_trace_root_api_export_bundle : SafeTraceRootAPIExportBundle where
  imageSubtypeStatus := traceImageSubtypeStatus
  fullCarrierObstruction := traceToFullTripleLexCarrier_not_surjective
  certificateBridgeCatalog := safe_trace_certificate_bridge_catalog
  complexityBridgeCatalog := safe_trace_complexity_bridge_catalog
  certificateAuditCatalog := safe_trace_certificate_audit_catalog

/-- Finite closeout rows for the M3 safe-trace theorem package. -/
inductive SafeTraceRoadmapCloseoutRow where
  | imageSubtypeExactness
  | fullCarrierObstruction
  | certificateBridge
  | rootEndpointBounds
  | contextExactDrop
  | mwCtxBound
  | fgEnvelopeBound
  | externalizedImageRecovery
  | certificateAudit
  | rootApiExport
deriving DecidableEq

/-- Finite closeout status values for the safe-trace roadmap. -/
inductive SafeTraceRoadmapCloseoutStatus where
  | closed
deriving DecidableEq, Repr

/-- Canonical finite closeout list for the M3 safe-trace theorem package. -/
def safeTraceRoadmapCloseoutRows : List SafeTraceRoadmapCloseoutRow :=
  [ .imageSubtypeExactness
  , .fullCarrierObstruction
  , .certificateBridge
  , .rootEndpointBounds
  , .contextExactDrop
  , .mwCtxBound
  , .fgEnvelopeBound
  , .externalizedImageRecovery
  , .certificateAudit
  , .rootApiExport
  ]

/-- Theorem-evidence carried by each closeout row. -/
def SafeTraceRoadmapCloseoutRowEvidence : SafeTraceRoadmapCloseoutRow → Prop
  | .imageSubtypeExactness =>
      Nonempty TraceImageSubtypeStatus
  | .fullCarrierObstruction =>
      ¬ Function.Surjective traceToFullTripleLexCarrier
  | .certificateBridge =>
      Nonempty SafeTraceCertificateBridgeCatalog
  | .rootEndpointBounds =>
      SafeTraceRootEndpointBoundsEvidence
  | .contextExactDrop =>
      SafeTraceContextExactDropEvidence
  | .mwCtxBound =>
      SafeTraceMWCtxBoundEvidence
  | .fgEnvelopeBound =>
      SafeTraceFGEnvelopeBoundEvidence
  | .externalizedImageRecovery =>
      SafeTraceExternalizedRecoveryEvidence
  | .certificateAudit =>
      Nonempty SafeTraceCertificateAuditCatalog
  | .rootApiExport =>
      Nonempty SafeTraceRootAPIExportBundle

/-- The finite closeout list has the expected ten rows. -/
@[simp] theorem safeTraceRoadmapCloseoutRows_length :
    safeTraceRoadmapCloseoutRows.length = 10 := by
  rfl

/-- The finite closeout list has no duplicate rows. -/
theorem safeTraceRoadmapCloseoutRows_nodup :
    safeTraceRoadmapCloseoutRows.Nodup := by
  simp [safeTraceRoadmapCloseoutRows]

/-- Membership in the closeout list is exactly membership in the finite ten-row partition. -/
theorem safeTraceRoadmapCloseoutRows_mem_iff (row : SafeTraceRoadmapCloseoutRow) :
    row ∈ safeTraceRoadmapCloseoutRows ↔
      row = .imageSubtypeExactness ∨
      row = .fullCarrierObstruction ∨
      row = .certificateBridge ∨
      row = .rootEndpointBounds ∨
      row = .contextExactDrop ∨
      row = .mwCtxBound ∨
      row = .fgEnvelopeBound ∨
      row = .externalizedImageRecovery ∨
      row = .certificateAudit ∨
      row = .rootApiExport := by
  cases row <;> simp [safeTraceRoadmapCloseoutRows]

/-- Every finite closeout row appears in the canonical closeout list. -/
theorem safeTraceRoadmapCloseoutRows_complete :
    ∀ row : SafeTraceRoadmapCloseoutRow, row ∈ safeTraceRoadmapCloseoutRows := by
  intro row
  cases row <;> simp [safeTraceRoadmapCloseoutRows]

/-- Every finite closeout row is closed at the theorem boundary. -/
def safeTraceRoadmapCloseout_row_status :
    ∀ row : SafeTraceRoadmapCloseoutRow,
      row ∈ safeTraceRoadmapCloseoutRows → SafeTraceRoadmapCloseoutStatus := by
  intro row _
  cases row <;> exact .closed

/-- Every row in the finite closeout list projects the corresponding theorem-backed evidence. -/
def safeTraceRoadmapCloseout_row_projects_evidence :
    ∀ row : SafeTraceRoadmapCloseoutRow,
      row ∈ safeTraceRoadmapCloseoutRows → SafeTraceRoadmapCloseoutRowEvidence row := by
  intro row _
  cases row with
  | imageSubtypeExactness =>
      exact ⟨traceImageSubtypeStatus⟩
  | fullCarrierObstruction =>
      exact traceToFullTripleLexCarrier_not_surjective
  | certificateBridge =>
      exact ⟨safe_trace_certificate_bridge_catalog⟩
  | rootEndpointBounds =>
      intro a b u n hStep hPow
      let P := safeStepEndpointComplexityPackage hStep
      exact ⟨
        safeStepEndpointComplexityPackage_root_length_le_tau P hPow,
        safeStepEndpointComplexityPackage_root_length_le_mwRootBound P hPow
      ⟩
  | contextExactDrop =>
      intro n t u h
      exact safeStepCtxComplexityPackage_exact_drop (safeStepCtxComplexityPackage h)
  | mwCtxBound =>
      intro n t u h
      exact safeStepCtxComplexityPackage_length_le_mwCtxBound (safeStepCtxComplexityPackage h)
  | fgEnvelopeBound =>
      intro n t u h
      exact safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope (safeStepCtxComplexityPackage h)
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
  | certificateAudit =>
      exact ⟨safe_trace_certificate_audit_catalog⟩
  | rootApiExport =>
      exact ⟨safe_trace_root_api_export_bundle⟩

/-- The finite safe-trace roadmap closeout catalog. -/
structure SafeTraceRoadmapCloseoutCatalog where
  imageSubtypeStatus : TraceImageSubtypeStatus
  fullCarrierObstruction : ¬ Function.Surjective traceToFullTripleLexCarrier
  certificateBridgeCatalog : SafeTraceCertificateBridgeCatalog
  complexityBridgeCatalog : SafeTraceComplexityBridgeCatalog
  certificateAuditCatalog : SafeTraceCertificateAuditCatalog
  rootApiExport : SafeTraceRootAPIExportBundle
  complete : ∀ row : SafeTraceRoadmapCloseoutRow, row ∈ safeTraceRoadmapCloseoutRows
  rowStatus :
    ∀ row : SafeTraceRoadmapCloseoutRow,
      row ∈ safeTraceRoadmapCloseoutRows → SafeTraceRoadmapCloseoutStatus
  projectsEvidence :
    ∀ row : SafeTraceRoadmapCloseoutRow,
      row ∈ safeTraceRoadmapCloseoutRows → SafeTraceRoadmapCloseoutRowEvidence row

/-- Canonical theorem-backed closeout catalog for the M3 safe-trace roadmap. -/
def safe_trace_roadmap_closeout_catalog : SafeTraceRoadmapCloseoutCatalog where
  imageSubtypeStatus := traceImageSubtypeStatus
  fullCarrierObstruction := traceToFullTripleLexCarrier_not_surjective
  certificateBridgeCatalog := safe_trace_certificate_bridge_catalog
  complexityBridgeCatalog := safe_trace_complexity_bridge_catalog
  certificateAuditCatalog := safe_trace_certificate_audit_catalog
  rootApiExport := safe_trace_root_api_export_bundle
  complete := safeTraceRoadmapCloseoutRows_complete
  rowStatus := safeTraceRoadmapCloseout_row_status
  projectsEvidence := safeTraceRoadmapCloseout_row_projects_evidence

/-- Any row in the canonical closeout catalog is closed at the theorem boundary. -/
def safeTraceRoadmapCloseout_catalog_projects_row_status
    (hCat : SafeTraceRoadmapCloseoutCatalog) (row : SafeTraceRoadmapCloseoutRow) :
    SafeTraceRoadmapCloseoutStatus :=
  hCat.rowStatus row (hCat.complete row)

/-- Any row in the canonical closeout catalog projects the corresponding theorem-backed evidence. -/
def safeTraceRoadmapCloseout_catalog_projects_row_evidence
    (hCat : SafeTraceRoadmapCloseoutCatalog) (row : SafeTraceRoadmapCloseoutRow) :
    SafeTraceRoadmapCloseoutRowEvidence row :=
  hCat.projectsEvidence row (hCat.complete row)

/-- The closeout catalog projects the theorem-visible trace-image subtype status object. -/
def safeTraceRoadmapCloseout_catalog_projects_image_subtype_status
    (hCat : SafeTraceRoadmapCloseoutCatalog) : TraceImageSubtypeStatus :=
  hCat.imageSubtypeStatus

/-- The closeout catalog projects exactness on the realized trace-image subtype. -/
def safeTraceRoadmapCloseout_catalog_projects_image_subtype_exactness
    (hCat : SafeTraceRoadmapCloseoutCatalog) : TraceRealizableCarrierExactnessPackage :=
  hCat.imageSubtypeStatus.exactness

/-- The closeout catalog projects the full-carrier surjectivity obstruction. -/
theorem safeTraceRoadmapCloseout_catalog_projects_full_carrier_obstruction
    (hCat : SafeTraceRoadmapCloseoutCatalog) :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  hCat.fullCarrierObstruction

/-- The closeout catalog projects the theorem-facing safe-trace certificate bridge catalog. -/
def safeTraceRoadmapCloseout_catalog_projects_certificate_bridge_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceCertificateBridgeCatalog :=
  hCat.certificateBridgeCatalog

/-- The closeout catalog projects the theorem-facing safe-trace complexity bridge catalog. -/
def safeTraceRoadmapCloseout_catalog_projects_complexity_bridge_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceComplexityBridgeCatalog :=
  hCat.complexityBridgeCatalog

/-- The closeout catalog projects the certified root-endpoint bounds. -/
def safeTraceRoadmapCloseout_catalog_projects_root_endpoint_bounds
    (_hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceRootEndpointBoundsEvidence := by
  intro a b u n hStep hPow
  let P := safeStepEndpointComplexityPackage hStep
  exact ⟨
    safeStepEndpointComplexityPackage_root_length_le_tau P hPow,
    safeStepEndpointComplexityPackage_root_length_le_mwRootBound P hPow
  ⟩

/-- The closeout catalog projects exact contextual drop on safe-trace context chains. -/
def safeTraceRoadmapCloseout_catalog_projects_context_exact_drop
    (_hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceContextExactDropEvidence := by
  intro n t u h
  exact safeStepCtxComplexityPackage_exact_drop (safeStepCtxComplexityPackage h)

/-- The closeout catalog projects the MW contextual bound. -/
def safeTraceRoadmapCloseout_catalog_projects_mw_ctx_bound
    (_hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceMWCtxBoundEvidence := by
  intro n t u h
  exact safeStepCtxComplexityPackage_length_le_mwCtxBound (safeStepCtxComplexityPackage h)

/-- The closeout catalog projects the fast-growing contextual bound. -/
def safeTraceRoadmapCloseout_catalog_projects_fg_envelope_bound
    (_hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceFGEnvelopeBoundEvidence := by
  intro n t u h
  exact safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope (safeStepCtxComplexityPackage h)

/-- The closeout catalog projects externalized-image recovery back into the realized subtype. -/
def safeTraceRoadmapCloseout_catalog_projects_externalized_image_recovery
    (_hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceExternalizedRecoveryEvidence := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K X x
    exact externalizedTraceImageToRealizableCarrier_realizes X x
  · intro K X x y
    exact externalizedTraceImageRecovery_code_eq_iff_realizable_eq X
  · intro K X x y
    exact externalizedTraceImageRecovery_order_iff_realizable_order X x y
  · intro K X x
    exact externalizedTraceImageRecovery_upper_bound X x

/-- The closeout catalog projects the finite safe-trace certificate audit catalog. -/
def safeTraceRoadmapCloseout_catalog_projects_certificate_audit_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceCertificateAuditCatalog :=
  hCat.certificateAuditCatalog

/-- The closeout catalog projects the theorem-backed root API export bundle. -/
def safeTraceRoadmapCloseout_catalog_projects_root_api_export
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceRootAPIExportBundle :=
  hCat.rootApiExport

/-- The closeout catalog projects the trace-image subtype status through the root API bundle. -/
def safeTraceRoadmapCloseout_catalog_projects_root_api_image_subtype_status
    (hCat : SafeTraceRoadmapCloseoutCatalog) : TraceImageSubtypeStatus :=
  hCat.rootApiExport.imageSubtypeStatus

/-- The closeout catalog projects the full-carrier obstruction through the root API bundle. -/
theorem safeTraceRoadmapCloseout_catalog_projects_root_api_full_carrier_obstruction
    (hCat : SafeTraceRoadmapCloseoutCatalog) :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  hCat.rootApiExport.fullCarrierObstruction

/-- The closeout catalog projects the certificate bridge through the root API bundle. -/
def safeTraceRoadmapCloseout_catalog_projects_root_api_certificate_bridge_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceCertificateBridgeCatalog :=
  hCat.rootApiExport.certificateBridgeCatalog

/-- The closeout catalog projects the complexity bridge through the root API bundle. -/
def safeTraceRoadmapCloseout_catalog_projects_root_api_complexity_bridge_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceComplexityBridgeCatalog :=
  hCat.rootApiExport.complexityBridgeCatalog

/-- The closeout catalog projects the certificate audit through the root API bundle. -/
def safeTraceRoadmapCloseout_catalog_projects_root_api_certificate_audit_catalog
    (hCat : SafeTraceRoadmapCloseoutCatalog) : SafeTraceCertificateAuditCatalog :=
  hCat.rootApiExport.certificateAuditCatalog

end OperatorKO7.SafeTraceRoadmapCloseout
