import OperatorKO7.Meta.SafeTrace_CertificateAudit

namespace SafeTraceTripleLexExactnessReach

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateAudit
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open MetaSN_KO7

#check fullTripleLexBound
#check TraceRealization
#check TraceRealization.code
#check TraceRealization.order
#check TraceRealization.carrier_eq_of_code_eq
#check TraceRealization.code_eq_iff_carrier_eq
#check TraceRealization.code_injective_of_toCarrier_injective
#check TraceRealization.code_eq_iff_eq_of_toCarrier_injective
#check TraceRealization.order_reflects
#check TraceRealization.order_iff
#check TraceRealization.image_upper_bound
#check TraceRealization.surjective_below_of_toCarrier_surjective
#check TraceRealization.ExactOrderTypePackage
#check TraceRealization.ExactOrderTypePackage.toCarrier_surjective
#check TraceRealization.exact_order_type_package_of_toCarrier_surjective
#check CarrierFaithfulnessObstruction
#check CarrierFaithfulnessObstruction.sameCarrier
#check CarrierFaithfulnessObstruction.not_toCarrier_injective
#check CarrierFaithfulnessObstruction.not_code_injective
#check traceToFullTripleLexCarrier
#check traceToFullTripleLexCarrier_toLex3cTuple
#check ofTraceMap
#check ofTraceMap_code_eq_iff_mu3c_eq
#check traceRealization
#check trace_code_eq_iff_carrier_eq
#check trace_code_eq_iff_mu3c_eq
#check trace_order_reflects
#check trace_order_iff
#check trace_image_upper_bound
#check TraceCodeFaithful
#check TraceExactOrderTypeResidual
#check ambientTraceSurjectivityObstructionCarrier
#check trace_dmComponent_ne_zero_of_phase_one
#check no_trace_realizes_ambientTraceSurjectivityObstructionCarrier
#check traceFaithfulnessObstruction
#check trace_toCarrier_not_injective
#check trace_code_not_injective
#check trace_exact_order_type_residual_false
#check trace_no_exact_order_type_package
#check trace_exact_order_type_of_surjective
#check integrateChain
#check zeroDmPhaseZeroCarrier
#check phaseOneZeroDmCarrier
#check payloadTowerPhaseZeroCarrier
#check flaggedTowerPhaseOneCarrier
#check zeroDmPhaseZeroTrace
#check payloadTowerPhaseZeroTrace
#check flaggedTowerPhaseOneTrace
#check traceToFullTripleLexCarrier_zeroDmPhaseZeroTrace
#check traceToFullTripleLexCarrier_payloadTowerPhaseZeroTrace
#check traceToFullTripleLexCarrier_flaggedTowerPhaseOneTrace
#check trace_realizes_zeroDmPhaseZeroCarrier
#check trace_realizes_payloadTowerPhaseZeroCarrier
#check trace_realizes_flaggedTowerPhaseOneCarrier
#check trace_dmComponent_has_one_of_phase_one
#check no_trace_realizes_phase_one_without_one
#check no_trace_realizes_phaseOneZeroDmCarrier
#check TraceImageRangeStatus
#check traceImageRangeStatus
#check TraceRealizableCarrier
#check traceRealizableCarrier_realizes
#check traceRealizableCarrierRealization
#check traceRealizableCarrier_toCarrier_injective
#check TraceRealizableCarrierExactnessPackage
#check traceRealizableCarrier_code_eq_iff_eq
#check traceRealizableCarrier_order_iff
#check traceRealizableCarrier_image_upper_bound
#check traceRealizableCarrierExactnessPackage
#check not_every_fullTripleLexCarrier_trace_realizable
#check traceToFullTripleLexCarrier_not_surjective
#check trace_exact_order_type_package_requires_surjective
#check TraceImageSubtypeStatus
#check traceImageSubtypeStatus
#check zeroDmPhaseZeroRealization
#check payloadTowerPhaseZeroRealization
#check flaggedTowerPhaseOneRealization
#check zeroDmPhaseZero_code_eq_iff_carrier_eq
#check zeroDmPhaseZero_order_iff
#check zeroDmPhaseZero_image_upper_bound
#check payloadTowerPhaseZero_code_eq_iff_carrier_eq
#check payloadTowerPhaseZero_order_iff
#check payloadTowerPhaseZero_image_upper_bound
#check flaggedTowerPhaseOne_code_eq_iff_carrier_eq
#check flaggedTowerPhaseOne_order_iff
#check flaggedTowerPhaseOne_image_upper_bound
#check primitiveTraceImageRealization
#check primitiveTraceImage_code_eq_iff_carrier_eq
#check primitiveTraceImage_code_eq_iff_mu3c_eq
#check primitiveTraceImage_order_iff
#check primitiveTraceImage_image_upper_bound
#check primitiveTraceImageFaithfulnessObstruction
#check primitiveTraceImage_toCarrier_not_injective
#check primitiveTraceImage_code_not_injective
#check primitiveTraceImage_exact_order_type_of_surjective
#check externalizedTraceImageRealization
#check externalizedTraceImage_code_eq_iff_carrier_eq
#check externalizedTraceImage_code_eq_iff_mu3c_eq
#check externalizedTraceImage_order_iff
#check externalizedTraceImage_image_upper_bound
#check externalizedTraceImage_exact_order_type_of_surjective
#check traceRealizableCarrierOfTrace
#check traceRealizableCarrierOfTrace_carrier
#check SafeStepEndpointPackage
#check safeStepEndpointPackage
#check safeStepEndpointPackage_source_realizes
#check safeStepEndpointPackage_target_realizes
#check safeStepEndpoint_tau_pos_of_source
#check safeStepEndpoint_source_fundamentalSequence
#check safeStepEndpoint_source_exact_pred_step
#check safeStepEndpoint_target_repr_le_source_pred
#check safeStepEndpoint_root_length_le_tau
#check safeStepEndpoint_root_length_le_mwRootBound
#check SafeStepCtxChainPackage
#check safeStepCtxChainPackage
#check externalizedTraceImageToRealizableCarrier
#check externalizedTraceImageToRealizableCarrier_carrier
#check externalizedTraceImageToRealizableCarrier_realizes
#check externalizedTraceImage_code_eq_iff_realizable_eq
#check externalizedTraceImage_order_iff_realizable_order
#check externalizedTraceImage_realizable_upper_bound
#check SafeTraceCertificateBridgeCatalog
#check safe_trace_certificate_bridge_catalog
#check SafeStepEndpointComplexityPackage
#check safeStepEndpointComplexityPackage
#check safeStepEndpointComplexityPackage_tau_pos_of_source
#check safeStepEndpointComplexityPackage_source_exact_pred_step
#check safeStepEndpointComplexityPackage_target_repr_le_source_pred
#check safeStepEndpointComplexityPackage_root_length_le_tau
#check safeStepEndpointComplexityPackage_root_length_le_mwRootBound
#check safeStepEndpointComplexityPackage_source_code_eq_iff_eq
#check safeStepEndpointComplexityPackage_source_order_iff
#check safeStepEndpointComplexityPackage_source_upper_bound
#check safeStepEndpointComplexityPackage_target_code_eq_iff_eq
#check safeStepEndpointComplexityPackage_target_order_iff
#check safeStepEndpointComplexityPackage_target_upper_bound
#check SafeStepCtxComplexityPackage
#check safeStepCtxComplexityPackage
#check safeStepCtxComplexityPackage_ctxFuel_antitone
#check safeStepCtxComplexityPackage_exact_drop
#check safeStepCtxComplexityPackage_length_le_ctxFuel_drop
#check safeStepCtxComplexityPackage_length_le_ctxFuel
#check safeStepCtxComplexityPackage_length_le_mwCtxBound
#check safeStepCtxComplexityPackage_length_bounded_by_size
#check safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope
#check safeStepCtxComplexityPackage_source_code_eq_iff_eq
#check safeStepCtxComplexityPackage_source_order_iff
#check safeStepCtxComplexityPackage_source_upper_bound
#check safeStepCtxComplexityPackage_target_code_eq_iff_eq
#check safeStepCtxComplexityPackage_target_order_iff
#check safeStepCtxComplexityPackage_target_upper_bound
#check externalizedTraceImageRecovery_code_eq_iff_realizable_eq
#check externalizedTraceImageRecovery_order_iff_realizable_order
#check externalizedTraceImageRecovery_upper_bound
#check SafeTraceComplexityBridgeCatalog
#check safe_trace_complexity_bridge_catalog
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

example (t : OperatorKO7.Trace) :
    (traceToFullTripleLexCarrier t).toLex3cTuple = mu3c t :=
  traceToFullTripleLexCarrier_toLex3cTuple t

example {a b : OperatorKO7.Trace} :
    traceRealization.code a = traceRealization.code b ↔ mu3c a = mu3c b :=
  trace_code_eq_iff_mu3c_eq

example (a b : OperatorKO7.Trace) :
    traceRealization.order a b ↔ traceRealization.code a < traceRealization.code b :=
  trace_order_iff a b

example : ¬ TraceCodeFaithful :=
  trace_code_not_injective

example (h : TraceExactOrderTypeResidual) :
    TraceRealization.ExactOrderTypePackage traceRealization :=
  trace_exact_order_type_of_surjective h

example : ¬ TraceExactOrderTypeResidual :=
  trace_exact_order_type_residual_false

example : ¬ TraceRealization.ExactOrderTypePackage traceRealization :=
  trace_no_exact_order_type_package

example (tauComponent : Nat) :
    ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = zeroDmPhaseZeroCarrier tauComponent :=
  trace_realizes_zeroDmPhaseZeroCarrier tauComponent

example (n slack : Nat) :
    ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = payloadTowerPhaseZeroCarrier n slack :=
  trace_realizes_payloadTowerPhaseZeroCarrier n slack

example (n slack : Nat) :
    ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = flaggedTowerPhaseOneCarrier n slack :=
  trace_realizes_flaggedTowerPhaseOneCarrier n slack

example {t : OperatorKO7.Trace}
    (hPhase : (traceToFullTripleLexCarrier t).phase = 1) :
    1 ∈ (traceToFullTripleLexCarrier t).dmComponent :=
  trace_dmComponent_has_one_of_phase_one hPhase

example {x : FullTripleLexCarrier}
    (hPhase : x.phase = 1) (hMissing : 1 ∉ x.dmComponent) :
    ¬ ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = x :=
  no_trace_realizes_phase_one_without_one hPhase hMissing

example (tauComponent : Nat) :
    ¬ ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = phaseOneZeroDmCarrier tauComponent :=
  no_trace_realizes_phaseOneZeroDmCarrier tauComponent

example : TraceImageRangeStatus :=
  traceImageRangeStatus

example (x : TraceRealizableCarrier) :
    ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = x.1 :=
  traceRealizableCarrier_realizes x

example {x y : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code x = traceRealizableCarrierRealization.code y ↔ x = y :=
  traceRealizableCarrier_code_eq_iff_eq

example (x y : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order x y ↔
      traceRealizableCarrierRealization.code x < traceRealizableCarrierRealization.code y :=
  traceRealizableCarrier_order_iff x y

example :
    ¬ ∀ x : FullTripleLexCarrier, ∃ t : OperatorKO7.Trace, traceToFullTripleLexCarrier t = x :=
  not_every_fullTripleLexCarrier_trace_realizable

example : ¬ Function.Surjective traceToFullTripleLexCarrier :=
  traceToFullTripleLexCarrier_not_surjective

example (hPkg : TraceRealization.ExactOrderTypePackage traceRealization) :
    Function.Surjective traceToFullTripleLexCarrier :=
  trace_exact_order_type_package_requires_surjective hPkg

example : TraceImageSubtypeStatus :=
  traceImageSubtypeStatus

example (a b : Nat) :
    zeroDmPhaseZeroRealization.order a b ↔
      zeroDmPhaseZeroRealization.code a < zeroDmPhaseZeroRealization.code b :=
  zeroDmPhaseZero_order_iff a b

example (a b : Nat × Nat) :
    payloadTowerPhaseZeroRealization.order a b ↔
      payloadTowerPhaseZeroRealization.code a < payloadTowerPhaseZeroRealization.code b :=
  payloadTowerPhaseZero_order_iff a b

example (a b : Nat × Nat) :
    flaggedTowerPhaseOneRealization.order a b ↔
      flaggedTowerPhaseOneRealization.code a < flaggedTowerPhaseOneRealization.code b :=
  flaggedTowerPhaseOne_order_iff a b

example {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      primitiveTraceImageRealization.toCarrier x = primitiveTraceImageRealization.toCarrier y :=
  primitiveTraceImage_code_eq_iff_carrier_eq

example {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      mu3c x.1 = mu3c y.1 :=
  primitiveTraceImage_code_eq_iff_mu3c_eq

example (x y : PrimitiveTraceImage) :
    primitiveTraceImageRealization.order x y ↔
      primitiveTraceImageRealization.code x < primitiveTraceImageRealization.code y :=
  primitiveTraceImage_order_iff x y

example : ¬ Function.Injective primitiveTraceImageRealization.toCarrier :=
  primitiveTraceImage_toCarrier_not_injective

example (hSurj : Function.Surjective primitiveTraceImageRealization.toCarrier) :
    TraceRealization.ExactOrderTypePackage primitiveTraceImageRealization :=
  primitiveTraceImage_exact_order_type_of_surjective hSurj

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) (x y : X.imageCarrier) :
    let RX := externalizedTraceImageRealization X
    RX.code x = RX.code y ↔ RX.toCarrier x = RX.toCarrier y := by
  simpa using
    (externalizedTraceImage_code_eq_iff_carrier_eq (X := X) (x := x) (y := y))

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) (x y : X.imageCarrier) :
    let RX := externalizedTraceImageRealization X
    RX.code x = RX.code y ↔ mu3c x.1 = mu3c y.1 := by
  simpa using
    (externalizedTraceImage_code_eq_iff_mu3c_eq (X := X) (x := x) (y := y))

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) (x y : X.imageCarrier) :
    let RX := externalizedTraceImageRealization X
    RX.order x y ↔ RX.code x < RX.code y := by
  simpa using
    (externalizedTraceImage_order_iff (X := X) x y)

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace)
    (hSurj : Function.Surjective (externalizedTraceImageRealization X).toCarrier) :
    TraceRealization.ExactOrderTypePackage (externalizedTraceImageRealization X) :=
  externalizedTraceImage_exact_order_type_of_surjective X hSurj

example (t : OperatorKO7.Trace) : TraceRealizableCarrier :=
  traceRealizableCarrierOfTrace t

example (t : OperatorKO7.Trace) :
    (traceRealizableCarrierOfTrace t).1 = traceToFullTripleLexCarrier t :=
  traceRealizableCarrierOfTrace_carrier t

example {a b : OperatorKO7.Trace} (h : SafeStep a b) :
    0 < tau a :=
  safeStepEndpoint_tau_pos_of_source (safeStepEndpointPackage h)

example {a b u : OperatorKO7.Trace} {n : Nat} (h : SafeStep a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepEndpoint_root_length_le_mwRootBound (safeStepEndpointPackage h) hPow

example {n : Nat} {t u : OperatorKO7.Trace} (h : SafeStepCtxPow n t u) :
    n ≤ complexity_bound (termSize t) :=
  (safeStepCtxChainPackage h).lengthBoundedBySize

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImage_code_eq_iff_realizable_eq X

example : SafeTraceCertificateBridgeCatalog :=
  safe_trace_certificate_bridge_catalog

example {a b : OperatorKO7.Trace} (h : SafeStep a b) :
    0 < tau a :=
  safeStepEndpointComplexityPackage_tau_pos_of_source
    (safeStepEndpointComplexityPackage h)

example {n : Nat} {t u : OperatorKO7.Trace} (h : SafeStepCtxPow n t u) :
    n ≤ fgOmegaEnvelope (termSize t) :=
  safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope
    (safeStepCtxComplexityPackage h)

noncomputable example : SafeTraceComplexityBridgeCatalog :=
  safe_trace_complexity_bridge_catalog

example : SafeTraceCertificateAuditCatalog :=
  safe_trace_certificate_audit_catalog

example (row : SafeTraceCertificateAuditRow) :
    SafeTraceCertificateAuditRowEvidence row :=
  safeTraceCertificateAudit_catalog_projects_evidence
    safe_trace_certificate_audit_catalog row

example {α : Type} (R : TraceRealization α)
    (hSurj : Function.Surjective R.toCarrier) :
    ∀ β < fullTripleLexBound, ∃ x : α, R.code x = β :=
  (R.exact_order_type_package_of_toCarrier_surjective hSurj).surjectiveBelow

example {α : Type} (R : TraceRealization α)
    (hPkg : TraceRealization.ExactOrderTypePackage R) :
    Function.Surjective R.toCarrier :=
  hPkg.toCarrier_surjective

end SafeTraceTripleLexExactnessReach
