import OperatorKO7.Meta.SafeTrace_TripleLexExactness
import OperatorKO7.Meta.SafeTrace_CertificateBridge
import OperatorKO7.Meta.SafeTrace_ComplexityBridge
import OperatorKO7.Meta.SafeTrace_CertificateAudit
import OperatorKO7.Meta.SafeTrace_RoadmapCloseout

/-!
# Safe-Trace Triple-Lex Exactness Final Catalog

This file packages the theorem-backed safe-trace exactness surface built on top
of the closed M3 calibrated-carrier exactness layer.
-/

namespace OperatorKO7.SafeTraceTripleLexExactnessFinalCatalog

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.OrdinalHierarchy
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateAudit
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceRoadmapCloseout
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open NONote
open MetaSN_KO7

/-- Final theorem-facing catalog for the safe-trace realization layer. -/
structure SafeTraceExactnessFinalCatalog where
  traceCodeCarrierEq :
    ∀ {a b : Trace},
      traceRealization.code a = traceRealization.code b ↔
        traceToFullTripleLexCarrier a = traceToFullTripleLexCarrier b
  traceCodeMu3cEq :
    ∀ {a b : Trace},
      traceRealization.code a = traceRealization.code b ↔ mu3c a = mu3c b
  traceOrderReflects :
    ∀ {a b : Trace},
      traceRealization.code a < traceRealization.code b → traceRealization.order a b
  traceOrderIff :
    ∀ a b : Trace,
      traceRealization.order a b ↔ traceRealization.code a < traceRealization.code b
  traceImageUpperBound :
    ∀ t : Trace, traceRealization.code t < fullTripleLexBound
  traceFaithfulnessBoundary : CarrierFaithfulnessObstruction traceRealization
  concreteCarrierFaithfulnessObstruction : CarrierFaithfulnessObstruction traceRealization
  existsTraceCarrierCollision :
    ∃ t1 t2 : Trace,
      t1 ≠ t2 ∧ traceRealization.toCarrier t1 = traceRealization.toCarrier t2
  traceCarrierNotInjective : ¬ Function.Injective traceRealization.toCarrier
  traceCodeNotInjective : ¬ TraceCodeFaithful
  traceExactOrderTypeResidual :
    TraceExactOrderTypeResidual →
      TraceRealization.ExactOrderTypePackage traceRealization
  traceExactOrderTypeObstructionCarrier : FullTripleLexCarrier
  traceExactOrderTypeObstruction :
    ¬ ∃ t : Trace,
      traceToFullTripleLexCarrier t = traceExactOrderTypeObstructionCarrier
  traceExactOrderTypeResidualFalse : ¬ TraceExactOrderTypeResidual
  traceNoExactOrderTypePackage :
    ¬ TraceRealization.ExactOrderTypePackage traceRealization
  traceImageRangeStatus : TraceImageRangeStatus
  traceImageSubtypeStatus : TraceImageSubtypeStatus
  certificateBridgeCatalog : SafeTraceCertificateBridgeCatalog
  complexityBridgeCatalog : SafeTraceComplexityBridgeCatalog
  certificateAuditCatalog : SafeTraceCertificateAuditCatalog
  roadmapCloseoutCatalog : SafeTraceRoadmapCloseoutCatalog
  zeroDmPhaseZeroCodeCarrierEq :
    ∀ {a b : Nat},
      zeroDmPhaseZeroRealization.code a = zeroDmPhaseZeroRealization.code b ↔
        zeroDmPhaseZeroCarrier a = zeroDmPhaseZeroCarrier b
  zeroDmPhaseZeroOrderIff :
    ∀ a b : Nat,
      zeroDmPhaseZeroRealization.order a b ↔
        zeroDmPhaseZeroRealization.code a < zeroDmPhaseZeroRealization.code b
  zeroDmPhaseZeroUpperBound :
    ∀ a : Nat, zeroDmPhaseZeroRealization.code a < fullTripleLexBound
  payloadTowerPhaseZeroCodeCarrierEq :
    ∀ {a b : Nat × Nat},
      payloadTowerPhaseZeroRealization.code a = payloadTowerPhaseZeroRealization.code b ↔
        payloadTowerPhaseZeroCarrier a.1 a.2 = payloadTowerPhaseZeroCarrier b.1 b.2
  payloadTowerPhaseZeroOrderIff :
    ∀ a b : Nat × Nat,
      payloadTowerPhaseZeroRealization.order a b ↔
        payloadTowerPhaseZeroRealization.code a < payloadTowerPhaseZeroRealization.code b
  payloadTowerPhaseZeroUpperBound :
    ∀ a : Nat × Nat, payloadTowerPhaseZeroRealization.code a < fullTripleLexBound
  flaggedTowerPhaseOneCodeCarrierEq :
    ∀ {a b : Nat × Nat},
      flaggedTowerPhaseOneRealization.code a = flaggedTowerPhaseOneRealization.code b ↔
        flaggedTowerPhaseOneCarrier a.1 a.2 = flaggedTowerPhaseOneCarrier b.1 b.2
  flaggedTowerPhaseOneOrderIff :
    ∀ a b : Nat × Nat,
      flaggedTowerPhaseOneRealization.order a b ↔
        flaggedTowerPhaseOneRealization.code a < flaggedTowerPhaseOneRealization.code b
  flaggedTowerPhaseOneUpperBound :
    ∀ a : Nat × Nat, flaggedTowerPhaseOneRealization.code a < fullTripleLexBound
  primitiveImageCodeCarrierEq :
    ∀ {x y : PrimitiveTraceImage},
      primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
        primitiveTraceImageRealization.toCarrier x = primitiveTraceImageRealization.toCarrier y
  primitiveImageCodeMu3cEq :
    ∀ {x y : PrimitiveTraceImage},
      primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
        mu3c x.1 = mu3c y.1
  primitiveImageOrderIff :
    ∀ x y : PrimitiveTraceImage,
      primitiveTraceImageRealization.order x y ↔
        primitiveTraceImageRealization.code x < primitiveTraceImageRealization.code y
  primitiveImageUpperBound :
    ∀ x : PrimitiveTraceImage,
      primitiveTraceImageRealization.code x < fullTripleLexBound
  primitiveImageFaithfulnessBoundary :
    CarrierFaithfulnessObstruction primitiveTraceImageRealization
  primitiveImageCarrierNotInjective :
    ¬ Function.Injective primitiveTraceImageRealization.toCarrier
  primitiveImageCodeNotInjective :
    ¬ Function.Injective primitiveTraceImageRealization.code
  primitiveImageExactOrderType :
    Function.Surjective primitiveTraceImageRealization.toCarrier →
      TraceRealization.ExactOrderTypePackage primitiveTraceImageRealization
  externalizedImageCodeCarrierEq :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace)
      {x y : X.imageCarrier},
      (externalizedTraceImageRealization X).code x =
          (externalizedTraceImageRealization X).code y ↔
        (externalizedTraceImageRealization X).toCarrier x =
          (externalizedTraceImageRealization X).toCarrier y
  externalizedImageCodeMu3cEq :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace)
      {x y : X.imageCarrier},
      (externalizedTraceImageRealization X).code x =
          (externalizedTraceImageRealization X).code y ↔
        mu3c x.1 = mu3c y.1
  externalizedImageOrderIff :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier),
      (externalizedTraceImageRealization X).order x y ↔
        (externalizedTraceImageRealization X).code x <
          (externalizedTraceImageRealization X).code y
  externalizedImageUpperBound :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      (externalizedTraceImageRealization X).code x < fullTripleLexBound
  externalizedImageExactOrderType :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace),
      Function.Surjective (externalizedTraceImageRealization X).toCarrier →
        TraceRealization.ExactOrderTypePackage (externalizedTraceImageRealization X)
  genericExactOrderTypeTransport :
    ∀ {α : Type} (R : TraceRealization α),
      Function.Surjective R.toCarrier → TraceRealization.ExactOrderTypePackage R

/-- Canonical safe-trace exactness catalog. -/
noncomputable def safe_trace_triple_lex_exactness_final_catalog :
  SafeTraceExactnessFinalCatalog where
  traceCodeCarrierEq := by
    intro a b
    exact trace_code_eq_iff_carrier_eq
  traceCodeMu3cEq := by
    intro a b
    exact trace_code_eq_iff_mu3c_eq
  traceOrderReflects := by
    intro a b hlt
    exact trace_order_reflects hlt
  traceOrderIff := trace_order_iff
  traceImageUpperBound := trace_image_upper_bound
  traceFaithfulnessBoundary := traceFaithfulnessObstruction
  concreteCarrierFaithfulnessObstruction := concreteCarrierFaithfulnessObstruction
  existsTraceCarrierCollision := exists_trace_carrier_collision
  traceCarrierNotInjective := trace_toCarrier_not_injective
  traceCodeNotInjective := trace_code_not_injective
  traceExactOrderTypeResidual := trace_exact_order_type_of_surjective
  traceExactOrderTypeObstructionCarrier := ambientTraceSurjectivityObstructionCarrier
  traceExactOrderTypeObstruction := no_trace_realizes_ambientTraceSurjectivityObstructionCarrier
  traceExactOrderTypeResidualFalse := trace_exact_order_type_residual_false
  traceNoExactOrderTypePackage := trace_no_exact_order_type_package
  traceImageRangeStatus := traceImageRangeStatus
  traceImageSubtypeStatus := traceImageSubtypeStatus
  certificateBridgeCatalog := safe_trace_certificate_bridge_catalog
  complexityBridgeCatalog := safe_trace_complexity_bridge_catalog
  certificateAuditCatalog := safe_trace_certificate_audit_catalog
  roadmapCloseoutCatalog := safe_trace_roadmap_closeout_catalog
  zeroDmPhaseZeroCodeCarrierEq := by
    intro a b
    exact zeroDmPhaseZero_code_eq_iff_carrier_eq
  zeroDmPhaseZeroOrderIff := zeroDmPhaseZero_order_iff
  zeroDmPhaseZeroUpperBound := zeroDmPhaseZero_image_upper_bound
  payloadTowerPhaseZeroCodeCarrierEq := by
    intro a b
    exact payloadTowerPhaseZero_code_eq_iff_carrier_eq
  payloadTowerPhaseZeroOrderIff := payloadTowerPhaseZero_order_iff
  payloadTowerPhaseZeroUpperBound := payloadTowerPhaseZero_image_upper_bound
  flaggedTowerPhaseOneCodeCarrierEq := by
    intro a b
    exact flaggedTowerPhaseOne_code_eq_iff_carrier_eq
  flaggedTowerPhaseOneOrderIff := flaggedTowerPhaseOne_order_iff
  flaggedTowerPhaseOneUpperBound := flaggedTowerPhaseOne_image_upper_bound
  primitiveImageCodeCarrierEq := by
    intro x y
    exact primitiveTraceImage_code_eq_iff_carrier_eq
  primitiveImageCodeMu3cEq := by
    intro x y
    exact primitiveTraceImage_code_eq_iff_mu3c_eq
  primitiveImageOrderIff := primitiveTraceImage_order_iff
  primitiveImageUpperBound := primitiveTraceImage_image_upper_bound
  primitiveImageFaithfulnessBoundary := primitiveTraceImageFaithfulnessObstruction
  primitiveImageCarrierNotInjective := primitiveTraceImage_toCarrier_not_injective
  primitiveImageCodeNotInjective := primitiveTraceImage_code_not_injective
  primitiveImageExactOrderType := primitiveTraceImage_exact_order_type_of_surjective
  externalizedImageCodeCarrierEq := by
    intro K X x y
    exact externalizedTraceImage_code_eq_iff_carrier_eq X
  externalizedImageCodeMu3cEq := by
    intro K X x y
    exact externalizedTraceImage_code_eq_iff_mu3c_eq X
  externalizedImageOrderIff := by
    intro K X x y
    exact externalizedTraceImage_order_iff X x y
  externalizedImageUpperBound := externalizedTraceImage_image_upper_bound
  externalizedImageExactOrderType := by
    intro K X hSurj
    exact externalizedTraceImage_exact_order_type_of_surjective X hSurj
  genericExactOrderTypeTransport := by
    intro α R hSurj
    exact R.exact_order_type_package_of_toCarrier_surjective hSurj

/-- The final catalog projects the ambient trace code-to-carrier equality criterion. -/
theorem final_catalog_projects_trace_code_carrier_eq
    {a b : Trace} :
    traceRealization.code a = traceRealization.code b ↔
      traceToFullTripleLexCarrier a = traceToFullTripleLexCarrier b :=
  safe_trace_triple_lex_exactness_final_catalog.traceCodeCarrierEq

/-- The final catalog projects the ambient trace code-to-`mu3c` equality criterion. -/
theorem final_catalog_projects_trace_code_mu3c_eq
    {a b : Trace} :
    traceRealization.code a = traceRealization.code b ↔ mu3c a = mu3c b :=
  safe_trace_triple_lex_exactness_final_catalog.traceCodeMu3cEq

/-- The final catalog projects order reflection on ambient traces. -/
theorem final_catalog_projects_trace_order_reflects
    {a b : Trace}
    (hlt : traceRealization.code a < traceRealization.code b) :
    traceRealization.order a b :=
  safe_trace_triple_lex_exactness_final_catalog.traceOrderReflects hlt

/-- The final catalog projects exact order equivalence on ambient traces. -/
theorem final_catalog_projects_trace_order_iff
    (a b : Trace) :
    traceRealization.order a b ↔ traceRealization.code a < traceRealization.code b :=
  safe_trace_triple_lex_exactness_final_catalog.traceOrderIff a b

/-- The final catalog projects the ambient trace image bound. -/
theorem final_catalog_projects_trace_image_upper_bound
    (t : Trace) :
    traceRealization.code t < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.traceImageUpperBound t

/-- The final catalog projects the explicit ambient trace faithfulness obstruction. -/
noncomputable def final_catalog_projects_trace_faithfulness_boundary :
    CarrierFaithfulnessObstruction traceRealization :=
  safe_trace_triple_lex_exactness_final_catalog.traceFaithfulnessBoundary

/-- The final catalog projects the concrete LONG-37 ambient trace collision witness. -/
noncomputable def final_catalog_projects_concreteCarrierFaithfulnessObstruction :
    CarrierFaithfulnessObstruction traceRealization :=
  safe_trace_triple_lex_exactness_final_catalog.concreteCarrierFaithfulnessObstruction

/-- The final catalog projects the explicit ambient trace carrier collision theorem. -/
theorem final_catalog_projects_exists_trace_carrier_collision :
    ∃ t1 t2 : Trace,
      t1 ≠ t2 ∧ traceRealization.toCarrier t1 = traceRealization.toCarrier t2 :=
  safe_trace_triple_lex_exactness_final_catalog.existsTraceCarrierCollision

/-- The final catalog projects failure of ambient trace carrier injectivity. -/
theorem final_catalog_projects_trace_carrier_not_injective :
    ¬ Function.Injective traceRealization.toCarrier :=
  safe_trace_triple_lex_exactness_final_catalog.traceCarrierNotInjective

/-- The final catalog projects failure of ambient trace code faithfulness. -/
theorem final_catalog_projects_trace_code_not_injective :
    ¬ TraceCodeFaithful :=
  safe_trace_triple_lex_exactness_final_catalog.traceCodeNotInjective

/-- The final catalog projects the residual hypothesis needed for a full ambient
trace exact-order-type package. -/
theorem final_catalog_projects_trace_exact_order_type_of_surjective
    (hResidual : TraceExactOrderTypeResidual) :
    TraceRealization.ExactOrderTypePackage traceRealization :=
  safe_trace_triple_lex_exactness_final_catalog.traceExactOrderTypeResidual hResidual

/-- The final catalog projects the explicit ambient-trace exact-order-type obstruction carrier. -/
noncomputable def final_catalog_projects_trace_exact_order_type_obstruction_carrier :
    FullTripleLexCarrier :=
  safe_trace_triple_lex_exactness_final_catalog.traceExactOrderTypeObstructionCarrier

/-- The final catalog projects the proof that the obstruction carrier is unrealized by ambient traces. -/
theorem final_catalog_projects_trace_exact_order_type_obstruction :
    ¬ ∃ t : Trace,
      traceToFullTripleLexCarrier t =
        final_catalog_projects_trace_exact_order_type_obstruction_carrier :=
  safe_trace_triple_lex_exactness_final_catalog.traceExactOrderTypeObstruction

/-- The final catalog projects failure of the ambient-trace surjectivity residual. -/
theorem final_catalog_projects_trace_exact_order_type_residual_false :
    ¬ TraceExactOrderTypeResidual :=
  safe_trace_triple_lex_exactness_final_catalog.traceExactOrderTypeResidualFalse

/-- The final catalog projects failure of an unconditional ambient exact-order-type package. -/
theorem final_catalog_projects_trace_no_exact_order_type_package :
    ¬ TraceRealization.ExactOrderTypePackage traceRealization :=
  safe_trace_triple_lex_exactness_final_catalog.traceNoExactOrderTypePackage

/-- The final catalog projects the theorem-visible ambient trace-image range/status object. -/
def final_catalog_projects_trace_image_range_status : TraceImageRangeStatus :=
  safe_trace_triple_lex_exactness_final_catalog.traceImageRangeStatus

/-- The final catalog projects the theorem-visible trace-image subtype status object. -/
def final_catalog_projects_trace_image_subtype_status : TraceImageSubtypeStatus :=
  safe_trace_triple_lex_exactness_final_catalog.traceImageSubtypeStatus

/-- The final catalog projects the theorem-facing safe-trace certificate-bridge catalog. -/
noncomputable def final_catalog_projects_certificate_bridge_catalog : SafeTraceCertificateBridgeCatalog :=
  safe_trace_triple_lex_exactness_final_catalog.certificateBridgeCatalog

/-- The final catalog projects the theorem-facing safe-trace complexity-bridge catalog. -/
noncomputable def final_catalog_projects_complexity_bridge_catalog : SafeTraceComplexityBridgeCatalog :=
  safe_trace_triple_lex_exactness_final_catalog.complexityBridgeCatalog

/-- The final catalog projects the finite safe-trace certificate audit catalog. -/
def final_catalog_projects_certificate_audit_catalog : SafeTraceCertificateAuditCatalog :=
  safe_trace_triple_lex_exactness_final_catalog.certificateAuditCatalog

/-- The final catalog projects the finite safe-trace roadmap closeout catalog. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog : SafeTraceRoadmapCloseoutCatalog :=
  safe_trace_triple_lex_exactness_final_catalog.roadmapCloseoutCatalog

/-- The final catalog projects the canonical realized-carrier point attached to an ambient trace. -/
def final_catalog_projects_traceRealizableCarrierOfTrace (t : Trace) : TraceRealizableCarrier :=
  traceRealizableCarrierOfTrace t

/-- The final catalog projects the carrier identity of the canonical realized-carrier point. -/
theorem final_catalog_projects_traceRealizableCarrierOfTrace_carrier (t : Trace) :
    (final_catalog_projects_traceRealizableCarrierOfTrace t).1 = traceToFullTripleLexCarrier t :=
  traceRealizableCarrierOfTrace_carrier t

/-- The final catalog projects the canonical theorem-visible endpoint package for a guarded root step. -/
def final_catalog_projects_safeStepEndpointPackage {a b : Trace}
    (h : SafeStep a b) : SafeStepEndpointPackage a b :=
  safeStepEndpointPackage h

/-- The final catalog projects source realizability for guarded root endpoints. -/
theorem final_catalog_projects_safeStepEndpointPackage_source_realizes {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = P.sourceCarrier :=
  safeStepEndpointPackage_source_realizes P

/-- The final catalog projects target realizability for guarded root endpoints. -/
theorem final_catalog_projects_safeStepEndpointPackage_target_realizes {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = P.targetCarrier :=
  safeStepEndpointPackage_target_realizes P

/-- The final catalog projects positivity of the safe-step source tail. -/
theorem final_catalog_projects_safeStepEndpoint_tau_pos_of_source {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    0 < tau a :=
  safeStepEndpoint_tau_pos_of_source P

/-- The final catalog projects the explicit predecessor fundamental sequence at the root endpoint. -/
theorem final_catalog_projects_safeStepEndpoint_source_fundamentalSequence {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    (lex3Note (mu3c a)).1.fundamentalSequence =
      Sum.inl (some (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1) :=
  safeStepEndpoint_source_fundamentalSequence P

/-- The final catalog projects one exact predecessor step at the root endpoint. -/
theorem final_catalog_projects_safeStepEndpoint_source_exact_pred_step {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
  OperatorKO7.OrdinalHierarchy.ExactControlledPow (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1) :=
  safeStepEndpoint_source_exact_pred_step P

/-- The final catalog projects the target predecessor bound at the root endpoint. -/
theorem final_catalog_projects_safeStepEndpoint_target_repr_le_source_pred {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))) :=
  safeStepEndpoint_target_repr_le_source_pred P

/-- The final catalog projects the `τ`-tail bound for root chains starting at a guarded endpoint source. -/
theorem final_catalog_projects_safeStepEndpoint_root_length_le_tau {a b u : Trace} {n : Nat}
    (P : SafeStepEndpointPackage a b) (hPow : SafeStepPow a n u) :
    n ≤ tau a :=
  safeStepEndpoint_root_length_le_tau P hPow

/-- The final catalog projects the MW root bound for root chains starting at a guarded endpoint source. -/
theorem final_catalog_projects_safeStepEndpoint_root_length_le_mwRootBound
    {a b u : Trace} {n : Nat} (P : SafeStepEndpointPackage a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepEndpoint_root_length_le_mwRootBound P hPow

/-- The final catalog projects the canonical theorem-visible context-chain package. -/
def final_catalog_projects_safeStepCtxChainPackage {n : Nat} {t u : Trace}
    (h : SafeStepCtxPow n t u) : SafeStepCtxChainPackage n t u :=
  safeStepCtxChainPackage h

/-- The final catalog projects recovery of an externalized image point into the realized carrier subtype. -/
def final_catalog_projects_externalizedTraceImageToRealizableCarrier {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) : TraceRealizableCarrier :=
  externalizedTraceImageToRealizableCarrier X x

/-- The final catalog projects realizability of recovered externalized-image points. -/
theorem final_catalog_projects_externalizedTraceImageToRealizableCarrier_realizes {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    ∃ t : Trace,
      traceToFullTripleLexCarrier t =
        (final_catalog_projects_externalizedTraceImageToRealizableCarrier X x).1 :=
  externalizedTraceImageToRealizableCarrier_realizes X x

/-- The final catalog projects code equality for externalized image points after recovery into the realized carrier subtype. -/
theorem final_catalog_projects_externalizedTraceImage_code_eq_iff_realizable_eq {K : Nat}
    (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      final_catalog_projects_externalizedTraceImageToRealizableCarrier X x =
        final_catalog_projects_externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImage_code_eq_iff_realizable_eq X

/-- The final catalog projects order compatibility for externalized image points after recovery. -/
theorem final_catalog_projects_externalizedTraceImage_order_iff_realizable_order {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      traceRealizableCarrierRealization.order
        (final_catalog_projects_externalizedTraceImageToRealizableCarrier X x)
        (final_catalog_projects_externalizedTraceImageToRealizableCarrier X y) :=
  externalizedTraceImage_order_iff_realizable_order X x y

/-- The final catalog projects the realized-subtype bound for recovered externalized image points. -/
theorem final_catalog_projects_externalizedTraceImage_realizable_upper_bound {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    traceRealizableCarrierRealization.code
        (final_catalog_projects_externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound :=
  externalizedTraceImage_realizable_upper_bound X x

/-- The final catalog projects the theorem-visible root-endpoint complexity package. -/
def final_catalog_projects_safeStepEndpointComplexityPackage {a b : Trace}
    (h : SafeStep a b) : SafeStepEndpointComplexityPackage a b :=
  safeStepEndpointComplexityPackage h

/-- The final catalog projects positivity of the root-endpoint source `τ` tail. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_tau_pos_of_source {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    0 < tau a :=
  safeStepEndpointComplexityPackage_tau_pos_of_source P

/-- The final catalog projects one exact predecessor step at a root endpoint. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_source_exact_pred_step
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1) :=
  safeStepEndpointComplexityPackage_source_exact_pred_step P

/-- The final catalog projects the root-endpoint target predecessor bound. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_target_repr_le_source_pred
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))) :=
  safeStepEndpointComplexityPackage_target_repr_le_source_pred P

/-- The final catalog projects the root-endpoint `τ` length bound. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_root_length_le_tau
    {a b u : Trace} {n : Nat} (P : SafeStepEndpointComplexityPackage a b)
    (hPow : SafeStepPow a n u) :
    n ≤ tau a :=
  safeStepEndpointComplexityPackage_root_length_le_tau P hPow

/-- The final catalog projects the root-endpoint MW length bound. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_root_length_le_mwRootBound
    {a b u : Trace} {n : Nat} (P : SafeStepEndpointComplexityPackage a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepEndpointComplexityPackage_root_length_le_mwRootBound P hPow

/-- The final catalog projects exact code equality for the realized source endpoint. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_source_code_eq_iff_eq
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.endpointPackage.sourceMember =
        traceRealizableCarrierRealization.code x ↔
      P.endpointPackage.sourceMember = x :=
  safeStepEndpointComplexityPackage_source_code_eq_iff_eq P

/-- The final catalog projects exact order for the realized source endpoint. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_source_order_iff
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.endpointPackage.sourceMember x ↔
      traceRealizableCarrierRealization.code P.endpointPackage.sourceMember <
        traceRealizableCarrierRealization.code x :=
  safeStepEndpointComplexityPackage_source_order_iff P x

/-- The final catalog projects the realized source-endpoint upper bound. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_source_upper_bound
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) :
    traceRealizableCarrierRealization.code P.endpointPackage.sourceMember < fullTripleLexBound :=
  safeStepEndpointComplexityPackage_source_upper_bound P

/-- The final catalog projects exact code equality for the realized target endpoint. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_target_code_eq_iff_eq
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.endpointPackage.targetMember =
        traceRealizableCarrierRealization.code x ↔
      P.endpointPackage.targetMember = x :=
  safeStepEndpointComplexityPackage_target_code_eq_iff_eq P

/-- The final catalog projects exact order for the realized target endpoint. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_target_order_iff
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.endpointPackage.targetMember x ↔
      traceRealizableCarrierRealization.code P.endpointPackage.targetMember <
        traceRealizableCarrierRealization.code x :=
  safeStepEndpointComplexityPackage_target_order_iff P x

/-- The final catalog projects the realized target-endpoint upper bound. -/
theorem final_catalog_projects_safeStepEndpointComplexityPackage_target_upper_bound
    {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) :
    traceRealizableCarrierRealization.code P.endpointPackage.targetMember < fullTripleLexBound :=
  safeStepEndpointComplexityPackage_target_upper_bound P

/-- The final catalog projects the theorem-visible context-chain complexity package. -/
def final_catalog_projects_safeStepCtxComplexityPackage {n : Nat} {t u : Trace}
    (h : SafeStepCtxPow n t u) : SafeStepCtxComplexityPackage n t u :=
  safeStepCtxComplexityPackage h

/-- The final catalog projects contextual `ctxFuel` antitonicity. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_ctxFuel_antitone
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    ctxFuel u ≤ ctxFuel t :=
  safeStepCtxComplexityPackage_ctxFuel_antitone P

/-- The final catalog projects exact contextual drop. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_exact_drop
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
      (ctxExactNote u).1 (ctxFuel t - ctxFuel u) :=
  safeStepCtxComplexityPackage_exact_drop P

/-- The final catalog projects the contextual fuel-drop length bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_length_le_ctxFuel_drop
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ ctxFuel t - ctxFuel u :=
  safeStepCtxComplexityPackage_length_le_ctxFuel_drop P

/-- The final catalog projects the contextual `ctxFuel` length bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_length_le_ctxFuel
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ ctxFuel t :=
  safeStepCtxComplexityPackage_length_le_ctxFuel P

/-- The final catalog projects the contextual MW bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_length_le_mwCtxBound
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ mwCtxBound t :=
  safeStepCtxComplexityPackage_length_le_mwCtxBound P

/-- The final catalog projects the contextual size-based bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_length_bounded_by_size
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ complexity_bound (termSize t) :=
  safeStepCtxComplexityPackage_length_bounded_by_size P

/-- The final catalog projects the contextual fast-growing envelope bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ fgOmegaEnvelope (termSize t) :=
  safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope P

/-- The final catalog projects exact code equality for the realized context source endpoint. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_source_code_eq_iff_eq
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u)
    {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.chainPackage.sourceMember =
        traceRealizableCarrierRealization.code x ↔
      P.chainPackage.sourceMember = x :=
  safeStepCtxComplexityPackage_source_code_eq_iff_eq P

/-- The final catalog projects exact order for the realized context source endpoint. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_source_order_iff
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.chainPackage.sourceMember x ↔
      traceRealizableCarrierRealization.code P.chainPackage.sourceMember <
        traceRealizableCarrierRealization.code x :=
  safeStepCtxComplexityPackage_source_order_iff P x

/-- The final catalog projects the realized context source upper bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_source_upper_bound
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    traceRealizableCarrierRealization.code P.chainPackage.sourceMember < fullTripleLexBound :=
  safeStepCtxComplexityPackage_source_upper_bound P

/-- The final catalog projects exact code equality for the realized context target endpoint. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_target_code_eq_iff_eq
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u)
    {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.chainPackage.targetMember =
        traceRealizableCarrierRealization.code x ↔
      P.chainPackage.targetMember = x :=
  safeStepCtxComplexityPackage_target_code_eq_iff_eq P

/-- The final catalog projects exact order for the realized context target endpoint. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_target_order_iff
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.chainPackage.targetMember x ↔
      traceRealizableCarrierRealization.code P.chainPackage.targetMember <
        traceRealizableCarrierRealization.code x :=
  safeStepCtxComplexityPackage_target_order_iff P x

/-- The final catalog projects the realized context target upper bound. -/
theorem final_catalog_projects_safeStepCtxComplexityPackage_target_upper_bound
    {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) :
    traceRealizableCarrierRealization.code P.chainPackage.targetMember < fullTripleLexBound :=
  safeStepCtxComplexityPackage_target_upper_bound P

/-- The final catalog projects exact code equality for recovered externalized-image points. -/
theorem final_catalog_projects_externalizedTraceImageRecovery_code_eq_iff_realizable_eq
    {K : Nat} (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImageRecovery_code_eq_iff_realizable_eq X

/-- The final catalog projects exact order for recovered externalized-image points. -/
theorem final_catalog_projects_externalizedTraceImageRecovery_order_iff_realizable_order
    {K : Nat} (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      traceRealizableCarrierRealization.order
        (externalizedTraceImageToRealizableCarrier X x)
        (externalizedTraceImageToRealizableCarrier X y) :=
  externalizedTraceImageRecovery_order_iff_realizable_order X x y

/-- The final catalog projects the realized-subtype upper bound for recovered externalized-image points. -/
theorem final_catalog_projects_externalizedTraceImageRecovery_upper_bound
    {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    traceRealizableCarrierRealization.code
        (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound :=
  externalizedTraceImageRecovery_upper_bound X x

/-- The final catalog projects the finite safe-trace certificate audit row list. -/
def final_catalog_projects_safeTraceCertificateAuditRows : List SafeTraceCertificateAuditRow :=
  safeTraceCertificateAuditRows

/-- The final catalog projects the finite audit row count. -/
theorem final_catalog_projects_safeTraceCertificateAuditRows_length :
    final_catalog_projects_safeTraceCertificateAuditRows.length = 8 :=
  safeTraceCertificateAuditRows_length

/-- The final catalog projects `NoDup` for the finite audit row list. -/
theorem final_catalog_projects_safeTraceCertificateAuditRows_nodup :
    final_catalog_projects_safeTraceCertificateAuditRows.Nodup :=
  safeTraceCertificateAuditRows_nodup

/-- The final catalog projects the audit-row membership criterion. -/
theorem final_catalog_projects_safeTraceCertificateAuditRows_mem_iff
    (row : SafeTraceCertificateAuditRow) :
    row ∈ final_catalog_projects_safeTraceCertificateAuditRows ↔
      row = .rootEndpoint ∨
      row = .contextChain ∨
      row = .externalizedImageRecovery ∨
      row = .realizedImageExactness ∨
      row = .fullCarrierObstruction ∨
      row = .contextExactDrop ∨
      row = .mwCtxBound ∨
      row = .fgEnvelopeBound :=
  safeTraceCertificateAuditRows_mem_iff row

/-- The final catalog projects completeness of the finite audit row list. -/
theorem final_catalog_projects_safeTraceCertificateAuditRows_complete
    (row : SafeTraceCertificateAuditRow) :
    row ∈ final_catalog_projects_safeTraceCertificateAuditRows :=
  safeTraceCertificateAuditRows_complete row

/-- The final catalog projects row-to-evidence projection for the finite audit list. -/
def final_catalog_projects_safeTraceCertificateAudit_row_projects_evidence
    (row : SafeTraceCertificateAuditRow)
    (hRow : row ∈ final_catalog_projects_safeTraceCertificateAuditRows) :
    SafeTraceCertificateAuditRowEvidence row :=
  safeTraceCertificateAudit_row_projects_evidence row hRow

/-- The final catalog projects catalog-to-evidence projection for the finite audit list. -/
def final_catalog_projects_certificate_audit_catalog_projects_evidence
    (row : SafeTraceCertificateAuditRow) :
    SafeTraceCertificateAuditRowEvidence row :=
  safeTraceCertificateAudit_catalog_projects_evidence
    final_catalog_projects_certificate_audit_catalog row

/-- The final catalog projects the finite safe-trace roadmap closeout row list. -/
def final_catalog_projects_safeTraceRoadmapCloseoutRows : List SafeTraceRoadmapCloseoutRow :=
  safeTraceRoadmapCloseoutRows

/-- The final catalog projects the finite closeout row count. -/
theorem final_catalog_projects_safeTraceRoadmapCloseoutRows_length :
    final_catalog_projects_safeTraceRoadmapCloseoutRows.length = 10 :=
  safeTraceRoadmapCloseoutRows_length

/-- The final catalog projects `NoDup` for the finite closeout row list. -/
theorem final_catalog_projects_safeTraceRoadmapCloseoutRows_nodup :
    final_catalog_projects_safeTraceRoadmapCloseoutRows.Nodup :=
  safeTraceRoadmapCloseoutRows_nodup

/-- The final catalog projects the closeout-row membership criterion. -/
theorem final_catalog_projects_safeTraceRoadmapCloseoutRows_mem_iff
    (row : SafeTraceRoadmapCloseoutRow) :
    row ∈ final_catalog_projects_safeTraceRoadmapCloseoutRows ↔
      row = .imageSubtypeExactness ∨
      row = .fullCarrierObstruction ∨
      row = .certificateBridge ∨
      row = .rootEndpointBounds ∨
      row = .contextExactDrop ∨
      row = .mwCtxBound ∨
      row = .fgEnvelopeBound ∨
      row = .externalizedImageRecovery ∨
      row = .certificateAudit ∨
      row = .rootApiExport :=
  safeTraceRoadmapCloseoutRows_mem_iff row

/-- The final catalog projects completeness of the finite closeout row list. -/
theorem final_catalog_projects_safeTraceRoadmapCloseoutRows_complete
    (row : SafeTraceRoadmapCloseoutRow) :
    row ∈ final_catalog_projects_safeTraceRoadmapCloseoutRows :=
  safeTraceRoadmapCloseoutRows_complete row

/-- The final catalog projects the closeout status attached to any finite closeout row. -/
def final_catalog_projects_safeTraceRoadmapCloseout_row_status
    (row : SafeTraceRoadmapCloseoutRow)
    (hRow : row ∈ final_catalog_projects_safeTraceRoadmapCloseoutRows) :
    SafeTraceRoadmapCloseoutStatus :=
  safeTraceRoadmapCloseout_row_status row hRow

/-- The final catalog projects row-to-evidence projection for the finite closeout list. -/
def final_catalog_projects_safeTraceRoadmapCloseout_row_projects_evidence
    (row : SafeTraceRoadmapCloseoutRow)
    (hRow : row ∈ final_catalog_projects_safeTraceRoadmapCloseoutRows) :
    SafeTraceRoadmapCloseoutRowEvidence row :=
  safeTraceRoadmapCloseout_row_projects_evidence row hRow

/-- The final catalog projects catalog-to-status projection for the finite closeout list. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_row_status
    (row : SafeTraceRoadmapCloseoutRow) :
    SafeTraceRoadmapCloseoutStatus :=
  safeTraceRoadmapCloseout_catalog_projects_row_status
    final_catalog_projects_roadmap_closeout_catalog row

/-- The final catalog projects catalog-to-evidence projection for the finite closeout list. -/
theorem final_catalog_projects_roadmap_closeout_catalog_projects_row_evidence
    (row : SafeTraceRoadmapCloseoutRow) :
    SafeTraceRoadmapCloseoutRowEvidence row :=
  safeTraceRoadmapCloseout_catalog_projects_row_evidence
    final_catalog_projects_roadmap_closeout_catalog row

/-- The final catalog projects the closeout image-subtype status object. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_image_subtype_status :
    TraceImageSubtypeStatus :=
  safeTraceRoadmapCloseout_catalog_projects_image_subtype_status
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects closeout exactness on the realized trace-image subtype. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_image_subtype_exactness :
    TraceRealizableCarrierExactnessPackage :=
  safeTraceRoadmapCloseout_catalog_projects_image_subtype_exactness
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout full-carrier obstruction. -/
theorem final_catalog_projects_roadmap_closeout_catalog_projects_full_carrier_obstruction :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  safeTraceRoadmapCloseout_catalog_projects_full_carrier_obstruction
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout certificate-bridge catalog. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_certificate_bridge_catalog :
    SafeTraceCertificateBridgeCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_certificate_bridge_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout complexity-bridge catalog. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_complexity_bridge_catalog :
    SafeTraceComplexityBridgeCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_complexity_bridge_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the certified root-endpoint bounds at closeout. -/
def final_catalog_projects_roadmap_closeout_catalog_projects_root_endpoint_bounds :
    SafeTraceRootEndpointBoundsEvidence :=
  safeTraceRoadmapCloseout_catalog_projects_root_endpoint_bounds
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects exact contextual drop at closeout. -/
def final_catalog_projects_roadmap_closeout_catalog_projects_context_exact_drop :
    SafeTraceContextExactDropEvidence :=
  safeTraceRoadmapCloseout_catalog_projects_context_exact_drop
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout MW contextual bound. -/
def final_catalog_projects_roadmap_closeout_catalog_projects_mw_ctx_bound :
    SafeTraceMWCtxBoundEvidence :=
  safeTraceRoadmapCloseout_catalog_projects_mw_ctx_bound
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout fast-growing contextual bound. -/
def final_catalog_projects_roadmap_closeout_catalog_projects_fg_envelope_bound :
    SafeTraceFGEnvelopeBoundEvidence :=
  safeTraceRoadmapCloseout_catalog_projects_fg_envelope_bound
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects closeout externalized-image recovery. -/
def final_catalog_projects_roadmap_closeout_catalog_projects_externalized_image_recovery :
    SafeTraceExternalizedRecoveryEvidence :=
  safeTraceRoadmapCloseout_catalog_projects_externalized_image_recovery
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the closeout certificate-audit catalog. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_certificate_audit_catalog :
    SafeTraceCertificateAuditCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_certificate_audit_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the theorem-backed root API export bundle. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_root_api_export :
    SafeTraceRootAPIExportBundle :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_export
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the trace-image subtype status through the root API export bundle. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_root_api_image_subtype_status :
    TraceImageSubtypeStatus :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_image_subtype_status
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the full-carrier obstruction through the root API export bundle. -/
theorem final_catalog_projects_roadmap_closeout_catalog_projects_root_api_full_carrier_obstruction :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_full_carrier_obstruction
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the certificate bridge through the root API export bundle. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_root_api_certificate_bridge_catalog :
    SafeTraceCertificateBridgeCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_certificate_bridge_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the complexity bridge through the root API export bundle. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_root_api_complexity_bridge_catalog :
    SafeTraceComplexityBridgeCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_complexity_bridge_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects the certificate audit through the root API export bundle. -/
noncomputable def final_catalog_projects_roadmap_closeout_catalog_projects_root_api_certificate_audit_catalog :
    SafeTraceCertificateAuditCatalog :=
  safeTraceRoadmapCloseout_catalog_projects_root_api_certificate_audit_catalog
    final_catalog_projects_roadmap_closeout_catalog

/-- The final catalog projects realization witnesses for the trace-image subtype. -/
theorem final_catalog_projects_trace_realizable_carrier_realizes
    (x : TraceRealizableCarrier) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = x.1 :=
  final_catalog_projects_trace_image_subtype_status.realizes x

/-- The final catalog projects faithful code equality on the trace-image subtype. -/
theorem final_catalog_projects_trace_realizable_carrier_code_eq_iff_eq
    {x y : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code x = traceRealizableCarrierRealization.code y ↔ x = y :=
  final_catalog_projects_trace_image_subtype_status.exactness.codeEqIffEq

/-- The final catalog projects exact order on the trace-image subtype. -/
theorem final_catalog_projects_trace_realizable_carrier_order_iff
    (x y : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order x y ↔
      traceRealizableCarrierRealization.code x < traceRealizableCarrierRealization.code y :=
  final_catalog_projects_trace_image_subtype_status.exactness.orderIff x y

/-- The final catalog projects the bound on trace-image subtype codes. -/
theorem final_catalog_projects_trace_realizable_carrier_upper_bound
    (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.code x < fullTripleLexBound :=
  final_catalog_projects_trace_image_subtype_status.exactness.imageUpperBound x

/-- The final catalog projects failure of full-carrier realizability. -/
theorem final_catalog_projects_not_every_fullTripleLexCarrier_trace_realizable :
    ¬ ∀ x : FullTripleLexCarrier, ∃ t : Trace, traceToFullTripleLexCarrier t = x :=
  final_catalog_projects_trace_image_subtype_status.fullCarrierNotRealizable

/-- The final catalog projects failure of surjectivity onto the full calibrated carrier. -/
theorem final_catalog_projects_traceToFullTripleLexCarrier_not_surjective :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  final_catalog_projects_trace_image_subtype_status.fullCarrierNotSurjective

/-- The final catalog projects the surjectivity hypothesis required for full-carrier exact order type. -/
theorem final_catalog_projects_trace_exact_order_type_requires_surjective
    (hPkg : TraceRealization.ExactOrderTypePackage traceRealization) :
    Function.Surjective traceToFullTripleLexCarrier :=
  final_catalog_projects_trace_image_subtype_status.fullCarrierExactOrderTypeRequiresSurjective hPkg

/-- The final catalog projects the zero-DM phase-`0` realizable family. -/
theorem final_catalog_projects_zeroDmPhaseZero_realizable
    (tauComponent : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = zeroDmPhaseZeroCarrier tauComponent :=
  final_catalog_projects_trace_image_range_status.zeroDmPhaseZeroRealizable tauComponent

/-- The final catalog projects the payload-tower phase-`0` realizable family. -/
theorem final_catalog_projects_payloadTowerPhaseZero_realizable
    (n slack : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = payloadTowerPhaseZeroCarrier n slack :=
  final_catalog_projects_trace_image_range_status.payloadTowerPhaseZeroRealizable n slack

/-- The final catalog projects the flagged-tower phase-`1` realizable family. -/
theorem final_catalog_projects_flaggedTowerPhaseOne_realizable
    (n slack : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = flaggedTowerPhaseOneCarrier n slack :=
  final_catalog_projects_trace_image_range_status.flaggedTowerPhaseOneRealizable n slack

/-- The final catalog projects the phase-`1` membership invariant `1 ∈ dmComponent`. -/
theorem final_catalog_projects_phaseOne_has_one
    {t : Trace} (hPhase : (traceToFullTripleLexCarrier t).phase = 1) :
    1 ∈ (traceToFullTripleLexCarrier t).dmComponent :=
  final_catalog_projects_trace_image_range_status.phaseOneHasOne hPhase

/-- The final catalog projects the blocked phase-`1` subfamily with no `1` in the DM component. -/
theorem final_catalog_projects_phaseOne_without_one_blocked
    {x : FullTripleLexCarrier} (hPhase : x.phase = 1) (hMissing : 1 ∉ x.dmComponent) :
    ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = x :=
  final_catalog_projects_trace_image_range_status.phaseOneWithoutOneBlocked hPhase hMissing

/-- The final catalog projects the blocked phase-`1`, zero-DM subfamily. -/
theorem final_catalog_projects_phaseOne_zero_dm_blocked
    (tauComponent : Nat) :
    ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = phaseOneZeroDmCarrier tauComponent :=
  final_catalog_projects_trace_image_range_status.phaseOneZeroDmBlocked tauComponent

/-- The final catalog projects the zero-DM phase-`0` code-to-carrier exactness transport. -/
theorem final_catalog_projects_zeroDmPhaseZero_code_carrier_eq
    {a b : Nat} :
    zeroDmPhaseZeroRealization.code a = zeroDmPhaseZeroRealization.code b ↔
      zeroDmPhaseZeroCarrier a = zeroDmPhaseZeroCarrier b :=
  safe_trace_triple_lex_exactness_final_catalog.zeroDmPhaseZeroCodeCarrierEq

/-- The final catalog projects the zero-DM phase-`0` order transport. -/
theorem final_catalog_projects_zeroDmPhaseZero_order_iff
    (a b : Nat) :
    zeroDmPhaseZeroRealization.order a b ↔
      zeroDmPhaseZeroRealization.code a < zeroDmPhaseZeroRealization.code b :=
  safe_trace_triple_lex_exactness_final_catalog.zeroDmPhaseZeroOrderIff a b

/-- The final catalog projects the zero-DM phase-`0` image bound. -/
theorem final_catalog_projects_zeroDmPhaseZero_upper_bound
    (a : Nat) :
    zeroDmPhaseZeroRealization.code a < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.zeroDmPhaseZeroUpperBound a

/-- The final catalog projects the payload-tower phase-`0` code-to-carrier transport. -/
theorem final_catalog_projects_payloadTowerPhaseZero_code_carrier_eq
    {a b : Nat × Nat} :
    payloadTowerPhaseZeroRealization.code a = payloadTowerPhaseZeroRealization.code b ↔
      payloadTowerPhaseZeroCarrier a.1 a.2 = payloadTowerPhaseZeroCarrier b.1 b.2 :=
  safe_trace_triple_lex_exactness_final_catalog.payloadTowerPhaseZeroCodeCarrierEq

/-- The final catalog projects the payload-tower phase-`0` order transport. -/
theorem final_catalog_projects_payloadTowerPhaseZero_order_iff
    (a b : Nat × Nat) :
    payloadTowerPhaseZeroRealization.order a b ↔
      payloadTowerPhaseZeroRealization.code a < payloadTowerPhaseZeroRealization.code b :=
  safe_trace_triple_lex_exactness_final_catalog.payloadTowerPhaseZeroOrderIff a b

/-- The final catalog projects the payload-tower phase-`0` image bound. -/
theorem final_catalog_projects_payloadTowerPhaseZero_upper_bound
    (a : Nat × Nat) :
    payloadTowerPhaseZeroRealization.code a < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.payloadTowerPhaseZeroUpperBound a

/-- The final catalog projects the flagged-tower phase-`1` code-to-carrier transport. -/
theorem final_catalog_projects_flaggedTowerPhaseOne_code_carrier_eq
    {a b : Nat × Nat} :
    flaggedTowerPhaseOneRealization.code a = flaggedTowerPhaseOneRealization.code b ↔
      flaggedTowerPhaseOneCarrier a.1 a.2 = flaggedTowerPhaseOneCarrier b.1 b.2 :=
  safe_trace_triple_lex_exactness_final_catalog.flaggedTowerPhaseOneCodeCarrierEq

/-- The final catalog projects the flagged-tower phase-`1` order transport. -/
theorem final_catalog_projects_flaggedTowerPhaseOne_order_iff
    (a b : Nat × Nat) :
    flaggedTowerPhaseOneRealization.order a b ↔
      flaggedTowerPhaseOneRealization.code a < flaggedTowerPhaseOneRealization.code b :=
  safe_trace_triple_lex_exactness_final_catalog.flaggedTowerPhaseOneOrderIff a b

/-- The final catalog projects the flagged-tower phase-`1` image bound. -/
theorem final_catalog_projects_flaggedTowerPhaseOne_upper_bound
    (a : Nat × Nat) :
    flaggedTowerPhaseOneRealization.code a < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.flaggedTowerPhaseOneUpperBound a

/-- The final catalog projects the primitive-image code-to-carrier equality criterion. -/
theorem final_catalog_projects_primitive_image_code_carrier_eq
    {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      primitiveTraceImageRealization.toCarrier x = primitiveTraceImageRealization.toCarrier y :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageCodeCarrierEq

/-- The final catalog projects the primitive-image code-to-`mu3c` equality criterion. -/
theorem final_catalog_projects_primitive_image_code_mu3c_eq
    {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      mu3c x.1 = mu3c y.1 :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageCodeMu3cEq

/-- The final catalog projects primitive-image order exactness. -/
theorem final_catalog_projects_primitive_image_order_iff
    (x y : PrimitiveTraceImage) :
    primitiveTraceImageRealization.order x y ↔
      primitiveTraceImageRealization.code x < primitiveTraceImageRealization.code y :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageOrderIff x y

/-- The final catalog projects the primitive-image bound. -/
theorem final_catalog_projects_primitive_image_upper_bound
    (x : PrimitiveTraceImage) :
    primitiveTraceImageRealization.code x < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageUpperBound x

/-- The final catalog projects the primitive-image faithfulness obstruction. -/
noncomputable def final_catalog_projects_primitive_image_faithfulness_boundary :
    CarrierFaithfulnessObstruction primitiveTraceImageRealization :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageFaithfulnessBoundary

/-- The final catalog projects failure of primitive-image carrier injectivity. -/
theorem final_catalog_projects_primitive_image_carrier_not_injective :
    ¬ Function.Injective primitiveTraceImageRealization.toCarrier :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageCarrierNotInjective

/-- The final catalog projects failure of primitive-image code injectivity. -/
theorem final_catalog_projects_primitive_image_code_not_injective :
    ¬ Function.Injective primitiveTraceImageRealization.code :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageCodeNotInjective

/-- The final catalog projects the primitive-image exact-order transport theorem. -/
theorem final_catalog_projects_primitive_image_exact_order_type_of_surjective
    (hSurj : Function.Surjective primitiveTraceImageRealization.toCarrier) :
    TraceRealization.ExactOrderTypePackage primitiveTraceImageRealization :=
  safe_trace_triple_lex_exactness_final_catalog.primitiveImageExactOrderType hSurj

/-- The final catalog projects the externalized-image code-to-carrier equality criterion. -/
theorem final_catalog_projects_externalized_image_code_carrier_eq
    {K : Nat} (X : ExternalizedTraceStorage K Trace)
    {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      (externalizedTraceImageRealization X).toCarrier x =
        (externalizedTraceImageRealization X).toCarrier y :=
  safe_trace_triple_lex_exactness_final_catalog.externalizedImageCodeCarrierEq X

/-- The final catalog projects the externalized-image code-to-`mu3c` equality criterion. -/
theorem final_catalog_projects_externalized_image_code_mu3c_eq
    {K : Nat} (X : ExternalizedTraceStorage K Trace)
    {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      mu3c x.1 = mu3c y.1 :=
  safe_trace_triple_lex_exactness_final_catalog.externalizedImageCodeMu3cEq X

/-- The final catalog projects externalized-image order exactness. -/
theorem final_catalog_projects_externalized_image_order_iff
    {K : Nat} (X : ExternalizedTraceStorage K Trace)
    (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      (externalizedTraceImageRealization X).code x <
        (externalizedTraceImageRealization X).code y :=
  safe_trace_triple_lex_exactness_final_catalog.externalizedImageOrderIff X x y

/-- The final catalog projects the externalized-image bound. -/
theorem final_catalog_projects_externalized_image_upper_bound
    {K : Nat} (X : ExternalizedTraceStorage K Trace)
    (x : X.imageCarrier) :
    (externalizedTraceImageRealization X).code x < fullTripleLexBound :=
  safe_trace_triple_lex_exactness_final_catalog.externalizedImageUpperBound X x

/-- The final catalog projects the externalized-image exact-order transport theorem. -/
theorem final_catalog_projects_externalized_image_exact_order_type_of_surjective
    {K : Nat} (X : ExternalizedTraceStorage K Trace)
    (hSurj : Function.Surjective (externalizedTraceImageRealization X).toCarrier) :
    TraceRealization.ExactOrderTypePackage (externalizedTraceImageRealization X) :=
  safe_trace_triple_lex_exactness_final_catalog.externalizedImageExactOrderType X hSurj

/-- The final catalog projects the generic exact-order-type transport theorem. -/
theorem final_catalog_projects_generic_exact_order_type_transport
    {α : Type} (R : TraceRealization α)
    (hSurj : Function.Surjective R.toCarrier) :
    TraceRealization.ExactOrderTypePackage R :=
  safe_trace_triple_lex_exactness_final_catalog.genericExactOrderTypeTransport R hSurj

end OperatorKO7.SafeTraceTripleLexExactnessFinalCatalog
