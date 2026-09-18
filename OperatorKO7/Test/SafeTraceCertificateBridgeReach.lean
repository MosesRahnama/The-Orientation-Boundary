import OperatorKO7.Meta.SafeTrace_CertificateBridge

namespace SafeTraceCertificateBridgeReach

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open MetaSN_KO7

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
    n ≤ tau a :=
  safeStepEndpoint_root_length_le_tau (safeStepEndpointPackage h) hPow

example {a b u : OperatorKO7.Trace} {n : Nat} (h : SafeStep a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepEndpoint_root_length_le_mwRootBound (safeStepEndpointPackage h) hPow

example {n : Nat} {t u : OperatorKO7.Trace} (h : SafeStepCtxPow n t u) :
    n ≤ complexity_bound (termSize t) :=
  (safeStepCtxChainPackage h).lengthBoundedBySize

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) (x : X.imageCarrier) :
    ∃ t : OperatorKO7.Trace,
      traceToFullTripleLexCarrier t = (externalizedTraceImageToRealizableCarrier X x).1 :=
  externalizedTraceImageToRealizableCarrier_realizes X x

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImage_code_eq_iff_realizable_eq X

example : SafeTraceCertificateBridgeCatalog :=
  safe_trace_certificate_bridge_catalog

end SafeTraceCertificateBridgeReach
