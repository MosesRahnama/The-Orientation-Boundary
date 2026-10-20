import OperatorKO7.Meta.SafeTrace_ComplexityBridge

namespace SafeTraceComplexityBridgeReach

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceComplexityBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open MetaSN_KO7

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

example {a b : OperatorKO7.Trace} (h : SafeStep a b) :
    0 < tau a :=
  safeStepEndpointComplexityPackage_tau_pos_of_source
    (safeStepEndpointComplexityPackage h)

example {a b u : OperatorKO7.Trace} {n : Nat} (h : SafeStep a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepEndpointComplexityPackage_root_length_le_mwRootBound
    (safeStepEndpointComplexityPackage h) hPow

example {n : Nat} {t u : OperatorKO7.Trace} (h : SafeStepCtxPow n t u) :
    n ≤ fgOmegaEnvelope (termSize t) :=
  safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope
    (safeStepCtxComplexityPackage h)

example {K : Nat} (X : ExternalizedTraceStorage K OperatorKO7.Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImageRecovery_code_eq_iff_realizable_eq X

noncomputable example : SafeTraceComplexityBridgeCatalog :=
  safe_trace_complexity_bridge_catalog

end SafeTraceComplexityBridgeReach
