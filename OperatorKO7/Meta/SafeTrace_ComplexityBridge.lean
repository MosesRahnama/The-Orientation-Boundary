import OperatorKO7.Meta.SafeTrace_CertificateBridge
import OperatorKO7.Meta.SafeStep_Complexity_MW_Root
import OperatorKO7.Meta.SafeStep_Complexity_MW_Ctx
import OperatorKO7.Meta.SafeStep_Complexity_MW_CtxExact
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal
import OperatorKO7.Meta.SafeStep_Complexity_FastGrowing

/-!
# Safe-Trace Complexity Bridge

This module upgrades the safe-trace certificate bridge to a theorem-facing
complexity surface. It packages the already-proved root and context bounds while
staying inside the realized image subtype and without asserting ambient-trace
surjectivity onto the full calibrated carrier.
-/

namespace OperatorKO7.SafeTraceComplexityBridge

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.OrdinalHierarchy
open OperatorKO7.Trace
open OperatorKO7.SafeTraceCertificateBridge
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open NONote
open MetaSN_KO7

/-- Theorem-visible root-endpoint complexity package over the safe-trace certificate bridge. -/
structure SafeStepEndpointComplexityPackage (a b : Trace) where
  endpointPackage : SafeStepEndpointPackage a b
  tauPos : 0 < tau a
  exactPredStep :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1)
  targetReprLeSourcePred :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1)))
  rootLengthLeTau :
    ∀ {u : Trace} {n : Nat}, SafeStepPow a n u → n ≤ tau a
  rootLengthLeMwRootBound :
    ∀ {u : Trace} {n : Nat}, SafeStepPow a n u → n ≤ mwRootBound a

/-- Canonical root-endpoint complexity package for a guarded root step. -/
def safeStepEndpointComplexityPackage {a b : Trace}
    (h : SafeStep a b) : SafeStepEndpointComplexityPackage a b := by
  let P := safeStepEndpointPackage h
  exact
    { endpointPackage := P
      tauPos := safeStepEndpoint_tau_pos_of_source P
      exactPredStep := safeStepEndpoint_source_exact_pred_step P
      targetReprLeSourcePred := safeStepEndpoint_target_repr_le_source_pred P
      rootLengthLeTau := by
        intro u n hPow
        exact safeStepEndpoint_root_length_le_tau P hPow
      rootLengthLeMwRootBound := by
        intro u n hPow
        exact safeStepEndpoint_root_length_le_mwRootBound P hPow }

/-- The root-endpoint complexity package projects positivity of the source `τ` tail. -/
theorem safeStepEndpointComplexityPackage_tau_pos_of_source {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    0 < tau a :=
  P.tauPos

/-- The root-endpoint complexity package projects one exact predecessor step. -/
theorem safeStepEndpointComplexityPackage_source_exact_pred_step {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1) :=
  P.exactPredStep

/-- The root-endpoint complexity package projects the target predecessor bound. -/
theorem safeStepEndpointComplexityPackage_target_repr_le_source_pred {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))) :=
  P.targetReprLeSourcePred

/-- The root-endpoint complexity package projects the `τ` bound for root chains. -/
theorem safeStepEndpointComplexityPackage_root_length_le_tau {a b u : Trace} {n : Nat}
    (P : SafeStepEndpointComplexityPackage a b) (hPow : SafeStepPow a n u) :
    n ≤ tau a :=
  P.rootLengthLeTau hPow

/-- The root-endpoint complexity package projects the MW root bound for root chains. -/
theorem safeStepEndpointComplexityPackage_root_length_le_mwRootBound
    {a b u : Trace} {n : Nat} (P : SafeStepEndpointComplexityPackage a b)
    (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  P.rootLengthLeMwRootBound hPow

/-- The source endpoint inherits exact code equality in the realized carrier subtype. -/
theorem safeStepEndpointComplexityPackage_source_code_eq_iff_eq {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.endpointPackage.sourceMember =
        traceRealizableCarrierRealization.code x ↔
      P.endpointPackage.sourceMember = x :=
  P.endpointPackage.exactness.codeEqIffEq
    (x := P.endpointPackage.sourceMember) (y := x)

/-- The source endpoint inherits exact order in the realized carrier subtype. -/
theorem safeStepEndpointComplexityPackage_source_order_iff {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.endpointPackage.sourceMember x ↔
      traceRealizableCarrierRealization.code P.endpointPackage.sourceMember <
        traceRealizableCarrierRealization.code x :=
  P.endpointPackage.exactness.orderIff P.endpointPackage.sourceMember x

/-- The source endpoint inherits the realized-carrier upper bound. -/
theorem safeStepEndpointComplexityPackage_source_upper_bound {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    traceRealizableCarrierRealization.code P.endpointPackage.sourceMember < fullTripleLexBound :=
  P.endpointPackage.exactness.imageUpperBound P.endpointPackage.sourceMember

/-- The target endpoint inherits exact code equality in the realized carrier subtype. -/
theorem safeStepEndpointComplexityPackage_target_code_eq_iff_eq {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.endpointPackage.targetMember =
        traceRealizableCarrierRealization.code x ↔
      P.endpointPackage.targetMember = x :=
  P.endpointPackage.exactness.codeEqIffEq
    (x := P.endpointPackage.targetMember) (y := x)

/-- The target endpoint inherits exact order in the realized carrier subtype. -/
theorem safeStepEndpointComplexityPackage_target_order_iff {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.endpointPackage.targetMember x ↔
      traceRealizableCarrierRealization.code P.endpointPackage.targetMember <
        traceRealizableCarrierRealization.code x :=
  P.endpointPackage.exactness.orderIff P.endpointPackage.targetMember x

/-- The target endpoint inherits the realized-carrier upper bound. -/
theorem safeStepEndpointComplexityPackage_target_upper_bound {a b : Trace}
    (P : SafeStepEndpointComplexityPackage a b) :
    traceRealizableCarrierRealization.code P.endpointPackage.targetMember < fullTripleLexBound :=
  P.endpointPackage.exactness.imageUpperBound P.endpointPackage.targetMember

/-- Theorem-visible context-chain complexity package over the safe-trace certificate bridge. -/
structure SafeStepCtxComplexityPackage (n : Nat) (t u : Trace) where
  chainPackage : SafeStepCtxChainPackage n t u
  ctxFuelAntitone : ctxFuel u ≤ ctxFuel t
  exactDrop :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
      (ctxExactNote u).1 (ctxFuel t - ctxFuel u)
  lengthLeCtxFuelDrop : n ≤ ctxFuel t - ctxFuel u
  lengthLeCtxFuel : n ≤ ctxFuel t
  lengthLeMwCtxBound : n ≤ mwCtxBound t
  lengthBoundedBySize : n ≤ complexity_bound (termSize t)
  lengthLeFgOmegaEnvelope : n ≤ fgOmegaEnvelope (termSize t)

/-- Canonical context-chain complexity package for an exact-length `SafeStepCtxPow` witness. -/
def safeStepCtxComplexityPackage {n : Nat} {t u : Trace}
    (h : SafeStepCtxPow n t u) : SafeStepCtxComplexityPackage n t u := by
  let P := safeStepCtxChainPackage h
  exact
    { chainPackage := P
      ctxFuelAntitone := safeStepCtxPow_ctxFuel_antitone t u n h
      exactDrop := by
        simpa using safeStepCtxPow_exact_drop (t := t) (u := u) (k := 0) h
      lengthLeCtxFuelDrop := safeStepCtx_length_le_ctxFuel_drop t u n h
      lengthLeCtxFuel := P.lengthLeCtxFuel
      lengthLeMwCtxBound := safeStepCtx_length_le_mwCtxBound t u n h
      lengthBoundedBySize := P.lengthBoundedBySize
      lengthLeFgOmegaEnvelope := safestep_length_bounded_by_fgOmegaEnvelope t u n h }

/-- The context-chain complexity package projects `ctxFuel` antitonicity. -/
theorem safeStepCtxComplexityPackage_ctxFuel_antitone {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    ctxFuel u ≤ ctxFuel t :=
  P.ctxFuelAntitone

/-- The context-chain complexity package projects exact contextual drop. -/
theorem safeStepCtxComplexityPackage_exact_drop {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    OperatorKO7.OrdinalHierarchy.ExactControlledPow
      (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
      (ctxExactNote u).1 (ctxFuel t - ctxFuel u) :=
  P.exactDrop

/-- The context-chain complexity package projects the contextual fuel-drop bound. -/
theorem safeStepCtxComplexityPackage_length_le_ctxFuel_drop {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ ctxFuel t - ctxFuel u :=
  P.lengthLeCtxFuelDrop

/-- The context-chain complexity package projects the ambient `ctxFuel` bound. -/
theorem safeStepCtxComplexityPackage_length_le_ctxFuel {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ ctxFuel t :=
  P.lengthLeCtxFuel

/-- The context-chain complexity package projects the MW contextual bound. -/
theorem safeStepCtxComplexityPackage_length_le_mwCtxBound {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ mwCtxBound t :=
  P.lengthLeMwCtxBound

/-- The context-chain complexity package projects the size-based bound. -/
theorem safeStepCtxComplexityPackage_length_bounded_by_size {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ complexity_bound (termSize t) :=
  P.lengthBoundedBySize

/-- The context-chain complexity package projects the fast-growing envelope bound. -/
theorem safeStepCtxComplexityPackage_length_le_fgOmegaEnvelope {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    n ≤ fgOmegaEnvelope (termSize t) :=
  P.lengthLeFgOmegaEnvelope

/-- The source context endpoint inherits exact code equality in the realized carrier subtype. -/
theorem safeStepCtxComplexityPackage_source_code_eq_iff_eq {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.chainPackage.sourceMember =
        traceRealizableCarrierRealization.code x ↔
      P.chainPackage.sourceMember = x :=
  traceRealizableCarrierExactnessPackage.codeEqIffEq
    (x := P.chainPackage.sourceMember) (y := x)

/-- The source context endpoint inherits exact order in the realized carrier subtype. -/
theorem safeStepCtxComplexityPackage_source_order_iff {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.chainPackage.sourceMember x ↔
      traceRealizableCarrierRealization.code P.chainPackage.sourceMember <
        traceRealizableCarrierRealization.code x :=
  traceRealizableCarrierExactnessPackage.orderIff P.chainPackage.sourceMember x

/-- The source context endpoint inherits the realized-carrier upper bound. -/
theorem safeStepCtxComplexityPackage_source_upper_bound {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    traceRealizableCarrierRealization.code P.chainPackage.sourceMember < fullTripleLexBound :=
  traceRealizableCarrierExactnessPackage.imageUpperBound P.chainPackage.sourceMember

/-- The target context endpoint inherits exact code equality in the realized carrier subtype. -/
theorem safeStepCtxComplexityPackage_target_code_eq_iff_eq {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) {x : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code P.chainPackage.targetMember =
        traceRealizableCarrierRealization.code x ↔
      P.chainPackage.targetMember = x :=
  traceRealizableCarrierExactnessPackage.codeEqIffEq
    (x := P.chainPackage.targetMember) (y := x)

/-- The target context endpoint inherits exact order in the realized carrier subtype. -/
theorem safeStepCtxComplexityPackage_target_order_iff {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order P.chainPackage.targetMember x ↔
      traceRealizableCarrierRealization.code P.chainPackage.targetMember <
        traceRealizableCarrierRealization.code x :=
  traceRealizableCarrierExactnessPackage.orderIff P.chainPackage.targetMember x

/-- The target context endpoint inherits the realized-carrier upper bound. -/
theorem safeStepCtxComplexityPackage_target_upper_bound {n : Nat} {t u : Trace}
    (P : SafeStepCtxComplexityPackage n t u) :
    traceRealizableCarrierRealization.code P.chainPackage.targetMember < fullTripleLexBound :=
  traceRealizableCarrierExactnessPackage.imageUpperBound P.chainPackage.targetMember

/-- Externalized-image recovery preserves exact code equality after realization. -/
theorem externalizedTraceImageRecovery_code_eq_iff_realizable_eq {K : Nat}
    (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y :=
  externalizedTraceImage_code_eq_iff_realizable_eq X

/-- Externalized-image recovery preserves order after realization. -/
theorem externalizedTraceImageRecovery_order_iff_realizable_order {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      traceRealizableCarrierRealization.order
        (externalizedTraceImageToRealizableCarrier X x)
        (externalizedTraceImageToRealizableCarrier X y) :=
  externalizedTraceImage_order_iff_realizable_order X x y

/-- Externalized-image recovery preserves the realized-carrier upper bound. -/
theorem externalizedTraceImageRecovery_upper_bound {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    traceRealizableCarrierRealization.code
        (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound :=
  externalizedTraceImage_realizable_upper_bound X x

/-- Final theorem-facing catalog for the safe-trace complexity bridge. -/
structure SafeTraceComplexityBridgeCatalog where
  safeStepEndpointComplexityPackage :
    ∀ {a b : Trace}, SafeStep a b → SafeStepEndpointComplexityPackage a b
  safeStepEndpointSourceCodeEqIffEq :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier},
      traceRealizableCarrierRealization.code P.endpointPackage.sourceMember =
          traceRealizableCarrierRealization.code x ↔
        P.endpointPackage.sourceMember = x
  safeStepEndpointSourceOrderIff :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier),
      traceRealizableCarrierRealization.order P.endpointPackage.sourceMember x ↔
        traceRealizableCarrierRealization.code P.endpointPackage.sourceMember <
          traceRealizableCarrierRealization.code x
  safeStepEndpointSourceUpperBound :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b),
      traceRealizableCarrierRealization.code P.endpointPackage.sourceMember < fullTripleLexBound
  safeStepEndpointTargetCodeEqIffEq :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) {x : TraceRealizableCarrier},
      traceRealizableCarrierRealization.code P.endpointPackage.targetMember =
          traceRealizableCarrierRealization.code x ↔
        P.endpointPackage.targetMember = x
  safeStepEndpointTargetOrderIff :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b) (x : TraceRealizableCarrier),
      traceRealizableCarrierRealization.order P.endpointPackage.targetMember x ↔
        traceRealizableCarrierRealization.code P.endpointPackage.targetMember <
          traceRealizableCarrierRealization.code x
  safeStepEndpointTargetUpperBound :
    ∀ {a b : Trace} (P : SafeStepEndpointComplexityPackage a b),
      traceRealizableCarrierRealization.code P.endpointPackage.targetMember < fullTripleLexBound
  safeStepCtxComplexityPackage :
    ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u → SafeStepCtxComplexityPackage n t u
  safeStepCtxSourceCodeEqIffEq :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) {x : TraceRealizableCarrier},
      traceRealizableCarrierRealization.code P.chainPackage.sourceMember =
          traceRealizableCarrierRealization.code x ↔
        P.chainPackage.sourceMember = x
  safeStepCtxSourceOrderIff :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier),
      traceRealizableCarrierRealization.order P.chainPackage.sourceMember x ↔
        traceRealizableCarrierRealization.code P.chainPackage.sourceMember <
          traceRealizableCarrierRealization.code x
  safeStepCtxSourceUpperBound :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u),
      traceRealizableCarrierRealization.code P.chainPackage.sourceMember < fullTripleLexBound
  safeStepCtxTargetCodeEqIffEq :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) {x : TraceRealizableCarrier},
      traceRealizableCarrierRealization.code P.chainPackage.targetMember =
          traceRealizableCarrierRealization.code x ↔
        P.chainPackage.targetMember = x
  safeStepCtxTargetOrderIff :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u) (x : TraceRealizableCarrier),
      traceRealizableCarrierRealization.order P.chainPackage.targetMember x ↔
        traceRealizableCarrierRealization.code P.chainPackage.targetMember <
          traceRealizableCarrierRealization.code x
  safeStepCtxTargetUpperBound :
    ∀ {n : Nat} {t u : Trace} (P : SafeStepCtxComplexityPackage n t u),
      traceRealizableCarrierRealization.code P.chainPackage.targetMember < fullTripleLexBound
  externalizedTraceImageToRealizableCarrier :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace), X.imageCarrier → TraceRealizableCarrier
  externalizedTraceImageToRealizableCarrierRealizes :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      ∃ t : Trace,
        traceToFullTripleLexCarrier t = (externalizedTraceImageToRealizableCarrier X x).1
  externalizedTraceImageRecoveryCodeEqIffRealizableEq :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier},
      (externalizedTraceImageRealization X).code x =
          (externalizedTraceImageRealization X).code y ↔
        externalizedTraceImageToRealizableCarrier X x =
          externalizedTraceImageToRealizableCarrier X y
  externalizedTraceImageRecoveryOrderIffRealizableOrder :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier),
      (externalizedTraceImageRealization X).order x y ↔
        traceRealizableCarrierRealization.order
          (externalizedTraceImageToRealizableCarrier X x)
          (externalizedTraceImageToRealizableCarrier X y)
  externalizedTraceImageRecoveryUpperBound :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      traceRealizableCarrierRealization.code
          (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound

/-- Canonical safe-trace complexity bridge catalog. -/
def safe_trace_complexity_bridge_catalog : SafeTraceComplexityBridgeCatalog where
  safeStepEndpointComplexityPackage := @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage
  safeStepEndpointSourceCodeEqIffEq :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_source_code_eq_iff_eq
  safeStepEndpointSourceOrderIff :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_source_order_iff
  safeStepEndpointSourceUpperBound :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_source_upper_bound
  safeStepEndpointTargetCodeEqIffEq :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_target_code_eq_iff_eq
  safeStepEndpointTargetOrderIff :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_target_order_iff
  safeStepEndpointTargetUpperBound :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepEndpointComplexityPackage_target_upper_bound
  safeStepCtxComplexityPackage := @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage
  safeStepCtxSourceCodeEqIffEq :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_source_code_eq_iff_eq
  safeStepCtxSourceOrderIff :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_source_order_iff
  safeStepCtxSourceUpperBound :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_source_upper_bound
  safeStepCtxTargetCodeEqIffEq :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_target_code_eq_iff_eq
  safeStepCtxTargetOrderIff :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_target_order_iff
  safeStepCtxTargetUpperBound :=
    @OperatorKO7.SafeTraceComplexityBridge.safeStepCtxComplexityPackage_target_upper_bound
  externalizedTraceImageToRealizableCarrier :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImageToRealizableCarrier
  externalizedTraceImageToRealizableCarrierRealizes :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImageToRealizableCarrier_realizes
  externalizedTraceImageRecoveryCodeEqIffRealizableEq :=
    @OperatorKO7.SafeTraceComplexityBridge.externalizedTraceImageRecovery_code_eq_iff_realizable_eq
  externalizedTraceImageRecoveryOrderIffRealizableOrder :=
    @OperatorKO7.SafeTraceComplexityBridge.externalizedTraceImageRecovery_order_iff_realizable_order
  externalizedTraceImageRecoveryUpperBound :=
    @OperatorKO7.SafeTraceComplexityBridge.externalizedTraceImageRecovery_upper_bound

end OperatorKO7.SafeTraceComplexityBridge
