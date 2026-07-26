import OperatorKO7.Meta.SafeTrace_TripleLexExactness
import OperatorKO7.Meta.SafeStep_Complexity_MW_Root
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Safe-Trace Certificate Bridge

This module reconnects the realized safe-trace image subtype to the existing
safe-step certificate stack. It packages theorem-backed endpoint and
context-chain facts without claiming surjectivity of ambient traces onto the
full calibrated carrier.
-/

namespace OperatorKO7.SafeTraceCertificateBridge

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.SafeTraceTripleLexExactness
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.OrdinalHierarchy
open NONote
open MetaSN_KO7

/-- Any ambient trace determines a theorem-visible point of the realized carrier subtype. -/
@[simp] def traceRealizableCarrierOfTrace (t : Trace) : TraceRealizableCarrier :=
  ⟨traceToFullTripleLexCarrier t, ⟨t, rfl⟩⟩

@[simp] theorem traceRealizableCarrierOfTrace_carrier (t : Trace) :
    (traceRealizableCarrierOfTrace t).1 = traceToFullTripleLexCarrier t :=
  rfl

/-- Theorem-visible endpoint package for a guarded root `SafeStep`. -/
structure SafeStepEndpointPackage (a b : Trace) where
  step : SafeStep a b
  sourceCarrier : FullTripleLexCarrier
  targetCarrier : FullTripleLexCarrier
  sourceMember : TraceRealizableCarrier
  targetMember : TraceRealizableCarrier
  sourceMemberCarrier : sourceMember.1 = sourceCarrier
  targetMemberCarrier : targetMember.1 = targetCarrier
  exactness : TraceRealizableCarrierExactnessPackage
  fullCarrierNotSurjective : ¬ Function.Surjective traceToFullTripleLexCarrier

/-- Canonical endpoint package attached to a guarded root `SafeStep`. -/
def safeStepEndpointPackage {a b : Trace} (h : SafeStep a b) : SafeStepEndpointPackage a b where
  step := h
  sourceCarrier := traceToFullTripleLexCarrier a
  targetCarrier := traceToFullTripleLexCarrier b
  sourceMember := traceRealizableCarrierOfTrace a
  targetMember := traceRealizableCarrierOfTrace b
  sourceMemberCarrier := rfl
  targetMemberCarrier := rfl
  exactness := traceRealizableCarrierExactnessPackage
  fullCarrierNotSurjective := traceToFullTripleLexCarrier_not_surjective

@[simp] theorem safeStepEndpointPackage_source_realizes {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = P.sourceCarrier := by
  rcases traceRealizableCarrier_realizes P.sourceMember with ⟨t, ht⟩
  exact ⟨t, ht.trans P.sourceMemberCarrier⟩

@[simp] theorem safeStepEndpointPackage_target_realizes {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = P.targetCarrier := by
  rcases traceRealizableCarrier_realizes P.targetMember with ⟨t, ht⟩
  exact ⟨t, ht.trans P.targetMemberCarrier⟩

/-- The endpoint package recovers positivity of the safe-step source tail. -/
theorem safeStepEndpoint_tau_pos_of_source {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    0 < tau a :=
  tau_pos_of_safeStep_source P.step

/-- The endpoint package recovers the explicit predecessor fundamental sequence. -/
theorem safeStepEndpoint_source_fundamentalSequence {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    (lex3Note (mu3c a)).1.fundamentalSequence =
      Sum.inl (some (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1) :=
  safeStep_source_fundamentalSequence P.step

/-- The endpoint package recovers one exact predecessor step on the note side. -/
theorem safeStepEndpoint_source_exact_pred_step {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    ExactControlledPow (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1) :=
  safeStep_source_exact_pred_step P.step

/-- The endpoint package recovers the certified root-target predecessor bound. -/
theorem safeStepEndpoint_target_repr_le_source_pred {a b : Trace}
    (P : SafeStepEndpointPackage a b) :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))) :=
  safeStep_target_repr_le_source_pred P.step

/-- Any root chain starting at the endpoint source is bounded by its finite `τ` tail. -/
theorem safeStepEndpoint_root_length_le_tau {a b u : Trace} {n : Nat}
    (_P : SafeStepEndpointPackage a b) (hPow : SafeStepPow a n u) :
    n ≤ tau a :=
  safeStepPow_length_le_tau hPow

/-- Any root chain starting at the endpoint source is bounded by the MW root certificate. -/
theorem safeStepEndpoint_root_length_le_mwRootBound {a b u : Trace} {n : Nat}
    (_P : SafeStepEndpointPackage a b) (hPow : SafeStepPow a n u) :
    n ≤ mwRootBound a :=
  safeStepPow_length_le_mwRootBound hPow

/-- Theorem-visible package for an exact-length `SafeStepCtxPow` chain. -/
structure SafeStepCtxChainPackage (n : Nat) (t u : Trace) where
  chain : SafeStepCtxPow n t u
  sourceMember : TraceRealizableCarrier
  targetMember : TraceRealizableCarrier
  sourceMemberCarrier : sourceMember.1 = traceToFullTripleLexCarrier t
  targetMemberCarrier : targetMember.1 = traceToFullTripleLexCarrier u
  lengthLeCtxFuel : n ≤ ctxFuel t
  lengthBoundedBySize : n ≤ complexity_bound (termSize t)

/-- Canonical context-chain package attached to an exact-length `SafeStepCtxPow` witness. -/
def safeStepCtxChainPackage {n : Nat} {t u : Trace}
    (h : SafeStepCtxPow n t u) : SafeStepCtxChainPackage n t u where
  chain := h
  sourceMember := traceRealizableCarrierOfTrace t
  targetMember := traceRealizableCarrierOfTrace u
  sourceMemberCarrier := rfl
  targetMemberCarrier := rfl
  lengthLeCtxFuel := safeStepCtx_length_le_ctxFuel t u n h
  lengthBoundedBySize := safestep_length_bounded_by_size t u n h

/-- Any externalized trace-image point canonically lands in the realized carrier subtype. -/
@[simp] def externalizedTraceImageToRealizableCarrier {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) : TraceRealizableCarrier :=
  ⟨(externalizedTraceImageRealization X).toCarrier x, ⟨x.1, rfl⟩⟩

@[simp] theorem externalizedTraceImageToRealizableCarrier_carrier {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    (externalizedTraceImageToRealizableCarrier X x).1 =
      (externalizedTraceImageRealization X).toCarrier x :=
  rfl

@[simp] theorem externalizedTraceImageToRealizableCarrier_realizes {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    ∃ t : Trace,
      traceToFullTripleLexCarrier t = (externalizedTraceImageToRealizableCarrier X x).1 :=
  traceRealizableCarrier_realizes (externalizedTraceImageToRealizableCarrier X x)

/-- Code equality on externalized image points is exactly equality after recovery into the
realized carrier subtype. -/
theorem externalizedTraceImage_code_eq_iff_realizable_eq {K : Nat}
    (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      externalizedTraceImageToRealizableCarrier X x =
        externalizedTraceImageToRealizableCarrier X y := by
  simpa [externalizedTraceImageToRealizableCarrier, externalizedTraceImageRealization,
      traceRealizableCarrierRealization] using
    (traceRealizableCarrier_code_eq_iff_eq
      (x := externalizedTraceImageToRealizableCarrier X x)
      (y := externalizedTraceImageToRealizableCarrier X y))

/-- The externalized-image order is unchanged after recovery into the realized carrier subtype. -/
theorem externalizedTraceImage_order_iff_realizable_order {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      traceRealizableCarrierRealization.order
        (externalizedTraceImageToRealizableCarrier X x)
        (externalizedTraceImageToRealizableCarrier X y) := by
  rfl

/-- Externalized-image points inherit the realized subtype bound after recovery. -/
theorem externalizedTraceImage_realizable_upper_bound {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    traceRealizableCarrierRealization.code
        (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound :=
  traceRealizableCarrier_image_upper_bound (externalizedTraceImageToRealizableCarrier X x)

/-- Final theorem-facing catalog for the safe-trace certificate bridge. -/
structure SafeTraceCertificateBridgeCatalog where
  safeStepEndpointPackage :
    ∀ {a b : Trace}, SafeStep a b → SafeStepEndpointPackage a b
  safeStepEndpointTauPos :
    ∀ {a b : Trace} (_P : SafeStepEndpointPackage a b), 0 < tau a
  safeStepEndpointSourceFundamentalSequence :
    ∀ {a b : Trace} (_P : SafeStepEndpointPackage a b),
      (lex3Note (mu3c a)).1.fundamentalSequence =
        Sum.inl (some (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1)
  safeStepEndpointSourceExactPredStep :
    ∀ {a b : Trace} (_P : SafeStepEndpointPackage a b),
      ExactControlledPow (lex3Note (mu3c a)).1 (ctxFuel a) 1
        (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1)
  safeStepEndpointTargetReprLeSourcePred :
    ∀ {a b : Trace} (_P : SafeStepEndpointPackage a b),
      NONote.repr (lex3Note (mu3c b)) ≤
        NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1)))
  safeStepEndpointRootLengthLeTau :
    ∀ {a b u : Trace} {n : Nat} (_P : SafeStepEndpointPackage a b),
      SafeStepPow a n u → n ≤ tau a
  safeStepEndpointRootLengthLeMwRootBound :
    ∀ {a b u : Trace} {n : Nat} (_P : SafeStepEndpointPackage a b),
      SafeStepPow a n u → n ≤ mwRootBound a
  safeStepCtxChainPackage :
    ∀ {n : Nat} {t u : Trace}, SafeStepCtxPow n t u → SafeStepCtxChainPackage n t u
  externalizedTraceImageToRealizableCarrier :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace), X.imageCarrier → TraceRealizableCarrier
  externalizedTraceImageToRealizableCarrierRealizes :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      ∃ t : Trace,
        traceToFullTripleLexCarrier t = (externalizedTraceImageToRealizableCarrier X x).1
  externalizedTraceImageCodeEqIffRealizableEq :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier},
      (externalizedTraceImageRealization X).code x =
          (externalizedTraceImageRealization X).code y ↔
        externalizedTraceImageToRealizableCarrier X x =
          externalizedTraceImageToRealizableCarrier X y
  externalizedTraceImageOrderIffRealizableOrder :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier),
      (externalizedTraceImageRealization X).order x y ↔
        traceRealizableCarrierRealization.order
          (externalizedTraceImageToRealizableCarrier X x)
          (externalizedTraceImageToRealizableCarrier X y)
  externalizedTraceImageRealizableUpperBound :
    ∀ {K : Nat} (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier),
      traceRealizableCarrierRealization.code
          (externalizedTraceImageToRealizableCarrier X x) < fullTripleLexBound

/-- Canonical safe-trace certificate-bridge catalog. -/
def safe_trace_certificate_bridge_catalog : SafeTraceCertificateBridgeCatalog where
  safeStepEndpointPackage := @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpointPackage
  safeStepEndpointTauPos := @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_tau_pos_of_source
  safeStepEndpointSourceFundamentalSequence :=
    @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_source_fundamentalSequence
  safeStepEndpointSourceExactPredStep :=
    @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_source_exact_pred_step
  safeStepEndpointTargetReprLeSourcePred :=
    @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_target_repr_le_source_pred
  safeStepEndpointRootLengthLeTau :=
    @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_root_length_le_tau
  safeStepEndpointRootLengthLeMwRootBound :=
    @OperatorKO7.SafeTraceCertificateBridge.safeStepEndpoint_root_length_le_mwRootBound
  safeStepCtxChainPackage := @OperatorKO7.SafeTraceCertificateBridge.safeStepCtxChainPackage
  externalizedTraceImageToRealizableCarrier :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImageToRealizableCarrier
  externalizedTraceImageToRealizableCarrierRealizes :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImageToRealizableCarrier_realizes
  externalizedTraceImageCodeEqIffRealizableEq :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImage_code_eq_iff_realizable_eq
  externalizedTraceImageOrderIffRealizableOrder :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImage_order_iff_realizable_order
  externalizedTraceImageRealizableUpperBound :=
    @OperatorKO7.SafeTraceCertificateBridge.externalizedTraceImage_realizable_upper_bound

end OperatorKO7.SafeTraceCertificateBridge
