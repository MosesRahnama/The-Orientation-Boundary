import OperatorKO7.Meta.DM_TripleLexExactness
import OperatorKO7.Meta.ExternalizedTraceStorage
import OperatorKO7.Meta.FreeStepDuplicatingTraceBridge
import OperatorKO7.Meta.Mu3c_Image_LowerBound

/-!
# Safe-Trace Triple-Lex Exactness

This module transports the closed M3 exactness surface from the calibrated
binary-phase carrier to trace-like objects that realize into that carrier.

The key positive fact is that every KO7 `Trace` already yields a calibrated
carrier point via `mu3c = (deltaFlag, kappaM, tau)`, because `deltaFlag` is
binary. The negative fact is equally explicit: that code is not faithful to
ambient syntax in general, so object equality needs extra hypotheses.
-/

namespace OperatorKO7.SafeTraceTripleLexExactness

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- The ambient exact-order-type bound for the calibrated binary-phase carrier. -/
abbrev fullTripleLexBound : Ordinal := ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)

/-- A theorem-facing realization map from a trace-like object into the calibrated
binary-phase M3 carrier. -/
structure TraceRealization (α : Type) where
  toCarrier : α → FullTripleLexCarrier

namespace TraceRealization

variable {α : Type} (R : TraceRealization α)

/-- The ordinal code induced by the realized calibrated carrier point. -/
@[simp] noncomputable def code (x : α) : Ordinal :=
  lex3cToOrd (R.toCarrier x).toLex3cTuple

/-- The realized triple-lex order induced by the calibrated carrier point. -/
@[simp] def order (x y : α) : Prop :=
  Lex3c (R.toCarrier x).toLex3cTuple (R.toCarrier y).toLex3cTuple

theorem carrier_eq_of_code_eq {x y : α}
    (hEq : R.code x = R.code y) :
    R.toCarrier x = R.toCarrier y := by
  exact lex3cToOrd_injective_on_fullCarrier hEq

theorem code_eq_iff_carrier_eq {x y : α} :
    R.code x = R.code y ↔ R.toCarrier x = R.toCarrier y := by
  constructor
  · exact R.carrier_eq_of_code_eq
  · intro hEq
    simp [TraceRealization.code, hEq]

theorem code_injective_of_toCarrier_injective
    (hInj : Function.Injective R.toCarrier) :
    Function.Injective R.code := by
  intro x y hEq
  exact hInj (R.carrier_eq_of_code_eq hEq)

theorem code_eq_iff_eq_of_toCarrier_injective
    (hInj : Function.Injective R.toCarrier) {x y : α} :
    R.code x = R.code y ↔ x = y := by
  constructor
  · intro hEq
    exact (R.code_injective_of_toCarrier_injective hInj) hEq
  · intro hEq
    simp [hEq]

theorem order_reflects {x y : α}
    (hlt : R.code x < R.code y) :
    R.order x y := by
  simpa [TraceRealization.code, TraceRealization.order] using
    (full_triple_lex_order_reflects
      (x := R.toCarrier x)
      (y := R.toCarrier y)
      hlt)

theorem order_iff (x y : α) :
    R.order x y ↔ R.code x < R.code y := by
  simpa [TraceRealization.code, TraceRealization.order] using
    (full_triple_lex_exact_order_type.1 (R.toCarrier x) (R.toCarrier y))

theorem image_upper_bound (x : α) :
    R.code x < fullTripleLexBound := by
  simpa [TraceRealization.code, fullTripleLexBound] using
    full_triple_lex_image_upper_bound (R.toCarrier x)

theorem surjective_below_of_toCarrier_surjective
    (hSurj : Function.Surjective R.toCarrier)
    {β : Ordinal} (hβ : β < fullTripleLexBound) :
    ∃ x : α, R.code x = β := by
  rcases full_triple_lex_exact_order_type.2.2 β (by simpa [fullTripleLexBound] using hβ) with
    ⟨carrier, hCode⟩
  rcases hSurj carrier with ⟨x, rfl⟩
  exact ⟨x, hCode⟩

/-- Exact-order-type package for a realization whose carrier map is surjective
onto the full calibrated binary-phase carrier. -/
structure ExactOrderTypePackage (R : TraceRealization α) : Prop where
  orderIff : ∀ x y : α, R.order x y ↔ R.code x < R.code y
  imageUpperBound : ∀ x : α, R.code x < fullTripleLexBound
  surjectiveBelow : ∀ β < fullTripleLexBound, ∃ x : α, R.code x = β

theorem ExactOrderTypePackage.toCarrier_surjective
    {R : TraceRealization α} (hPkg : ExactOrderTypePackage R) :
    Function.Surjective R.toCarrier := by
  intro carrier
  let β := lex3cToOrd carrier.toLex3cTuple
  have hβ : β < fullTripleLexBound := by
    simpa [β, fullTripleLexBound] using full_triple_lex_image_upper_bound carrier
  rcases hPkg.surjectiveBelow β hβ with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact lex3cToOrd_injective_on_fullCarrier (by simpa [TraceRealization.code, β] using hx)

theorem exact_order_type_package_of_toCarrier_surjective
    (hSurj : Function.Surjective R.toCarrier) :
    ExactOrderTypePackage R := by
  refine ⟨R.order_iff, R.image_upper_bound, ?_⟩
  intro β hβ
  exact R.surjective_below_of_toCarrier_surjective hSurj hβ

end TraceRealization

/-- Explicit witness that a realization code can forget ambient syntax. -/
structure CarrierFaithfulnessObstruction {α : Type} (R : TraceRealization α) where
  left : α
  right : α
  distinct : left ≠ right
  sameCode : R.code left = R.code right

namespace CarrierFaithfulnessObstruction

variable {α : Type} {R : TraceRealization α}

theorem sameCarrier (O : CarrierFaithfulnessObstruction R) :
    R.toCarrier O.left = R.toCarrier O.right :=
  R.carrier_eq_of_code_eq O.sameCode

theorem not_toCarrier_injective (O : CarrierFaithfulnessObstruction R) :
    ¬ Function.Injective R.toCarrier := by
  intro hInj
  exact O.distinct (hInj O.sameCarrier)

theorem not_code_injective (O : CarrierFaithfulnessObstruction R) :
    ¬ Function.Injective R.code := by
  intro hInj
  exact O.distinct (hInj O.sameCode)

end CarrierFaithfulnessObstruction

/-- Every KO7 trace already realizes a calibrated binary-phase carrier point via
its computable triple measure `mu3c`. -/
@[simp] def traceToFullTripleLexCarrier (t : Trace) : FullTripleLexCarrier where
  phase := MetaSN_KO7.deltaFlag t
  dmComponent := MetaSN_DM.kappaM t
  tauComponent := tau t
  phase_le_one := by
    cases t <;> simp
    case recΔ b s n =>
      cases n <;> simp

@[simp] theorem traceToFullTripleLexCarrier_toLex3cTuple (t : Trace) :
    (traceToFullTripleLexCarrier t).toLex3cTuple = mu3c t := by
  simp [traceToFullTripleLexCarrier, mu3c]

/-- Build a carrier realization from any trace-valued map. -/
@[simp] def ofTraceMap {α : Type} (toTrace : α → Trace) : TraceRealization α where
  toCarrier := fun x => traceToFullTripleLexCarrier (toTrace x)

theorem ofTraceMap_code_eq_iff_mu3c_eq {α : Type} (toTrace : α → Trace)
    {x y : α} :
    (ofTraceMap toTrace).code x = (ofTraceMap toTrace).code y ↔
      mu3c (toTrace x) = mu3c (toTrace y) := by
  constructor
  · intro hEq
    simpa [ofTraceMap, traceToFullTripleLexCarrier_toLex3cTuple] using
      congrArg FullTripleLexCarrier.toLex3cTuple
        ((ofTraceMap toTrace).carrier_eq_of_code_eq hEq)
  · intro hEq
    simpa [TraceRealization.code, ofTraceMap] using congrArg lex3cToOrd hEq

/-- The ambient KO7 trace carrier itself realizes directly into the calibrated
binary-phase carrier. -/
@[simp] def traceRealization : TraceRealization Trace :=
  ofTraceMap id

/-- Equality of trace codes is exactly equality of the realized calibrated
carrier points. -/
theorem trace_code_eq_iff_carrier_eq {a b : Trace} :
    traceRealization.code a = traceRealization.code b ↔
      traceToFullTripleLexCarrier a = traceToFullTripleLexCarrier b :=
  traceRealization.code_eq_iff_carrier_eq

/-- Equality of trace codes is exactly equality of the underlying `mu3c` tuples. -/
theorem trace_code_eq_iff_mu3c_eq {a b : Trace} :
    traceRealization.code a = traceRealization.code b ↔ mu3c a = mu3c b := by
  constructor
  · intro hEq
    simpa [traceRealization, ofTraceMap, traceToFullTripleLexCarrier_toLex3cTuple] using
      congrArg FullTripleLexCarrier.toLex3cTuple
        (traceRealization.carrier_eq_of_code_eq hEq)
  · intro hEq
    simpa [TraceRealization.code, traceRealization, ofTraceMap] using congrArg lex3cToOrd hEq

/-- Trace codes reflect the realized triple-lex order. -/
theorem trace_order_reflects {a b : Trace}
    (hlt : traceRealization.code a < traceRealization.code b) :
    traceRealization.order a b :=
  traceRealization.order_reflects hlt

/-- The realized trace order is exactly the ordinal order on realized trace codes. -/
theorem trace_order_iff (a b : Trace) :
    traceRealization.order a b ↔ traceRealization.code a < traceRealization.code b :=
  traceRealization.order_iff a b

/-- Every trace code lands below the calibrated carrier bound. -/
theorem trace_image_upper_bound (t : Trace) :
    traceRealization.code t < fullTripleLexBound :=
  traceRealization.image_upper_bound t

/-- Full ambient-trace code faithfulness would mean the realized carrier code is
injective on KO7 syntax itself. This is the exact equality-strengthening that
fails for arbitrary traces. -/
def TraceCodeFaithful : Prop :=
  Function.Injective traceRealization.code

/-- Full ambient-trace exact order type needs one additional hypothesis beyond
realization and image exactness: surjectivity of the carrier realization onto
the calibrated binary-phase carrier. -/
def TraceExactOrderTypeResidual : Prop :=
  Function.Surjective traceRealization.toCarrier

/-- Explicit carrier point witnessing failure of ambient-trace surjectivity onto
the full calibrated binary-phase carrier. -/
def ambientTraceSurjectivityObstructionCarrier : FullTripleLexCarrier where
  phase := 1
  dmComponent := 0
  tauComponent := 0
  phase_le_one := by decide

theorem trace_dmComponent_ne_zero_of_phase_one {t : Trace}
    (hPhase : (traceToFullTripleLexCarrier t).phase = 1) :
    (traceToFullTripleLexCarrier t).dmComponent ≠ 0 := by
  cases t with
  | void => simp [traceToFullTripleLexCarrier] at hPhase
  | delta t => simp [traceToFullTripleLexCarrier] at hPhase
  | integrate t => simp [traceToFullTripleLexCarrier] at hPhase
  | merge a b => simp [traceToFullTripleLexCarrier] at hPhase
  | app a b => simp [traceToFullTripleLexCarrier] at hPhase
  | eqW a b => simp [traceToFullTripleLexCarrier] at hPhase
  | recΔ b s n =>
      cases n with
      | void => simp [traceToFullTripleLexCarrier] at hPhase
      | delta n => simp [traceToFullTripleLexCarrier, MetaSN_DM.kappaM]
      | integrate t => simp [traceToFullTripleLexCarrier] at hPhase
      | merge a b => simp [traceToFullTripleLexCarrier] at hPhase
      | app a b => simp [traceToFullTripleLexCarrier] at hPhase
      | recΔ b s n => simp [traceToFullTripleLexCarrier] at hPhase
      | eqW a b => simp [traceToFullTripleLexCarrier] at hPhase

theorem no_trace_realizes_ambientTraceSurjectivityObstructionCarrier :
    ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = ambientTraceSurjectivityObstructionCarrier := by
  intro h
  rcases h with ⟨t, ht⟩
  have hPhase : (traceToFullTripleLexCarrier t).phase = 1 := by
    simpa [ambientTraceSurjectivityObstructionCarrier] using
      congrArg FullTripleLexCarrier.phase ht
  have hDm : (traceToFullTripleLexCarrier t).dmComponent = 0 := by
    simpa [ambientTraceSurjectivityObstructionCarrier] using
      congrArg FullTripleLexCarrier.dmComponent ht
  exact trace_dmComponent_ne_zero_of_phase_one hPhase hDm

theorem trace_exact_order_type_residual_false :
    ¬ TraceExactOrderTypeResidual := by
  intro hSurj
  rcases hSurj ambientTraceSurjectivityObstructionCarrier with ⟨t, ht⟩
  exact no_trace_realizes_ambientTraceSurjectivityObstructionCarrier ⟨t, ht⟩

/-- The computable trace code is not faithful to full KO7 syntax: `void` and
`delta void` have the same code. -/
def traceFaithfulnessObstruction : CarrierFaithfulnessObstruction traceRealization where
  left := void
  right := delta void
  distinct := by
    intro hEq
    cases hEq
  sameCode := by
    simp [TraceRealization.code, traceRealization, ofTraceMap, traceToFullTripleLexCarrier]

/-- Concrete ambient-trace carrier-faithfulness obstruction used by the
LONG-37 SafeTrace closeout. -/
def concreteCarrierFaithfulnessObstruction :
    CarrierFaithfulnessObstruction traceRealization :=
  traceFaithfulnessObstruction

/-- Two distinct traces collide under the ambient carrier realization. -/
theorem exists_trace_carrier_collision :
    ∃ t1 t2 : Trace,
      t1 ≠ t2 ∧ traceRealization.toCarrier t1 = traceRealization.toCarrier t2 := by
  refine ⟨concreteCarrierFaithfulnessObstruction.left,
    concreteCarrierFaithfulnessObstruction.right,
    concreteCarrierFaithfulnessObstruction.distinct,
    concreteCarrierFaithfulnessObstruction.sameCarrier⟩

theorem trace_toCarrier_not_injective :
    ¬ Function.Injective traceRealization.toCarrier :=
  traceFaithfulnessObstruction.not_toCarrier_injective

theorem trace_code_not_injective :
    ¬ TraceCodeFaithful :=
  traceFaithfulnessObstruction.not_code_injective

theorem trace_no_exact_order_type_package :
    ¬ TraceRealization.ExactOrderTypePackage traceRealization := by
  intro hPkg
  exact trace_exact_order_type_residual_false hPkg.toCarrier_surjective

theorem trace_exact_order_type_of_surjective
    (hResidual : TraceExactOrderTypeResidual) :
    TraceRealization.ExactOrderTypePackage traceRealization :=
  traceRealization.exact_order_type_package_of_toCarrier_surjective hResidual

@[simp] def integrateChain : Nat → Trace → Trace
  | 0, t => t
  | n + 1, t => integrate (integrateChain n t)

@[simp] theorem kappaM_integrateChain (n : Nat) (t : Trace) :
    MetaSN_DM.kappaM (integrateChain n t) = MetaSN_DM.kappaM t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [integrateChain, ih]

@[simp] theorem tau_integrateChain (n : Nat) (t : Trace) :
    tau (integrateChain n t) = n + tau t := by
  induction n generalizing t with
  | zero => simp [integrateChain]
  | succ n ih =>
      simp [integrateChain, ih]
      omega

theorem deltaFlag_integrateChain_of_zero (n : Nat) {t : Trace}
    (hZero : MetaSN_KO7.deltaFlag t = 0) :
    MetaSN_KO7.deltaFlag (integrateChain n t) = 0 := by
  cases n with
  | zero => simpa [integrateChain] using hZero
  | succ n => simp [integrateChain]

/-- Phase-`0`, zero-DM carrier slice realized by iterated `integrate` over `void`. -/
def zeroDmPhaseZeroCarrier (tauComponent : Nat) : FullTripleLexCarrier where
  phase := 0
  dmComponent := 0
  tauComponent := tauComponent
  phase_le_one := by decide

/-- Phase-`1`, zero-DM carrier slice, used only as a blocked family witness. -/
def phaseOneZeroDmCarrier (tauComponent : Nat) : FullTripleLexCarrier where
  phase := 1
  dmComponent := 0
  tauComponent := tauComponent
  phase_le_one := by decide

/-- Phase-`0` payload-tower slice from the existing `mu3c` image lower-bound module,
with extra tau slack added by iterated `integrate`. -/
def payloadTowerPhaseZeroCarrier (n slack : Nat) : FullTripleLexCarrier where
  phase := 0
  dmComponent := kappaTower n
  tauComponent := 3 * (n + 1) + slack
  phase_le_one := by decide

/-- Phase-`1` flagged-tower slice from the existing `mu3c` image lower-bound module,
with extra tau slack added inside the base payload. -/
def flaggedTowerPhaseOneCarrier (n slack : Nat) : FullTripleLexCarrier where
  phase := 1
  dmComponent := 1 ::ₘ kappaTower n
  tauComponent := 3 * (n + 2) + slack
  phase_le_one := by decide

@[simp] def zeroDmPhaseZeroTrace (slack : Nat) : Trace :=
  integrateChain slack void

@[simp] def payloadTowerPhaseZeroTrace (n slack : Nat) : Trace :=
  integrateChain slack (payloadTower n)

@[simp] def flaggedTowerPhaseOneTrace (n slack : Nat) : Trace :=
  recΔ (integrateChain slack (payloadTower n)) void (delta void)

theorem fullTripleLexCarrier_eq_of_fields {x y : FullTripleLexCarrier}
    (hPhase : x.phase = y.phase)
    (hDm : x.dmComponent = y.dmComponent)
    (hTau : x.tauComponent = y.tauComponent) :
    x = y := by
  cases x with
  | mk phaseX dmX tauX hLeX =>
      cases y with
      | mk phaseY dmY tauY hLeY =>
          cases hPhase
          cases hDm
          cases hTau
          simp

@[simp] theorem traceToFullTripleLexCarrier_zeroDmPhaseZeroTrace (slack : Nat) :
    traceToFullTripleLexCarrier (zeroDmPhaseZeroTrace slack) = zeroDmPhaseZeroCarrier slack := by
  refine fullTripleLexCarrier_eq_of_fields ?_ ?_ ?_
  · simpa [traceToFullTripleLexCarrier, zeroDmPhaseZeroTrace, zeroDmPhaseZeroCarrier] using
      (deltaFlag_integrateChain_of_zero slack (t := void) (by simp))
  · simp [traceToFullTripleLexCarrier, zeroDmPhaseZeroTrace, zeroDmPhaseZeroCarrier]
  · simp [traceToFullTripleLexCarrier, zeroDmPhaseZeroTrace, zeroDmPhaseZeroCarrier,
      tau_integrateChain]

@[simp] theorem traceToFullTripleLexCarrier_payloadTowerPhaseZeroTrace
    (n slack : Nat) :
    traceToFullTripleLexCarrier (payloadTowerPhaseZeroTrace n slack) =
      payloadTowerPhaseZeroCarrier n slack := by
  refine fullTripleLexCarrier_eq_of_fields ?_ ?_ ?_
  · simpa [traceToFullTripleLexCarrier, payloadTowerPhaseZeroTrace,
      payloadTowerPhaseZeroCarrier] using
      (deltaFlag_integrateChain_of_zero slack (t := payloadTower n) (deltaFlag_payloadTower n))
  · simp [traceToFullTripleLexCarrier, payloadTowerPhaseZeroTrace,
      payloadTowerPhaseZeroCarrier]
  · simp [traceToFullTripleLexCarrier, payloadTowerPhaseZeroTrace,
      payloadTowerPhaseZeroCarrier, tau_integrateChain]
    omega

@[simp] theorem traceToFullTripleLexCarrier_flaggedTowerPhaseOneTrace
    (n slack : Nat) :
    traceToFullTripleLexCarrier (flaggedTowerPhaseOneTrace n slack) =
      flaggedTowerPhaseOneCarrier n slack := by
  refine fullTripleLexCarrier_eq_of_fields ?_ ?_ ?_
  · simp [traceToFullTripleLexCarrier, flaggedTowerPhaseOneTrace,
      flaggedTowerPhaseOneCarrier]
  · simp [traceToFullTripleLexCarrier, flaggedTowerPhaseOneTrace,
      flaggedTowerPhaseOneCarrier]
  · simp [traceToFullTripleLexCarrier, flaggedTowerPhaseOneTrace,
      flaggedTowerPhaseOneCarrier, tau_integrateChain]
    omega

theorem trace_realizes_zeroDmPhaseZeroCarrier (slack : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = zeroDmPhaseZeroCarrier slack := by
  exact ⟨zeroDmPhaseZeroTrace slack, traceToFullTripleLexCarrier_zeroDmPhaseZeroTrace slack⟩

theorem trace_realizes_payloadTowerPhaseZeroCarrier (n slack : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = payloadTowerPhaseZeroCarrier n slack := by
  exact ⟨payloadTowerPhaseZeroTrace n slack,
    traceToFullTripleLexCarrier_payloadTowerPhaseZeroTrace n slack⟩

theorem trace_realizes_flaggedTowerPhaseOneCarrier (n slack : Nat) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = flaggedTowerPhaseOneCarrier n slack := by
  exact ⟨flaggedTowerPhaseOneTrace n slack,
    traceToFullTripleLexCarrier_flaggedTowerPhaseOneTrace n slack⟩

theorem kappaM_has_one_of_deltaFlag_one {t : Trace}
    (hFlag : MetaSN_KO7.deltaFlag t = 1) :
    1 ∈ MetaSN_DM.kappaM t := by
  cases t with
  | void => simp at hFlag
  | delta t => simp at hFlag
  | integrate t => simp at hFlag
  | merge a b => simp at hFlag
  | app a b => simp at hFlag
  | eqW a b => simp at hFlag
  | recΔ b s n =>
      cases n with
      | delta n => simp [MetaSN_DM.kappaM]
      | void => simp at hFlag
      | integrate t => simp at hFlag
      | merge a b => simp at hFlag
      | app a b => simp at hFlag
      | recΔ b s n => simp at hFlag
      | eqW a b => simp at hFlag

theorem trace_dmComponent_has_one_of_phase_one {t : Trace}
    (hPhase : (traceToFullTripleLexCarrier t).phase = 1) :
    1 ∈ (traceToFullTripleLexCarrier t).dmComponent := by
  have hFlag : MetaSN_KO7.deltaFlag t = 1 := by
    simpa [traceToFullTripleLexCarrier] using hPhase
  have hKappa : 1 ∈ MetaSN_DM.kappaM t :=
    kappaM_has_one_of_deltaFlag_one hFlag
  simpa [traceToFullTripleLexCarrier] using hKappa

theorem no_trace_realizes_phase_one_without_one {x : FullTripleLexCarrier}
    (hPhase : x.phase = 1) (hMissing : 1 ∉ x.dmComponent) :
    ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = x := by
  intro h
  rcases h with ⟨t, ht⟩
  have hTracePhase : (traceToFullTripleLexCarrier t).phase = 1 := by
    cases ht
    exact hPhase
  have hTraceOne : 1 ∈ (traceToFullTripleLexCarrier t).dmComponent :=
    trace_dmComponent_has_one_of_phase_one hTracePhase
  have hxOne : 1 ∈ x.dmComponent := by
    cases ht
    exact hTraceOne
  exact hMissing hxOne

theorem no_trace_realizes_phaseOneZeroDmCarrier (tauComponent : Nat) :
    ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = phaseOneZeroDmCarrier tauComponent := by
  exact no_trace_realizes_phase_one_without_one rfl (by simp [phaseOneZeroDmCarrier])

/-- Theorem-visible status object for the currently proved ambient trace-image range:
three constructive realizable families and two blocked phase-`1` subfamilies. -/
structure TraceImageRangeStatus where
  zeroDmPhaseZeroRealizable :
    ∀ tauComponent : Nat,
      ∃ t : Trace, traceToFullTripleLexCarrier t = zeroDmPhaseZeroCarrier tauComponent
  payloadTowerPhaseZeroRealizable :
    ∀ n slack : Nat,
      ∃ t : Trace, traceToFullTripleLexCarrier t = payloadTowerPhaseZeroCarrier n slack
  flaggedTowerPhaseOneRealizable :
    ∀ n slack : Nat,
      ∃ t : Trace, traceToFullTripleLexCarrier t = flaggedTowerPhaseOneCarrier n slack
  phaseOneHasOne :
    ∀ {t : Trace}, (traceToFullTripleLexCarrier t).phase = 1 →
      1 ∈ (traceToFullTripleLexCarrier t).dmComponent
  phaseOneWithoutOneBlocked :
    ∀ {x : FullTripleLexCarrier}, x.phase = 1 → 1 ∉ x.dmComponent →
      ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = x
  phaseOneZeroDmBlocked :
    ∀ tauComponent : Nat,
      ¬ ∃ t : Trace, traceToFullTripleLexCarrier t = phaseOneZeroDmCarrier tauComponent

def traceImageRangeStatus : TraceImageRangeStatus := by
  refine ⟨trace_realizes_zeroDmPhaseZeroCarrier,
    trace_realizes_payloadTowerPhaseZeroCarrier,
    trace_realizes_flaggedTowerPhaseOneCarrier,
    ?_, ?_, no_trace_realizes_phaseOneZeroDmCarrier⟩
  · intro t hPhase
    exact trace_dmComponent_has_one_of_phase_one hPhase
  · intro x hPhase hMissing
    exact no_trace_realizes_phase_one_without_one hPhase hMissing

@[simp] def zeroDmPhaseZeroRealization : TraceRealization Nat :=
  ofTraceMap zeroDmPhaseZeroTrace

@[simp] def payloadTowerPhaseZeroRealization : TraceRealization (Nat × Nat) :=
  ofTraceMap (fun p => payloadTowerPhaseZeroTrace p.1 p.2)

@[simp] def flaggedTowerPhaseOneRealization : TraceRealization (Nat × Nat) :=
  ofTraceMap (fun p => flaggedTowerPhaseOneTrace p.1 p.2)

@[simp] theorem zeroDmPhaseZeroRealization_toCarrier (tauComponent : Nat) :
    zeroDmPhaseZeroRealization.toCarrier tauComponent = zeroDmPhaseZeroCarrier tauComponent :=
  traceToFullTripleLexCarrier_zeroDmPhaseZeroTrace tauComponent

@[simp] theorem payloadTowerPhaseZeroRealization_toCarrier (p : Nat × Nat) :
    payloadTowerPhaseZeroRealization.toCarrier p = payloadTowerPhaseZeroCarrier p.1 p.2 :=
  traceToFullTripleLexCarrier_payloadTowerPhaseZeroTrace p.1 p.2

@[simp] theorem flaggedTowerPhaseOneRealization_toCarrier (p : Nat × Nat) :
    flaggedTowerPhaseOneRealization.toCarrier p = flaggedTowerPhaseOneCarrier p.1 p.2 :=
  traceToFullTripleLexCarrier_flaggedTowerPhaseOneTrace p.1 p.2

theorem zeroDmPhaseZero_code_eq_iff_carrier_eq {a b : Nat} :
    zeroDmPhaseZeroRealization.code a = zeroDmPhaseZeroRealization.code b ↔
      zeroDmPhaseZeroCarrier a = zeroDmPhaseZeroCarrier b := by
  constructor
  · intro hEq
    calc
      zeroDmPhaseZeroCarrier a = zeroDmPhaseZeroRealization.toCarrier a := by
        symm
        exact zeroDmPhaseZeroRealization_toCarrier a
      _ = zeroDmPhaseZeroRealization.toCarrier b :=
        zeroDmPhaseZeroRealization.carrier_eq_of_code_eq hEq
      _ = zeroDmPhaseZeroCarrier b :=
        zeroDmPhaseZeroRealization_toCarrier b
  · intro hEq
    exact (zeroDmPhaseZeroRealization.code_eq_iff_carrier_eq).2 <|
      calc
        zeroDmPhaseZeroRealization.toCarrier a = zeroDmPhaseZeroCarrier a :=
          zeroDmPhaseZeroRealization_toCarrier a
        _ = zeroDmPhaseZeroCarrier b := hEq
        _ = zeroDmPhaseZeroRealization.toCarrier b := by
          symm
          exact zeroDmPhaseZeroRealization_toCarrier b

theorem zeroDmPhaseZero_order_iff (a b : Nat) :
    zeroDmPhaseZeroRealization.order a b ↔
      zeroDmPhaseZeroRealization.code a < zeroDmPhaseZeroRealization.code b :=
  zeroDmPhaseZeroRealization.order_iff a b

theorem zeroDmPhaseZero_image_upper_bound (tauComponent : Nat) :
    zeroDmPhaseZeroRealization.code tauComponent < fullTripleLexBound :=
  zeroDmPhaseZeroRealization.image_upper_bound tauComponent

theorem payloadTowerPhaseZero_code_eq_iff_carrier_eq {a b : Nat × Nat} :
    payloadTowerPhaseZeroRealization.code a = payloadTowerPhaseZeroRealization.code b ↔
      payloadTowerPhaseZeroCarrier a.1 a.2 = payloadTowerPhaseZeroCarrier b.1 b.2 := by
  constructor
  · intro hEq
    calc
      payloadTowerPhaseZeroCarrier a.1 a.2 = payloadTowerPhaseZeroRealization.toCarrier a := by
        symm
        exact payloadTowerPhaseZeroRealization_toCarrier a
      _ = payloadTowerPhaseZeroRealization.toCarrier b :=
        payloadTowerPhaseZeroRealization.carrier_eq_of_code_eq hEq
      _ = payloadTowerPhaseZeroCarrier b.1 b.2 :=
        payloadTowerPhaseZeroRealization_toCarrier b
  · intro hEq
    exact (payloadTowerPhaseZeroRealization.code_eq_iff_carrier_eq).2 <|
      calc
        payloadTowerPhaseZeroRealization.toCarrier a = payloadTowerPhaseZeroCarrier a.1 a.2 :=
          payloadTowerPhaseZeroRealization_toCarrier a
        _ = payloadTowerPhaseZeroCarrier b.1 b.2 := hEq
        _ = payloadTowerPhaseZeroRealization.toCarrier b := by
          symm
          exact payloadTowerPhaseZeroRealization_toCarrier b

theorem payloadTowerPhaseZero_order_iff (a b : Nat × Nat) :
    payloadTowerPhaseZeroRealization.order a b ↔
      payloadTowerPhaseZeroRealization.code a < payloadTowerPhaseZeroRealization.code b :=
  payloadTowerPhaseZeroRealization.order_iff a b

theorem payloadTowerPhaseZero_image_upper_bound (p : Nat × Nat) :
    payloadTowerPhaseZeroRealization.code p < fullTripleLexBound :=
  payloadTowerPhaseZeroRealization.image_upper_bound p

theorem flaggedTowerPhaseOne_code_eq_iff_carrier_eq {a b : Nat × Nat} :
    flaggedTowerPhaseOneRealization.code a = flaggedTowerPhaseOneRealization.code b ↔
      flaggedTowerPhaseOneCarrier a.1 a.2 = flaggedTowerPhaseOneCarrier b.1 b.2 := by
  constructor
  · intro hEq
    calc
      flaggedTowerPhaseOneCarrier a.1 a.2 = flaggedTowerPhaseOneRealization.toCarrier a := by
        symm
        exact flaggedTowerPhaseOneRealization_toCarrier a
      _ = flaggedTowerPhaseOneRealization.toCarrier b :=
        flaggedTowerPhaseOneRealization.carrier_eq_of_code_eq hEq
      _ = flaggedTowerPhaseOneCarrier b.1 b.2 :=
        flaggedTowerPhaseOneRealization_toCarrier b
  · intro hEq
    exact (flaggedTowerPhaseOneRealization.code_eq_iff_carrier_eq).2 <|
      calc
        flaggedTowerPhaseOneRealization.toCarrier a = flaggedTowerPhaseOneCarrier a.1 a.2 :=
          flaggedTowerPhaseOneRealization_toCarrier a
        _ = flaggedTowerPhaseOneCarrier b.1 b.2 := hEq
        _ = flaggedTowerPhaseOneRealization.toCarrier b := by
          symm
          exact flaggedTowerPhaseOneRealization_toCarrier b

theorem flaggedTowerPhaseOne_order_iff (a b : Nat × Nat) :
    flaggedTowerPhaseOneRealization.order a b ↔
      flaggedTowerPhaseOneRealization.code a < flaggedTowerPhaseOneRealization.code b :=
  flaggedTowerPhaseOneRealization.order_iff a b

theorem flaggedTowerPhaseOne_image_upper_bound (p : Nat × Nat) :
    flaggedTowerPhaseOneRealization.code p < fullTripleLexBound :=
  flaggedTowerPhaseOneRealization.image_upper_bound p

/-- The theorem-visible ambient trace image as a subtype of the full calibrated carrier. -/
abbrev TraceRealizableCarrier :=
  {x : FullTripleLexCarrier // ∃ t : Trace, traceToFullTripleLexCarrier t = x}

@[simp] theorem traceRealizableCarrier_realizes (x : TraceRealizableCarrier) :
    ∃ t : Trace, traceToFullTripleLexCarrier t = x.1 :=
  x.2

/-- The trace-realizable carrier subtype inherits the ambient carrier code by inclusion. -/
@[simp] def traceRealizableCarrierRealization : TraceRealization TraceRealizableCarrier where
  toCarrier := Subtype.val

theorem traceRealizableCarrier_toCarrier_injective :
    Function.Injective traceRealizableCarrierRealization.toCarrier := by
  intro x y hEq
  exact Subtype.ext hEq

/-- Honest exactness package for the realized carrier subtype: exact order and
faithful code on the image, without any claim of surjectivity onto the full carrier. -/
structure TraceRealizableCarrierExactnessPackage : Prop where
  codeEqIffEq :
    ∀ {x y : TraceRealizableCarrier},
      traceRealizableCarrierRealization.code x = traceRealizableCarrierRealization.code y ↔ x = y
  orderIff :
    ∀ x y : TraceRealizableCarrier,
      traceRealizableCarrierRealization.order x y ↔
        traceRealizableCarrierRealization.code x < traceRealizableCarrierRealization.code y
  imageUpperBound :
    ∀ x : TraceRealizableCarrier,
      traceRealizableCarrierRealization.code x < fullTripleLexBound

theorem traceRealizableCarrier_code_eq_iff_eq {x y : TraceRealizableCarrier} :
    traceRealizableCarrierRealization.code x = traceRealizableCarrierRealization.code y ↔ x = y :=
  traceRealizableCarrierRealization.code_eq_iff_eq_of_toCarrier_injective
    traceRealizableCarrier_toCarrier_injective

theorem traceRealizableCarrier_order_iff (x y : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.order x y ↔
      traceRealizableCarrierRealization.code x < traceRealizableCarrierRealization.code y :=
  traceRealizableCarrierRealization.order_iff x y

theorem traceRealizableCarrier_image_upper_bound (x : TraceRealizableCarrier) :
    traceRealizableCarrierRealization.code x < fullTripleLexBound :=
  traceRealizableCarrierRealization.image_upper_bound x

def traceRealizableCarrierExactnessPackage : TraceRealizableCarrierExactnessPackage :=
  ⟨traceRealizableCarrier_code_eq_iff_eq,
    traceRealizableCarrier_order_iff,
    traceRealizableCarrier_image_upper_bound⟩

theorem not_every_fullTripleLexCarrier_trace_realizable :
    ¬ ∀ x : FullTripleLexCarrier, ∃ t : Trace, traceToFullTripleLexCarrier t = x := by
  intro hAll
  exact no_trace_realizes_ambientTraceSurjectivityObstructionCarrier
    (hAll ambientTraceSurjectivityObstructionCarrier)

theorem traceToFullTripleLexCarrier_not_surjective :
    ¬ Function.Surjective traceToFullTripleLexCarrier := by
  simpa [TraceExactOrderTypeResidual, traceRealization, ofTraceMap] using
    trace_exact_order_type_residual_false

theorem trace_exact_order_type_package_requires_surjective
    (hPkg : TraceRealization.ExactOrderTypePackage traceRealization) :
    Function.Surjective traceToFullTripleLexCarrier := by
  simpa [traceRealization, ofTraceMap] using hPkg.toCarrier_surjective

/-- Theorem-visible companion to `TraceImageRangeStatus`: exactness on the realized
carrier image together with the explicit non-surjectivity obstruction on the full carrier. -/
structure TraceImageSubtypeStatus where
  realizes :
    ∀ x : TraceRealizableCarrier,
      ∃ t : Trace, traceToFullTripleLexCarrier t = x.1
  exactness : TraceRealizableCarrierExactnessPackage
  fullCarrierNotRealizable :
    ¬ ∀ x : FullTripleLexCarrier, ∃ t : Trace, traceToFullTripleLexCarrier t = x
  fullCarrierNotSurjective : ¬ Function.Surjective traceToFullTripleLexCarrier
  fullCarrierExactOrderTypeRequiresSurjective :
    TraceRealization.ExactOrderTypePackage traceRealization →
      Function.Surjective traceToFullTripleLexCarrier
  fullCarrierNoExactOrderTypePackage :
    ¬ TraceRealization.ExactOrderTypePackage traceRealization

def traceImageSubtypeStatus : TraceImageSubtypeStatus :=
  ⟨traceRealizableCarrier_realizes,
    traceRealizableCarrierExactnessPackage,
    not_every_fullTripleLexCarrier_trace_realizable,
    traceToFullTripleLexCarrier_not_surjective,
    trace_exact_order_type_package_requires_surjective,
    trace_no_exact_order_type_package⟩

/-- The primitive free-fragment image inside `Trace` realizes through the ambient
trace realization. -/
@[simp] def primitiveTraceImageRealization : TraceRealization PrimitiveTraceImage :=
  ofTraceMap Subtype.val

/-- Equality of primitive-image codes is exactly equality of the realized
calibrated carrier points. -/
theorem primitiveTraceImage_code_eq_iff_carrier_eq
    {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      primitiveTraceImageRealization.toCarrier x = primitiveTraceImageRealization.toCarrier y :=
  primitiveTraceImageRealization.code_eq_iff_carrier_eq

theorem primitiveTraceImage_code_eq_iff_mu3c_eq
    {x y : PrimitiveTraceImage} :
    primitiveTraceImageRealization.code x = primitiveTraceImageRealization.code y ↔
      mu3c x.1 = mu3c y.1 := by
  simpa [primitiveTraceImageRealization] using
    (ofTraceMap_code_eq_iff_mu3c_eq (toTrace := Subtype.val) (x := x) (y := y))

/-- Primitive-image traces inherit the realized triple-lex order equivalence. -/
theorem primitiveTraceImage_order_iff (x y : PrimitiveTraceImage) :
    primitiveTraceImageRealization.order x y ↔
      primitiveTraceImageRealization.code x < primitiveTraceImageRealization.code y :=
  primitiveTraceImageRealization.order_iff x y

/-- Primitive-image trace codes stay below the calibrated carrier bound. -/
theorem primitiveTraceImage_image_upper_bound (x : PrimitiveTraceImage) :
    primitiveTraceImageRealization.code x < fullTripleLexBound :=
  primitiveTraceImageRealization.image_upper_bound x

/-- The primitive image still does not make the code faithful: the embedded
primitive base and successor-base terms have the same realized code. -/
def primitiveTraceImageFaithfulnessObstruction :
    CarrierFaithfulnessObstruction primitiveTraceImageRealization where
  left := ofFreeTermToImage FreeTerm.base
  right := ofFreeTermToImage (FreeTerm.succ FreeTerm.base)
  distinct := by
    intro hEq
    have hVal :
        embedFreeTerm FreeTerm.base =
          embedFreeTerm (FreeTerm.succ FreeTerm.base) := by
      exact congrArg Subtype.val hEq
    have hTerm : FreeTerm.base = FreeTerm.succ FreeTerm.base :=
      embedFreeTerm_injective hVal
    cases hTerm
  sameCode := by
    simpa [primitiveTraceImageRealization, ofTraceMap] using
      traceFaithfulnessObstruction.sameCode

theorem primitiveTraceImage_code_not_injective :
    ¬ Function.Injective primitiveTraceImageRealization.code :=
  primitiveTraceImageFaithfulnessObstruction.not_code_injective

theorem primitiveTraceImage_toCarrier_not_injective :
    ¬ Function.Injective primitiveTraceImageRealization.toCarrier :=
  primitiveTraceImageFaithfulnessObstruction.not_toCarrier_injective

theorem primitiveTraceImage_exact_order_type_of_surjective
    (hSurj : Function.Surjective primitiveTraceImageRealization.toCarrier) :
    TraceRealization.ExactOrderTypePackage primitiveTraceImageRealization :=
  primitiveTraceImageRealization.exact_order_type_package_of_toCarrier_surjective hSurj

/-- Any externalized trace-storage image over the ambient KO7 `Trace` carrier
inherits the realized calibrated carrier surface pointwise. -/
@[simp] def externalizedTraceImageRealization {K : Nat}
    (X : ExternalizedTraceStorage K Trace) :
    TraceRealization X.imageCarrier :=
  ofTraceMap Subtype.val

theorem externalizedTraceImage_code_eq_iff_carrier_eq {K : Nat}
    (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      (externalizedTraceImageRealization X).toCarrier x =
        (externalizedTraceImageRealization X).toCarrier y :=
  (externalizedTraceImageRealization X).code_eq_iff_carrier_eq

theorem externalizedTraceImage_code_eq_iff_mu3c_eq {K : Nat}
    (X : ExternalizedTraceStorage K Trace) {x y : X.imageCarrier} :
    (externalizedTraceImageRealization X).code x =
        (externalizedTraceImageRealization X).code y ↔
      mu3c x.1 = mu3c y.1 := by
  simpa [externalizedTraceImageRealization] using
    (ofTraceMap_code_eq_iff_mu3c_eq (toTrace := Subtype.val) (x := x) (y := y))

/-- Externalized trace images inherit the realized triple-lex order equivalence. -/
theorem externalizedTraceImage_order_iff {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x y : X.imageCarrier) :
    (externalizedTraceImageRealization X).order x y ↔
      (externalizedTraceImageRealization X).code x <
        (externalizedTraceImageRealization X).code y :=
  (externalizedTraceImageRealization X).order_iff x y

/-- Externalized trace-image codes stay below the calibrated carrier bound. -/
theorem externalizedTraceImage_image_upper_bound {K : Nat}
    (X : ExternalizedTraceStorage K Trace) (x : X.imageCarrier) :
    (externalizedTraceImageRealization X).code x < fullTripleLexBound :=
  (externalizedTraceImageRealization X).image_upper_bound x

theorem externalizedTraceImage_exact_order_type_of_surjective {K : Nat}
    (X : ExternalizedTraceStorage K Trace)
    (hSurj : Function.Surjective (externalizedTraceImageRealization X).toCarrier) :
    TraceRealization.ExactOrderTypePackage (externalizedTraceImageRealization X) :=
  (externalizedTraceImageRealization X).exact_order_type_package_of_toCarrier_surjective hSurj

end OperatorKO7.SafeTraceTripleLexExactness
