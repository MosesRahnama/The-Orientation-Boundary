import OperatorKO7.Meta.SafeTrace_TripleLexExactness

/-!
# The order type of the ambient trace image

`Meta/SafeTrace_TripleLexExactness.lean` computes the exact order type of the trace-realizable
carrier and, separately, proves that the trace map is not surjective onto the full calibrated
carrier. What it leaves outside is the order type of the ambient image itself: the set of
calibrated carriers a trace actually realizes, ordered by the calibrated code.

This module closes that. The ambient image and the realizable carrier are the same set. Their code
orders are related by an actual `RelIso`, and therefore their `Ordinal.type` values are equal.
Codes are injective on the image and every code lies below `fullTripleLexBound`.

The residual the earlier module records stays exactly where it was. The image is not the full
carrier: `ambientTraceSurjectivityObstructionCarrier` is a calibrated carrier no trace realizes.
What is now proved is that this is the only gap, in the sense that everything the trace map does
reach is ordered exactly as the realizable carrier is.

Relation: the calibrated triple-lexicographic code on traces. Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.SafeTraceTripleLexExactness

open Ordinal
open OperatorKO7
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- The ambient image of the trace map inside the full calibrated carrier. -/
def AmbientTraceImage : Type :=
  {x : FullTripleLexCarrier // x ∈ Set.range traceToFullTripleLexCarrier}

/-- The ambient image and the realizable carrier are the same subtype. -/
def traceImageEquivRealizable : AmbientTraceImage ≃ TraceRealizableCarrier where
  toFun := fun x => ⟨x.1, x.2⟩
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The calibrated code on the ambient image. -/
noncomputable def ambientImageCode (x : AmbientTraceImage) : Ordinal :=
  traceRealizableCarrierRealization.code (traceImageEquivRealizable x)

/-- Comparing two members of the ambient image by
the calibrated code is comparing their images in the realizable carrier by the same code, so the
two carry the same order. -/
theorem traceImageOrder_iff_realizable (x y : AmbientTraceImage) :
    ambientImageCode x < ambientImageCode y ↔
      traceRealizableCarrierRealization.code (traceImageEquivRealizable x) <
        traceRealizableCarrierRealization.code (traceImageEquivRealizable y) :=
  Iff.rfl

/-- The code is injective on the ambient image, so the identification is faithful and not merely
monotone. -/
theorem ambientImageCode_injective : Function.Injective ambientImageCode := by
  intro x y hEq
  have h : traceImageEquivRealizable x = traceImageEquivRealizable y :=
    traceRealizableCarrier_code_eq_iff_eq.1 hEq
  exact traceImageEquivRealizable.injective h

/-- The code order on the ambient image. -/
def AmbientImageOrder (x y : AmbientTraceImage) : Prop :=
  ambientImageCode x < ambientImageCode y

/-- The code order on the trace-realizable carrier. -/
def RealizableCarrierOrder (x y : TraceRealizableCarrier) : Prop :=
  traceRealizableCarrierRealization.code x < traceRealizableCarrierRealization.code y

theorem realizableCarrierCode_injective :
    Function.Injective traceRealizableCarrierRealization.code := by
  intro x y h
  exact traceRealizableCarrier_code_eq_iff_eq.1 h

instance ambientImageOrder_isWellOrder : IsWellOrder AmbientTraceImage AmbientImageOrder where
  wf := InvImage.wf ambientImageCode Ordinal.lt_wf
  trans := by
    intro a b c hab hbc
    exact lt_trans hab hbc
  trichotomous := by
    intro a b
    rcases lt_trichotomy (ambientImageCode a) (ambientImageCode b) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (ambientImageCode_injective h))
    · exact Or.inr (Or.inr h)

instance realizableCarrierOrder_isWellOrder :
    IsWellOrder TraceRealizableCarrier RealizableCarrierOrder where
  wf := InvImage.wf traceRealizableCarrierRealization.code Ordinal.lt_wf
  trans := by
    intro a b c hab hbc
    exact lt_trans hab hbc
  trichotomous := by
    intro a b
    rcases lt_trichotomy (traceRealizableCarrierRealization.code a)
        (traceRealizableCarrierRealization.code b) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (realizableCarrierCode_injective h))
    · exact Or.inr (Or.inr h)

/-- The subtype identification is a genuine relation isomorphism, not merely an equivalence plus
an informal order claim. -/
noncomputable def traceImageOrderRelIso : AmbientImageOrder ≃r RealizableCarrierOrder where
  toEquiv := traceImageEquivRealizable
  map_rel_iff' := by
    intro x y
    rfl

/-- Every ambient-image code lies below the calibrated bound. -/
theorem ambientImageCode_lt_bound (x : AmbientTraceImage) :
    ambientImageCode x < fullTripleLexBound :=
  traceRealizableCarrier_image_upper_bound (traceImageEquivRealizable x)

/-- **The order type of the ambient trace image.** The actual ordinal order types of the ambient
image and the realizable carrier are equal. -/
theorem ambient_trace_image_order_type_eq_realizable :
    @Ordinal.type AmbientTraceImage AmbientImageOrder ambientImageOrder_isWellOrder =
      @Ordinal.type TraceRealizableCarrier RealizableCarrierOrder
        realizableCarrierOrder_isWellOrder :=
  traceImageOrderRelIso.ordinal_type_eq

/-- Complete image package: ordinal-type equality, code faithfulness, the calibrated upper bound,
and bijectivity of the underlying subtype identification. -/
theorem ambient_trace_image_exact_package :
    (@Ordinal.type AmbientTraceImage AmbientImageOrder ambientImageOrder_isWellOrder =
        @Ordinal.type TraceRealizableCarrier RealizableCarrierOrder
          realizableCarrierOrder_isWellOrder)
      ∧ Function.Injective ambientImageCode
      ∧ (∀ x : AmbientTraceImage, ambientImageCode x < fullTripleLexBound)
      ∧ Function.Bijective traceImageEquivRealizable :=
  ⟨ambient_trace_image_order_type_eq_realizable, ambientImageCode_injective,
    ambientImageCode_lt_bound, traceImageEquivRealizable.bijective⟩

/-- The residual stays where it was: the ambient image is not the whole calibrated carrier, and the
obstruction is the same compiled witness. -/
theorem ambient_trace_image_proper :
    ¬ Function.Surjective traceToFullTripleLexCarrier :=
  traceToFullTripleLexCarrier_not_surjective

end OperatorKO7.SafeTraceTripleLexExactness
