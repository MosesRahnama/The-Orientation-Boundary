import OperatorKO7.Meta.UUET.ObservationInterface

set_option autoImplicit false

/-!
# UUET finite operational-completeness carrier (U-27)

This module formalizes the finite gate behind UUET Section 25. Operational
completeness is represented as a conjunction of self-reference detection,
bounded recursion, typed refusal, calibration, uncertainty estimation, and the
two boundary resolutions required for a terminal record.

It does not prove a solution to the halting problem, Godel incompleteness, or a
theory of consciousness. Those remain external or structural readings over this
finite gate.
-/

namespace OperatorKO7.Meta.UUET

/-- A finite record of the operational-completeness diagnostics. -/
structure OperationalCompletenessState where
  detectsSelfReference : Bool
  recursionBounded : Bool
  emitsTypedRefusal : Bool
  calibrated : Bool
  uncertaintyEstimated : Bool
  projectionLicensed : Bool
  projectionDeferred : Bool
  branchLicensed : Bool
  branchRefused : Bool
  deriving DecidableEq, Repr

/-- The orientation transaction is resolved by a projection license or a typed
deferral certificate. -/
def projectionResolved (s : OperationalCompletenessState) : Prop :=
  s.projectionLicensed = true ∨ s.projectionDeferred = true

/-- The distinction transaction is resolved by a branch license or a typed
branch refusal. -/
def branchResolved (s : OperationalCompletenessState) : Prop :=
  s.branchLicensed = true ∨ s.branchRefused = true

/-- A terminal record is licensed only when both boundary transactions are
resolved. -/
def terminalRecordLicensed (s : OperationalCompletenessState) : Prop :=
  projectionResolved s ∧ branchResolved s

/-- Finite operational completeness for the Section 25 diagnostic. -/
def operationallyComplete (s : OperationalCompletenessState) : Prop :=
  s.detectsSelfReference = true
    ∧ s.recursionBounded = true
    ∧ s.emitsTypedRefusal = true
    ∧ s.calibrated = true
    ∧ s.uncertaintyEstimated = true
    ∧ terminalRecordLicensed s

/-- A complete operational state resolves the projection transaction. -/
theorem operationallyComplete_projection_resolved
    {s : OperationalCompletenessState}
    (h : operationallyComplete s) :
    projectionResolved s := by
  unfold operationallyComplete terminalRecordLicensed at h
  exact h.2.2.2.2.2.1

/-- A complete operational state resolves the branch transaction. -/
theorem operationallyComplete_branch_resolved
    {s : OperationalCompletenessState}
    (h : operationallyComplete s) :
    branchResolved s := by
  unfold operationallyComplete terminalRecordLicensed at h
  exact h.2.2.2.2.2.2

/-- A complete operational state licenses terminal record formation. -/
theorem operationallyComplete_terminal_record_licensed
    {s : OperationalCompletenessState}
    (h : operationallyComplete s) :
    terminalRecordLicensed s := by
  unfold operationallyComplete at h
  exact h.2.2.2.2.2

/-- Projection-only resolution is not operational completeness, because the
branch transaction remains unresolved. -/
theorem projection_only_not_operationally_complete :
    ¬ operationallyComplete
      { detectsSelfReference := true
        recursionBounded := true
        emitsTypedRefusal := true
        calibrated := true
        uncertaintyEstimated := true
        projectionLicensed := true
        projectionDeferred := false
        branchLicensed := false
        branchRefused := false } := by
  intro h
  have hb := operationallyComplete_branch_resolved h
  unfold branchResolved at hb
  simp at hb

/-- Branch-only resolution is not operational completeness, because the
projection transaction remains unresolved. -/
theorem branch_only_not_operationally_complete :
    ¬ operationallyComplete
      { detectsSelfReference := true
        recursionBounded := true
        emitsTypedRefusal := true
        calibrated := true
        uncertaintyEstimated := true
        projectionLicensed := false
        projectionDeferred := false
        branchLicensed := true
        branchRefused := false } := by
  intro h
  have hp := operationallyComplete_projection_resolved h
  unfold projectionResolved at hp
  simp at hp

/-- The canonical finite complete state. -/
def canonicalOperationallyComplete : OperationalCompletenessState where
  detectsSelfReference := true
  recursionBounded := true
  emitsTypedRefusal := true
  calibrated := true
  uncertaintyEstimated := true
  projectionLicensed := true
  projectionDeferred := false
  branchLicensed := true
  branchRefused := false

/-- The canonical finite state is operationally complete. -/
theorem canonicalOperationallyComplete_complete :
    operationallyComplete canonicalOperationallyComplete := by
  unfold operationallyComplete terminalRecordLicensed projectionResolved branchResolved
    canonicalOperationallyComplete
  simp

/-- Normalized self-reference probe errors. -/
structure SelfReferenceErrorProfile where
  tokenError : ℚ
  confidenceError : ℚ
  timeError : ℚ
  stopError : ℚ
  capabilityError : ℚ
  deriving DecidableEq, Repr

/-- Nonnegative weights for the five probe families. -/
structure SelfReferenceWeights where
  tokenWeight : ℚ
  confidenceWeight : ℚ
  timeWeight : ℚ
  stopWeight : ℚ
  capabilityWeight : ℚ
  deriving DecidableEq, Repr

/-- The Section 25 finite self-reference completeness index. -/
def selfReferenceCompletenessIndex
    (w : SelfReferenceWeights)
    (e : SelfReferenceErrorProfile) : ℚ :=
  w.tokenWeight * e.tokenError
    + w.confidenceWeight * e.confidenceError
    + w.timeWeight * e.timeError
    + w.stopWeight * e.stopError
    + w.capabilityWeight * e.capabilityError

/-- The zero-error profile has zero self-reference index for every weight
profile. -/
theorem selfReferenceCompletenessIndex_zero_errors
    (w : SelfReferenceWeights) :
    selfReferenceCompletenessIndex w
      { tokenError := 0
        confidenceError := 0
        timeError := 0
        stopError := 0
        capabilityError := 0 } = 0 := by
  simp [selfReferenceCompletenessIndex]

/-- Nonnegative weights and nonnegative errors force a nonnegative finite index. -/
theorem selfReferenceCompletenessIndex_nonneg
    {w : SelfReferenceWeights}
    {e : SelfReferenceErrorProfile}
    (hwToken : 0 ≤ w.tokenWeight)
    (hwConf : 0 ≤ w.confidenceWeight)
    (hwTime : 0 ≤ w.timeWeight)
    (hwStop : 0 ≤ w.stopWeight)
    (hwCap : 0 ≤ w.capabilityWeight)
    (heToken : 0 ≤ e.tokenError)
    (heConf : 0 ≤ e.confidenceError)
    (heTime : 0 ≤ e.timeError)
    (heStop : 0 ≤ e.stopError)
    (heCap : 0 ≤ e.capabilityError) :
    0 ≤ selfReferenceCompletenessIndex w e := by
  unfold selfReferenceCompletenessIndex
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (mul_nonneg hwToken heToken) (mul_nonneg hwConf heConf))
        (mul_nonneg hwTime heTime))
      (mul_nonneg hwStop heStop))
    (mul_nonneg hwCap heCap)

/-- The finite operational-completeness carrier has concrete positive and
negative witnesses. -/
theorem operationalCompleteness_nonvacuous :
    operationallyComplete canonicalOperationallyComplete
      ∧ ¬ operationallyComplete
        { detectsSelfReference := true
          recursionBounded := true
          emitsTypedRefusal := true
          calibrated := true
          uncertaintyEstimated := true
          projectionLicensed := true
          projectionDeferred := false
          branchLicensed := false
          branchRefused := false }
      ∧ ¬ operationallyComplete
        { detectsSelfReference := true
          recursionBounded := true
          emitsTypedRefusal := true
          calibrated := true
          uncertaintyEstimated := true
          projectionLicensed := false
          projectionDeferred := false
          branchLicensed := true
          branchRefused := false }
      ∧ selfReferenceCompletenessIndex
        { tokenWeight := 1
          confidenceWeight := 1
          timeWeight := 1
          stopWeight := 1
          capabilityWeight := 1 }
        { tokenError := 0
          confidenceError := 0
          timeError := 0
          stopError := 0
          capabilityError := 0 } = 0 := by
  exact ⟨canonicalOperationallyComplete_complete,
    projection_only_not_operationally_complete,
    branch_only_not_operationally_complete,
    selfReferenceCompletenessIndex_zero_errors _⟩

#print axioms operationallyComplete_projection_resolved
#print axioms operationallyComplete_branch_resolved
#print axioms operationallyComplete_terminal_record_licensed
#print axioms projection_only_not_operationally_complete
#print axioms branch_only_not_operationally_complete
#print axioms canonicalOperationallyComplete_complete
#print axioms selfReferenceCompletenessIndex_zero_errors
#print axioms selfReferenceCompletenessIndex_nonneg
#print axioms operationalCompleteness_nonvacuous

end OperatorKO7.Meta.UUET
