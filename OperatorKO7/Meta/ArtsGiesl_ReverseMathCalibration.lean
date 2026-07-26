import OperatorKO7.Meta.ArtsGiesl_LowerBound

/-!
# Arts-Giesl calibration records

This module packages Arts-Giesl profile, evidence-status, and comparison
records. The proved propositions concern fields of those records and the
finite `FormalTheory` order. They do not formalize second-order principles,
reductions between principles, or an exact reverse-mathematical equivalence.
In particular, `CalibrationStatus.exact` and `EvidenceStatus.theoremLevel`
below are enum values stored in records, not independent proofs of the
mathematical calibration described by their labels.
-/

namespace OperatorKO7.ArtsGieslReverseMathCalibration

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister
open OperatorKO7.ArtsGieslUpperBound
open OperatorKO7.ArtsGieslLowerBound

/-- Profile record with the proposed target, registered upper and lower
packages, and conjectural status. The order fields compare only the registered
`FormalTheory` values. -/
noncomputable def artsGieslCurrentCalibration : ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslTheoremUpperBound
  lowerBound? := some artsGieslTheoremLowerBound
  targetLeUpper := artsGiesl_targetTheory_le_theoremUpperBound
  lowerLeTarget := artsGieslTheoremLowerBound_le_target
  status := CalibrationStatus.conjectural

@[simp] theorem artsGieslCurrentCalibration_status :
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural := rfl

@[simp] theorem artsGieslCurrentCalibration_target_theory :
    artsGieslCurrentCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslCurrentCalibration_target_ordinal :
    artsGieslCurrentCalibration.targetProfile.ordinalCeiling? = some omegaPowThree := rfl

/-- The calibration record's upper package carries the `theoremLevel` tag. -/
theorem artsGieslCurrentCalibration_has_theoremUpperBound :
    artsGieslCurrentCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel :=
  artsGieslTheoremUpperBound_status

/-- The calibration record's lower package carries the `theoremLevel` tag and
the coarse `RCA₀` plus `Π⁰₂` profile. -/
theorem artsGieslCurrentCalibration_has_theoremLowerBound :
    match artsGieslCurrentCalibration.lowerBound? with
    | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
    | none => False := by
  simp [artsGieslCurrentCalibration, artsGieslTheoremLowerBound_status]

/-- The recorded target ordinal `ω^3` is below the registered `ε₀` upper
benchmark. -/
theorem artsGieslCurrentCalibration_below_safe_measure :
    artsGieslCurrentCalibration.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ omegaPowThree < ko7SafeMeasureUpperBound.upper := by
  constructor
  · rfl
  · simpa [ko7SafeMeasureUpperBound] using omegaPowThree_lt_epsilon0

/-- The Arts-Giesl and SCT records use the same target theory and ordinal,
while the Arts-Giesl record remains tagged `conjectural`. -/
theorem artsGieslCurrentCalibration_matches_sct_reference :
    artsGieslCurrentCalibration.targetProfile.theory = sctExactCalibration.targetProfile.theory
      ∧ artsGieslCurrentCalibration.targetProfile.ordinalCeiling? =
          sctExactCalibration.targetProfile.ordinalCeiling?
      ∧ artsGieslCurrentCalibration.status = CalibrationStatus.conjectural := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Collect the calibration record's status, target theory, and evidence tags. -/
theorem artsGieslCurrentCalibration_supported :
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural
      ∧ artsGieslCurrentCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ artsGieslCurrentCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match artsGieslCurrentCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact artsGieslTheoremUpperBound_status
  · simp [artsGieslCurrentCalibration, artsGieslTheoremLowerBound_status]

/-- Metadata transfer record pairing the SCT calibration profile with a
constant-overhead cost-shape witness and target-labelled Arts-Giesl packages.

`ConstantOverheadTransformation` contains only a natural-number cost function
and its affine equation. It is not indexed by source and destination
principles, so this definition does not prove an Arts-Giesl/SCT reduction or
transfer reverse-mathematical strength. -/
noncomputable def artsGieslExactCalibrationTransferFromSct :
    ExactCalibrationTransfer.{0, 0, 0} sctPrincipleProfile artsGieslPrincipleProfile where
  sourceCalibration := sctExactCalibration
  sourceExact := rfl
  witnessTransport := agRecursorTransformation
  dstUpper := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "constant-overhead transfer of exact SCT upper target"
  }
  dstLower := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "constant-overhead transfer of exact SCT lower target"
  }
  upperMatchesSourceTarget := by
    rfl
  lowerMatchesSourceTarget := by
    rfl
  upperTheoremLevel := rfl
  lowerTheoremLevel := rfl

theorem artsGieslExactCalibrationTransferFromSct_supported :
    artsGieslExactCalibrationTransferFromSct.sourceCalibration.status =
        CalibrationStatus.exact
      ∧ artsGieslExactCalibrationTransferFromSct.witnessTransport.overhead =
          agLicenseOverhead
      ∧ artsGieslExactCalibrationTransferFromSct.dstUpper.evidenceStatus =
          EvidenceStatus.theoremLevel
      ∧ artsGieslExactCalibrationTransferFromSct.dstLower.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Compatibility metadata object.

Its `exact` status is inherited from supplied record fields, not from a
formalized proof that the Arts-Giesl soundness principle has reverse-
mathematical strength `RCA₀ + WO(ω^3)`. -/
noncomputable def artsGieslExactCalibration :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  ExactCalibrationTransfer.transferredCalibration.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct

/-- Record-field projection; this does not establish mathematical exactness. -/
@[simp] theorem quarantined_metadata_artsGieslExactCalibration_status :
    artsGieslExactCalibration.status = CalibrationStatus.exact := rfl

/-- Record-field summary; this does not establish mathematical exactness.
`artsGieslCurrentCalibration_supported` states the conjectural profile, while
`artsGiesl_exactCalibration_of_matching_bounds` and
`artsGiesl_exactCalibration_of_sharp_bounds` are conditional constructors. -/
theorem quarantined_metadata_artsGiesl_exactCalibration :
    let C := artsGieslExactCalibration
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Conditional profile-equality assumptions for matching both registered
bounds to the proposed `RCA₀ + WO(ω^3)` target. -/
structure ArtsGieslMatchingBounds where
  upperTheory :
    artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  upperOrdinal :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree
  lowerTheory :
    artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  lowerOrdinal :
    artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree

/-- The registered lower package has theory `RCA₀`, so it cannot satisfy the
matching-bounds record whose lower theory is `RCA₀ + WO(ω^3)`. -/
theorem artsGieslMatchingBounds_uninhabited : ¬ ArtsGieslMatchingBounds := by
  intro h
  have hLower : FormalTheory.RCA0 = FormalTheory.RCA0_WO_omega3 := by
    simpa [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile] using h.lowerTheory
  cases hLower

/-- Construct a calibration record from four supplied profile equalities. -/
noncomputable def artsGieslExactCalibrationOfMatchingBounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslTheoremUpperBound
  lowerBound? := some artsGieslTheoremLowerBound
  targetLeUpper := by
    let _ := hUpperTheory
    let _ := hUpperOrdinal
    exact artsGiesl_targetTheory_le_theoremUpperBound
  lowerLeTarget := by
    let _ := hLowerTheory
    let _ := hLowerOrdinal
    exact artsGieslTheoremLowerBound_le_target
  status := CalibrationStatus.exact

@[simp] theorem artsGieslExactCalibrationOfMatchingBounds_status
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    (artsGieslExactCalibrationOfMatchingBounds
      hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal).status =
        CalibrationStatus.exact := rfl

/-- Under the four profile-equality assumptions, collect the resulting record
fields and evidence tags. -/
theorem artsGiesl_exactCalibration_of_matching_bounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    let C := artsGieslExactCalibrationOfMatchingBounds
      hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact artsGieslTheoremUpperBound_status
  · simp [artsGieslExactCalibrationOfMatchingBounds, artsGieslTheoremLowerBound_status]

/-- Under the four profile-equality assumptions, construct a calibration
record whose status field is `exact`. -/
theorem artsGiesl_exactCalibration_exists_if_matching_bounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    ∃ C : ReverseMathCalibration artsGieslPrincipleProfile,
      C.status = CalibrationStatus.exact := by
  exact ⟨artsGieslExactCalibrationOfMatchingBounds
    hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal, rfl⟩

/-- Construct the same calibration record from a bundled matching-bounds
witness. -/
noncomputable def artsGieslExactCalibrationOfWitnessedMatchingBounds
    (h : ArtsGieslMatchingBounds) :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfMatchingBounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- The record built from a matching-bounds witness has status field `exact`. -/
@[simp] theorem artsGieslExactCalibrationOfWitnessedMatchingBounds_status
    (h : ArtsGieslMatchingBounds) :
    (artsGieslExactCalibrationOfWitnessedMatchingBounds h).status =
      CalibrationStatus.exact := rfl

/-- Collect the fields of the calibration record built from a bundled witness. -/
theorem artsGiesl_exactCalibration_of_witnessed_matching_bounds
    (h : ArtsGieslMatchingBounds) :
    let C := artsGieslExactCalibrationOfWitnessedMatchingBounds h
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  exact artsGiesl_exactCalibration_of_matching_bounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- A bundled matching-bounds witness yields a calibration record tagged
`exact`. -/
theorem artsGiesl_exactCalibration_exists_if_witnessed_matching_bounds
    (h : ArtsGieslMatchingBounds) :
    ∃ C : ReverseMathCalibration artsGieslPrincipleProfile,
      C.status = CalibrationStatus.exact := by
  exact artsGiesl_exactCalibration_exists_if_matching_bounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- Finite-register gap data: the lower theory differs from the target and the
target differs from the upper theory, with both registered order relations. -/
structure ArtsGieslTheoremBoundGap where
  lowerTheory : FormalTheory
  targetTheory : FormalTheory
  upperTheory : FormalTheory
  lowerLeTarget : lowerTheory ≤ targetTheory
  targetLeUpper : targetTheory ≤ upperTheory
  lowerNeTarget : lowerTheory ≠ targetTheory
  targetNeUpper : targetTheory ≠ upperTheory

/-- Instantiate the finite-register gap with `RCA₀`,
`RCA₀ + WO(ω^3)`, and `WO(ε₀)`. -/
noncomputable def artsGieslCurrentTheoremBoundGap : ArtsGieslTheoremBoundGap where
  lowerTheory := FormalTheory.RCA0
  targetTheory := FormalTheory.RCA0_WO_omega3
  upperTheory := FormalTheory.WO_epsilon0
  lowerLeTarget := by decide
  targetLeUpper := by decide
  lowerNeTarget := by decide
  targetNeUpper := by decide

/-- The registered lower and target theories are distinct enum values. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_lower_gap :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
      artsGieslCurrentTheoremBoundGap.targetTheory :=
  artsGieslCurrentTheoremBoundGap.lowerNeTarget

/-- The registered target and upper theories are distinct enum values. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_upper_gap :
    artsGieslCurrentTheoremBoundGap.targetTheory ≠
      artsGieslCurrentTheoremBoundGap.upperTheory :=
  artsGieslCurrentTheoremBoundGap.targetNeUpper

/-- The registered lower and upper packages do not equal the proposed target
in the finite theory register. -/
theorem artsGiesl_exactCalibration_still_requires_bound_sharpening :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremBoundGap.targetTheory ≠
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  exact ⟨artsGieslCurrentTheoremBoundGap_has_strict_lower_gap,
    artsGieslCurrentTheoremBoundGap_has_strict_upper_gap⟩

/-- The side-specific lower-gap record uses the same lower and target theory
values as the combined gap. -/
theorem artsGieslCurrentLowerGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.lowerTheory
      ∧ artsGieslCurrentTheoremLowerBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory := by
  constructor <;> rfl

/-- The side-specific upper-gap record uses the same target and upper theory
values as the combined gap. -/
theorem artsGieslCurrentUpperGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremUpperBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  constructor <;> rfl

/-- Pair an upper and lower target-profile package. The component structures
carry profile equalities and evidence-status equalities. -/
structure ArtsGieslSctSharpTransferPair where
  upper : ArtsGieslSctSharpUpperTransfer
  lower : ArtsGieslSctSharpLowerTransfer

/-- The registered AG/SCT alignment does not carry the `theoremLevel` tag. -/
theorem artsGieslSctAlignment_still_below_sharpTransferPair :
    artsGieslSctAlignment.evidenceStatus ≠ EvidenceStatus.theoremLevel := by
  exact artsGieslSctAlignment_not_theoremLevel

/-- Proposed target profile used by the conditional constructors below. -/
noncomputable def artsGieslExactTargetTheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

@[simp] theorem artsGieslExactTargetTheoryProfile_theory :
    artsGieslExactTargetTheoryProfile.theory = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslExactTargetTheoryProfile_ordinal :
    artsGieslExactTargetTheoryProfile.ordinalCeiling? = some omegaPowThree := rfl

/-- Construct a calibration record from upper and lower packages whose fields
equal `artsGieslExactTargetTheoryProfile` and carry the `theoremLevel` tag.
The component types encode only profile and status equalities; they do not
contain derivations of the underlying reverse-mathematical bounds. -/
noncomputable def artsGieslExactCalibrationOfSharpBounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := artsGieslExactTargetTheoryProfile
  upperBound := U.bound
  lowerBound? := some L.bound
  targetLeUpper := by
    rw [artsGieslExactTargetTheoryProfile_theory, U.theoryEq]
    decide
  lowerLeTarget := by
    simpa using (show L.bound.theoryProfile.theory ≤ FormalTheory.RCA0_WO_omega3 from by
      rw [L.theoryEq]
      decide)
  status := CalibrationStatus.exact

@[simp] theorem artsGieslExactCalibrationOfSharpBounds_status
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactCalibrationOfSharpBounds U L).status = CalibrationStatus.exact := rfl

/-- Record of a calibration together with target, bound-profile, and
evidence-status equalities. This structure contains no reduction or
second-order derivability field. -/
structure ArtsGieslExactTheoremCalibration where
  calibration : ReverseMathCalibration artsGieslPrincipleProfile
  targetTheory :
    calibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3
  targetOrdinal :
    calibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  upperTheory :
    calibration.upperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  upperOrdinal :
    calibration.upperBound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  upperTheoremLevel :
    calibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
  lowerBound :
    ∃ lb : ReverseMathLowerBound artsGieslPrincipleProfile,
      calibration.lowerBound? = some lb
        ∧ lb.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
        ∧ lb.theoryProfile.ordinalCeiling? =
            some OperatorKO7.ReverseMathSupport.omegaPowThree
        ∧ lb.evidenceStatus = EvidenceStatus.theoremLevel
  statusExact :
    calibration.status = CalibrationStatus.exact

/-- Assemble an `ArtsGieslExactTheoremCalibration` record from upper and lower
profile packages. -/
noncomputable def artsGieslExactTheoremCalibrationOfSharpBounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    ArtsGieslExactTheoremCalibration where
  calibration := artsGieslExactCalibrationOfSharpBounds U L
  targetTheory := rfl
  targetOrdinal := rfl
  upperTheory := U.theoryEq
  upperOrdinal := U.ordinalEq
  upperTheoremLevel := U.theoremLevel
  lowerBound := ⟨L.bound, rfl, L.theoryEq, L.ordinalEq, L.theoremLevel⟩
  statusExact := rfl

/-- Project the assembled calibration record's status field. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSharpBounds_status
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

/-- Assemble a calibration record from the two SCT-labelled profile packages. -/
noncomputable def artsGieslExactTheoremCalibrationOfSctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    T.upper.toSharpTheoremUpperBound
    T.lower.toSharpTheoremLowerBound

/-- Project the status field of the SCT-labelled assembly. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSctSharpTransfers_status
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- Extract the upper profile package from a calibration record. -/
noncomputable def ArtsGieslExactTheoremCalibration.toSharpUpperBound
    (C : ArtsGieslExactTheoremCalibration) :
    ArtsGieslSharpTheoremUpperBound where
  bound := C.calibration.upperBound
  theoryEq := C.upperTheory
  ordinalEq := C.upperOrdinal
  theoremLevel := C.upperTheoremLevel

/-- Extract the lower profile package from a calibration record. -/
noncomputable def ArtsGieslExactTheoremCalibration.toSharpLowerBound
    (C : ArtsGieslExactTheoremCalibration) :
    ArtsGieslSharpTheoremLowerBound := by
  let lb := Classical.choose C.lowerBound
  let h := Classical.choose_spec C.lowerBound
  refine
    { bound := lb
      theoryEq := h.2.1
      ordinalEq := ?_
      theoremLevel := h.2.2.2 }
  show lb.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  exact h.2.2.1

/-- The extracted upper package retains its evidence-status equality. -/
theorem ArtsGieslExactTheoremCalibration.toSharpUpperBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpUpperBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpUpperBound.theoremLevel

/-- The extracted lower package retains its evidence-status equality. -/
theorem ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpLowerBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpLowerBound.theoremLevel

/-- No calibration record satisfying the target-profile upper equalities can
reuse `artsGieslTheoremUpperBound`, whose registered theory differs from the
target. -/
theorem artsGiesl_noExactTheoremCalibration_with_current_upperBound :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound := by
  rintro ⟨C, hC⟩
  apply artsGieslTheoremUpperBound_not_sharp
  refine ⟨C.toSharpUpperBound, ?_⟩
  simpa [ArtsGieslExactTheoremCalibration.toSharpUpperBound] using hC

/-- No calibration record satisfying the target-profile lower equalities can
reuse `artsGieslTheoremLowerBound`, whose registered theory differs from the
target. -/
theorem artsGiesl_noExactTheoremCalibration_with_current_lowerBound :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.lowerBound? = some artsGieslTheoremLowerBound := by
  rintro ⟨C, hC⟩
  have hChoose :
      Classical.choose C.lowerBound = artsGieslTheoremLowerBound := by
    apply Option.some.inj
    rw [← (Classical.choose_spec C.lowerBound).1, hC]
  apply artsGieslTheoremLowerBound_not_sharp
  refine ⟨C.toSharpLowerBound, ?_⟩
  simp [ArtsGieslExactTheoremCalibration.toSharpLowerBound, hChoose]

/-- The two coarse registered packages cannot be the upper and lower fields of
a record satisfying the target-profile equalities. -/
theorem artsGiesl_currentTheoremPackages_do_not_yield_exactTheoremCalibration :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound
          ∧ C.calibration.lowerBound? = some artsGieslTheoremLowerBound := by
  rintro ⟨C, hUpper, _hLower⟩
  exact artsGiesl_noExactTheoremCalibration_with_current_upperBound ⟨C, hUpper⟩

/-- Compatibility metadata package assembled from the SCT-labelled transfer
record. Its status and evidence fields are inherited record values; this is not
a proof of an Arts-Giesl/SCT reduction or reverse-mathematical equivalence. -/
noncomputable def artsGieslExactTheoremCalibrationWitness :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer.{0, 0, 0}
      artsGieslExactCalibrationTransferFromSct
      (by rfl) (by rfl))
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer.{0, 0, 0}
      artsGieslExactCalibrationTransferFromSct
      (by rfl) (by rfl))

@[simp] theorem artsGieslExactTheoremCalibrationWitness_status :
    artsGieslExactTheoremCalibrationWitness.calibration.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactTheoremCalibration :
    artsGieslExactTheoremCalibrationWitness.calibration.status = CalibrationStatus.exact
      ∧ artsGieslExactTheoremCalibrationWitness.calibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslExactTheoremCalibrationWitness.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Any supplied pair of target-profile packages yields a calibration record
tagged `exact`. -/
theorem artsGiesl_exactTheoremCalibration_of_sctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- Convert an alignment metadata record into paired profile packages. -/
noncomputable def ArtsGieslSctSharpTransferPair.ofTheoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpTransferPair where
  upper := ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A
  lower := ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A

/-- Project the `exact` status assigned by the calibration constructor applied
to alignment-derived profile packages. -/
theorem artsGiesl_exactTheoremCalibration_of_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
      (ArtsGieslSctSharpTransferPair.ofTheoremAlignment A)).calibration.status =
        CalibrationStatus.exact := rfl

/-- Collect the status, profile, and evidence fields produced from two
target-profile packages. -/
theorem artsGiesl_exactCalibration_of_sharp_bounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    let C := artsGieslExactCalibrationOfSharpBounds U L
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact U.theoremLevel
  · simpa [artsGieslExactCalibrationOfSharpBounds] using L.theoremLevel

/-- Compatibility metadata object assembled from target-labelled packages.
It does not establish the reverse-mathematical bounds named by those labels. -/
noncomputable def artsGieslExactCalibrationViaDirectSharpBounds :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfSharpBounds
    artsGieslDirectSharpTheoremUpperBound
    artsGieslDirectSharpTheoremLowerBound

/-- Record-field projection; this does not establish mathematical exactness. -/
@[simp] theorem quarantined_metadata_artsGieslExactCalibrationViaDirectSharpBounds_status :
    artsGieslExactCalibrationViaDirectSharpBounds.status = CalibrationStatus.exact := rfl

/-- Record-field summary; this does not establish mathematical exactness. -/
theorem quarantined_metadata_artsGiesl_exactCalibration_via_directSharpBounds :
    let C := artsGieslExactCalibrationViaDirectSharpBounds
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  exact artsGiesl_exactCalibration_of_sharp_bounds
    artsGieslDirectSharpTheoremUpperBound
    artsGieslDirectSharpTheoremLowerBound

/-- Two target-profile packages yield the corresponding calibration record. -/
theorem artsGiesl_exactTheoremCalibration_of_sharp_bounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

/-! ## Named SCT-labelled profile packages

The definitions below expose named upper and lower packages derived from
`artsGieslExactCalibrationTransferFromSct`. Their obligations are profile and
evidence-tag equalities discharged by reduction. They do not add a formal
relation between the Arts-Giesl and SCT principles. They live in this namespace
to preserve the import direction of the component modules. -/

/-- Named upper profile package reusing the destination record from
`artsGieslExactCalibrationTransferFromSct`. -/
noncomputable def artsGieslConcreteSctSharpUpperTransfer :
    ArtsGieslSctSharpUpperTransfer where
  bound := artsGieslExactCalibrationTransferFromSct.dstUpper
  theoryEqSct  := by rfl
  ordinalEqSct := by rfl
  theoremLevel := by rfl

@[simp] theorem artsGieslConcreteSctSharpUpperTransfer_status :
    artsGieslConcreteSctSharpUpperTransfer.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslConcreteSctSharpUpperTransfer_theory :
    artsGieslConcreteSctSharpUpperTransfer.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteSctSharpUpperTransfer_ordinal :
    artsGieslConcreteSctSharpUpperTransfer.bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree := rfl

/-- Named lower profile package reusing the destination record from
`artsGieslExactCalibrationTransferFromSct`. -/
noncomputable def artsGieslConcreteSctSharpLowerTransfer :
    ArtsGieslSctSharpLowerTransfer where
  bound := artsGieslExactCalibrationTransferFromSct.dstLower
  theoryEqSct  := by rfl
  ordinalEqSct := by rfl
  theoremLevel := by rfl

@[simp] theorem artsGieslConcreteSctSharpLowerTransfer_status :
    artsGieslConcreteSctSharpLowerTransfer.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslConcreteSctSharpLowerTransfer_theory :
    artsGieslConcreteSctSharpLowerTransfer.bound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteSctSharpLowerTransfer_ordinal :
    artsGieslConcreteSctSharpLowerTransfer.bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree := rfl

/-- Pair the named upper and lower profile packages. -/
noncomputable def artsGieslConcreteSctSharpTransferPair :
    ArtsGieslSctSharpTransferPair where
  upper := artsGieslConcreteSctSharpUpperTransfer
  lower := artsGieslConcreteSctSharpLowerTransfer

@[simp] theorem artsGieslConcreteSctSharpTransferPair_upper_status :
    artsGieslConcreteSctSharpTransferPair.upper.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslConcreteSctSharpTransferPair_lower_status :
    artsGieslConcreteSctSharpTransferPair.lower.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The calibration constructor assigns status `exact` to the named pair's
record. This theorem proves only that status-field equality. -/
theorem artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
        artsGieslConcreteSctSharpTransferPair).calibration.status =
      CalibrationStatus.exact := rfl

/-! ## Named calibration metadata object

The named profile pair assembles into an `ArtsGieslExactTheoremCalibration`
record. The following lemmas expose its stored profile and status fields. The
object remains subject to the module-level limitation: it contains no
formalized reduction or reverse-mathematical derivability theorem. -/

/-- Upper profile package specialized to universe level zero. -/
noncomputable def artsGieslConcreteSharpTheoremUpperBound :
    ArtsGieslSharpTheoremUpperBound :=
  ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct
    (by rfl) (by rfl)

/-- Lower profile package specialized to universe level zero. -/
noncomputable def artsGieslConcreteSharpTheoremLowerBound :
    ArtsGieslSharpTheoremLowerBound :=
  ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct
    (by rfl) (by rfl)

/-- Named calibration record assembled from the universe-zero profile
packages above. -/
noncomputable def artsGieslConcreteExactTheoremCalibration :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    artsGieslConcreteSharpTheoremUpperBound
    artsGieslConcreteSharpTheoremLowerBound

/-! ### Record-field projection lemmas -/

@[simp] theorem artsGieslConcreteExactTheoremCalibration_status :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_targetTheory :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_targetOrdinal :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_upperTheory :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_upperOrdinal :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_upperTheoremLevel :
    artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The extracted lower package retains the `theoremLevel` tag. The proof uses
the record's coherence field because extraction passes through
`Classical.choose`. -/
theorem artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel :
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    artsGieslConcreteExactTheoremCalibration

/-! ### Extraction equalities for the named profile packages -/

/-- Upper-package extraction returns the named upper package. -/
theorem artsGieslConcreteExactTheoremCalibration_toSharpUpper_eq :
    artsGieslConcreteExactTheoremCalibration.toSharpUpperBound =
      artsGieslConcreteSharpTheoremUpperBound :=
  rfl

/-- Lower-package extraction returns a bound propositionally equal to the
named lower package. The proof uses `Option.some.inj` because extraction passes
through `Classical.choose`. -/
theorem artsGieslConcreteExactTheoremCalibration_toSharpLower_eq :
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound =
      artsGieslConcreteSharpTheoremLowerBound.bound := by
  have hLowerBound? :
      artsGieslConcreteExactTheoremCalibration.calibration.lowerBound?
        = some artsGieslConcreteSharpTheoremLowerBound.bound := rfl
  have hEq :
      Classical.choose artsGieslConcreteExactTheoremCalibration.lowerBound
        = artsGieslConcreteSharpTheoremLowerBound.bound := by
    apply Option.some.inj
    rw [← (Classical.choose_spec
      artsGieslConcreteExactTheoremCalibration.lowerBound).1, hLowerBound?]
  simpa [ArtsGieslExactTheoremCalibration.toSharpLowerBound] using hEq

/-! ### Named status endpoint -/

/-- The named calibration record has status field `exact`. -/
theorem artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibrationObject :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration.statusExact

/-! ### Short record-field aliases

These aliases expose the named object's status and target-profile fields. They
introduce no additional mathematical content. -/

/-- The named calibration record has status field `exact`. -/
theorem artsGieslConcreteExactTheoremCalibration_isExact :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration.statusExact

/-- The named calibration record stores the `RCA₀ + WO(ω^3)` target fields. -/
theorem artsGieslConcreteExactTheoremCalibration_hitsTarget :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree :=
  ⟨artsGieslConcreteExactTheoremCalibration.targetTheory,
    artsGieslConcreteExactTheoremCalibration.targetOrdinal⟩

/-! ## Alternative alignment-metadata route

This route builds the same target and evidence tags through an
`ArtsGieslSctTheoremAlignment` record rather than through the cost-shape field
of `ExactCalibrationTransfer`. Neither route contains a principle-indexed
reduction. -/

/-- Alignment metadata record with fixed target and evidence tags. Its
coherence fields discharge by reduction. -/
noncomputable def artsGieslConcreteSctTheoremAlignment :
    ArtsGieslSctTheoremAlignment where
  sharedTheoryTarget? := some FormalTheory.RCA0_WO_omega3
  sharedOrdinalTarget? := some omegaPowThree
  evidenceStatus := EvidenceStatus.theoremLevel
  sharedTheoryExact := rfl
  sharedOrdinalExact := rfl
  theoremLevel := rfl

/-! ### Projection theorems on the concrete theorem-alignment object -/

@[simp] theorem artsGieslConcreteSctTheoremAlignment_theory :
    artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? =
      some FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteSctTheoremAlignment_ordinal :
    artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? =
      some omegaPowThree := rfl

@[simp] theorem artsGieslConcreteSctTheoremAlignment_theoremLevel :
    artsGieslConcreteSctTheoremAlignment.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- Collect the alignment record's theory, ordinal, and evidence-tag fields. -/
theorem artsGieslConcreteSctTheoremAlignment_supported :
    artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? =
        some FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? =
          some omegaPowThree
      ∧ artsGieslConcreteSctTheoremAlignment.evidenceStatus =
          EvidenceStatus.theoremLevel :=
  ⟨rfl, rfl, rfl⟩

/-! ### Alignment-route profile pair and calibration record

The upper and lower packages are inlined at universe level zero to avoid the
universe polymorphism introduced by the generic extraction helpers. Their
content remains profile and evidence-tag metadata. -/

/-- Universe-zero pair of alignment-route profile packages. The original
constructors supplied fixed records independent of their alignment argument;
this definition makes that behavior explicit. -/
noncomputable def artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment :
    ArtsGieslSctSharpTransferPair where
  upper :=
    { bound :=
        { theoryProfile := rca0WoOmega3TheoryProfile
          evidenceStatus := EvidenceStatus.theoremLevel
          justificationTag := "theorem-level AG/SCT exact-target upper transfer" }
      theoryEqSct := rfl
      ordinalEqSct := rfl
      theoremLevel := rfl }
  lower :=
    { bound :=
        { theoryProfile := rca0WoOmega3TheoryProfile
          evidenceStatus := EvidenceStatus.theoremLevel
          justificationTag := "theorem-level AG/SCT exact-target lower transfer" }
      theoryEqSct := rfl
      ordinalEqSct := rfl
      theoremLevel := rfl }

/-- Universe-zero upper package with the alignment-route presentation tag. -/
noncomputable def artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment :
    ArtsGieslSharpTheoremUpperBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target upper transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Universe-zero lower package with the alignment-route presentation tag. -/
noncomputable def artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment :
    ArtsGieslSharpTheoremLowerBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target lower transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Calibration record assembled from the alignment-route profile packages. -/
noncomputable def artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment
    artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment

/-! ### Projections on the alignment-route calibration record -/

@[simp] theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_status :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetTheory :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_targetOrdinal :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.ordinalCeiling? =
      some omegaPowThree := rfl

@[simp] theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_upperTheoremLevel :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The extracted lower package retains the `theoremLevel` tag. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment

/-! ### Alignment-route status projections -/

/-- The alignment-route constructor assigns status field `exact`. -/
theorem artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibration :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

/-- The named alignment-route calibration record has status field `exact`. -/
theorem artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibrationObject :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.statusExact

/-! ### Alignment-route aliases -/

/-- The alignment record carries the `theoremLevel` tag. -/
theorem artsGieslConcreteSctTheoremAlignment_isTheoremLevel :
    artsGieslConcreteSctTheoremAlignment.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The alignment-route calibration record has status field `exact`. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_isExact :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

/-- The alignment-route calibration record stores the proposed target fields. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_hitsTarget :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree :=
  ⟨rfl, rfl⟩

/-! ## Comparison of the two metadata routes

The two routes store the same target, theory, ordinal, evidence, and status
fields. Their presentation tags differ, so the underlying records are compared
fieldwise or after tag erasure. -/

/-- Both records store the same target profile. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameTarget :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile =
      artsGieslConcreteExactTheoremCalibration.calibration.targetProfile :=
  rfl

/-- Both records store the same upper theory. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperTheory :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory :=
  rfl

/-- Both records store the same upper ordinal ceiling. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperOrdinal :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.ordinalCeiling? =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.ordinalCeiling? :=
  rfl

/-- Both records store the same upper evidence tag. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus :=
  rfl

/-- Both extracted lower packages store the same evidence tag. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.evidenceStatus =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.evidenceStatus := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel,
    artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel]

/-- Both records store the same calibration-status value. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      artsGieslConcreteExactTheoremCalibration.calibration.status :=
  rfl

/-! ### Profile-pair comparison -/

/-- The alignment-route upper package carries the `theoremLevel` tag. -/
@[simp] theorem artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_upper_status :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The alignment-route lower package carries the `theoremLevel` tag. -/
@[simp] theorem artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_lower_status :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- Collect the alignment-route pair's evidence tags and theory fields. -/
theorem artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_supported :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
        EvidenceStatus.theoremLevel
      ∧ artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
          EvidenceStatus.theoremLevel
      ∧ artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.theoryProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.theoryProfile.theory =
          FormalTheory.RCA0_WO_omega3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both upper packages store the same evidence tag. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_upperStatus :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.upper.bound.evidenceStatus :=
  rfl

/-- Both lower packages store the same evidence tag. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_lowerStatus :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.lower.bound.evidenceStatus :=
  rfl

/-- Both upper packages store the same theory value. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_upperTheory :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.upper.bound.theoryProfile.theory :=
  rfl

/-- Both lower packages store the same theory value. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_lowerTheory :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.lower.bound.theoryProfile.theory :=
  rfl

/-! ## Bridge between transfer and alignment metadata

Applying `ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer` to the
named transfer record yields the same fixed theory, ordinal, and evidence tag
as the named alignment record. The propositional coherence fields are
proof-irrelevant. -/

/-- Convert the transfer metadata record to an alignment metadata record. -/
noncomputable def artsGieslExactCalibrationTransferFromSct_toTheoremAlignment :
    ArtsGieslSctTheoremAlignment :=
  ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
    artsGieslExactCalibrationTransferFromSct rfl rfl

/-- Collect the converted alignment record's theory, ordinal, and evidence
fields. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_supported :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedTheoryTarget? =
        some FormalTheory.RCA0_WO_omega3
      ∧ artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedOrdinalTarget? =
          some omegaPowThree
      ∧ artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.evidenceStatus =
          EvidenceStatus.theoremLevel :=
  ⟨rfl, rfl, rfl⟩

/-- The converted and named alignment records are definitionally equal after
proof irrelevance. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment =
      artsGieslConcreteSctTheoremAlignment := rfl

/-- The two alignment records store the same theory target. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameTheory :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedTheoryTarget? =
      artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? := rfl

/-- The two alignment records store the same ordinal target. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameOrdinal :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedOrdinalTarget? =
      artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? := rfl

/-- The two alignment records store the same evidence tag. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameStatus :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.evidenceStatus =
      artsGieslConcreteSctTheoremAlignment.evidenceStatus := rfl

/-! ## Equality after presentation-tag erasure

The two metadata constructions differ only in `justificationTag`. After those
strings are erased, their upper, lower, and calibration records are equal. -/

/-- The upper records agree after erasing their presentation tags. -/
theorem artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteSharpTheoremUpperBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  rfl

/-- The lower records agree after erasing their presentation tags. -/
theorem artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteSharpTheoremLowerBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  rfl

/-- The calibration records agree after erasing their presentation tags. -/
theorem artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteExactTheoremCalibration.calibration.eraseJustificationTags =
      artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.eraseJustificationTags :=
  rfl

/-- Despite the declaration name, this theorem compares only the listed record
fields and the tag-erased calibration records. It does not compare formalized
reverse-mathematical principles or reductions. -/
theorem artsGieslConcreteExactTheoremCalibration_sameMathematicalContent_as_viaTheoremAlignment :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile =
        artsGieslConcreteExactTheoremCalibration.calibration.targetProfile
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.theory =
          artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.ordinalCeiling? =
          artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.ordinalCeiling?
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
          artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
          artsGieslConcreteExactTheoremCalibration.calibration.status
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.eraseJustificationTags =
          artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.eraseJustificationTags :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Extracted lower-package comparisons -/

/-- The extracted lower packages store the same theory value. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerTheory :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.theory := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.theoryEq,
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.theoryEq]

/-- The extracted lower packages store the same ordinal ceiling. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.ordinalEq,
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.ordinalEq]

/-! ## Generic metadata packaging and comparison

The following constructions are parametric in an `ExactCalibrationTransfer`
record whose source target fields equal the proposed theory and ordinal. The
same module-level limitation applies: the transfer type does not encode a
reduction between its profile parameters. -/

/-- Build a calibration record from a supplied transfer metadata record. -/
noncomputable def artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
      T hTheory hOrdinal)
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
      T hTheory hOrdinal)

/-- Fixed universe-zero upper package used by the alignment-metadata route. -/
noncomputable def artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute :
    ArtsGieslSharpTheoremUpperBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target upper transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Fixed universe-zero lower package used by the alignment-metadata route. -/
noncomputable def artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute :
    ArtsGieslSharpTheoremLowerBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target lower transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Build the fixed alignment-route calibration record. The arguments witness
the input contract but do not affect the fixed output packages. -/
noncomputable def artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
    (_T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (_hTheory : _T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (_hOrdinal : _T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute
    artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute

@[simp] theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_status
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.status =
      CalibrationStatus.exact := rfl

@[simp] theorem artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer_status
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.status =
      CalibrationStatus.exact := rfl

/-! ### Generic fieldwise metadata comparisons -/

/-- Both constructions store the same target profile. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameTargetProfile
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.targetProfile =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.targetProfile :=
  rfl

/-- Compare the upper theory fields. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperTheory
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory :=
  (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
    T hTheory hOrdinal).theoryEq

/-- Compare the upper ordinal fields. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperOrdinal
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling? =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling? :=
  (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
    T hTheory hOrdinal).ordinalEq

/-- Compare the upper evidence tags. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameUpperStatus
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.upperBound.evidenceStatus =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.upperBound.evidenceStatus :=
  (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
    T hTheory hOrdinal).theoremLevel

/-- Compare the calibration-status fields. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameStatus
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.status =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.status :=
  rfl

/-- Compare the extracted lower theory fields. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerTheory
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.theoryProfile.theory =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.theoryProfile.theory := by
  rw [(artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.theoryEq,
    (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.theoryEq]

/-- Compare the extracted lower ordinal fields. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerOrdinal
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.theoryProfile.ordinalCeiling? =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.theoryProfile.ordinalCeiling? := by
  rw [(artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.ordinalEq,
    (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.ordinalEq]

/-- Compare the extracted lower evidence tags. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameLowerStatus
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.evidenceStatus =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.bound.evidenceStatus := by
  rw [(artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).toSharpLowerBound.theoremLevel,
    (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).toSharpLowerBound.theoremLevel]

/-- Under full source-profile equality, the upper records agree after erasing
their presentation tags. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_upperBound
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree)
    (hSource : T.sourceCalibration.targetProfile =
      sctExactUpperBound.theoryProfile) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.upperBound.eraseJustificationTag =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.upperBound.eraseJustificationTag := by
  apply ReverseMathUpperBound.eraseJustificationTag_congr
  · show T.dstUpper.theoryProfile =
      artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute.bound.theoryProfile
    rw [T.upperMatchesSourceTarget, hSource]
    rfl
  · show T.dstUpper.evidenceStatus =
      artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute.bound.evidenceStatus
    exact T.upperTheoremLevel

/-- Under full source-profile equality, the optional lower records agree after
erasing their presentation tags. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_eraseTags_eq_ofTheoremAlignment_lowerBound
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree)
    (hSource : T.sourceCalibration.targetProfile =
      sctExactLowerBound.theoryProfile) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.lowerBound?.map
          ReverseMathLowerBound.eraseJustificationTag =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.lowerBound?.map
          ReverseMathLowerBound.eraseJustificationTag := by
  show (some T.dstLower).map _ = (some _).map _
  simp only [Option.map_some]
  apply congrArg some
  apply ReverseMathLowerBound.eraseJustificationTag_congr
  · show T.dstLower.theoryProfile =
      artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute.bound.theoryProfile
    rw [T.lowerMatchesSourceTarget, hSource]
    rfl
  · show T.dstLower.evidenceStatus =
      artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute.bound.evidenceStatus
    exact T.lowerTheoremLevel

/-- The upper records agree after erasing labels and tags when the source
theory and ordinal fields match the target. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.upperBound.erasePresentationMetadata =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.upperBound.erasePresentationMetadata := by
  apply ReverseMathUpperBound.erasePresentationMetadata_congr
  · show T.dstUpper.theoryProfile.theory =
      artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute.bound.theoryProfile.theory
    rw [T.upperMatchesSourceTarget]
    exact hTheory
  · show T.dstUpper.theoryProfile.ordinalCeiling? =
      artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute.bound.theoryProfile.ordinalCeiling?
    rw [T.upperMatchesSourceTarget]
    exact hOrdinal
  · show T.dstUpper.evidenceStatus =
      artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute.bound.evidenceStatus
    exact T.upperTheoremLevel

/-- The optional lower records agree after erasing labels and tags when the
source theory and ordinal fields match the target. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
        T hTheory hOrdinal).calibration.lowerBound?.map
          ReverseMathLowerBound.erasePresentationMetadata =
      (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
        T hTheory hOrdinal).calibration.lowerBound?.map
          ReverseMathLowerBound.erasePresentationMetadata := by
  show (some T.dstLower).map _ = (some _).map _
  simp only [Option.map_some]
  apply congrArg some
  apply ReverseMathLowerBound.erasePresentationMetadata_congr
  · show T.dstLower.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
    rw [T.lowerMatchesSourceTarget]
    exact hTheory
  · show T.dstLower.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
    rw [T.lowerMatchesSourceTarget]
    exact hOrdinal
  · show T.dstLower.evidenceStatus = EvidenceStatus.theoremLevel
    exact T.lowerTheoremLevel

/-! ### Full-record tag-erased equality

The generic API exposes upper and lower equalities separately because a full
`ReverseMathCalibration` equality is obstructed by the `Ordinal` universe in
the record type. The universe-zero instance has a full tag-erased equality. -/

/-- Collect the target, upper-package, and status-field comparisons. Lower
comparisons remain separate because `toSharpLowerBound` is universe-polymorphic
through `Classical.choose`. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameMathematicalContent_as_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
          T hTheory hOrdinal).calibration.targetProfile =
        (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
          T hTheory hOrdinal).calibration.targetProfile
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling? =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling?
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.evidenceStatus =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.evidenceStatus
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.status =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.status :=
  by
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩
    · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoryEq
    · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).ordinalEq
    · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
        T hTheory hOrdinal).theoremLevel

/-- Despite the declaration name, this theorem compares record fields and
presentation-erased packages only. It adds no proposition about the semantics
or derivability strength of the represented principles. -/
theorem artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_sameSemanticContent_as_ofTheoremAlignment
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3)
    (hOrdinal : T.sourceCalibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
          T hTheory hOrdinal).calibration.targetProfile =
        (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
          T hTheory hOrdinal).calibration.targetProfile
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.theory
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling? =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.theoryProfile.ordinalCeiling?
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.evidenceStatus =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.evidenceStatus
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.status =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.status
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.upperBound.erasePresentationMetadata =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.upperBound.erasePresentationMetadata
      ∧ (artsGieslExactTheoremCalibrationOfExactCalibrationTransfer
            T hTheory hOrdinal).calibration.lowerBound?.map
              ReverseMathLowerBound.erasePresentationMetadata =
          (artsGieslExactTheoremCalibrationOfTheoremAlignmentFromExactTransfer
            T hTheory hOrdinal).calibration.lowerBound?.map
              ReverseMathLowerBound.erasePresentationMetadata := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
      T hTheory hOrdinal).theoryEq
  · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
      T hTheory hOrdinal).ordinalEq
  · exact (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
      T hTheory hOrdinal).theoremLevel
  · exact artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_upperBound
      T hTheory hOrdinal
  · exact artsGieslExactTheoremCalibrationOfExactCalibrationTransfer_erasePresentation_eq_ofTheoremAlignment_lowerBound
      T hTheory hOrdinal

end OperatorKO7.ArtsGieslReverseMathCalibration
