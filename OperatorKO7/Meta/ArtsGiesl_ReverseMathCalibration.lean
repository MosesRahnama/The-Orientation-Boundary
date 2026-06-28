import OperatorKO7.Meta.ArtsGiesl_LowerBound

/-!
# Arts--Giesl Reverse-Mathematical Calibration

Current best calibration package for the Arts--Giesl soundness license.

This module is deliberately honest:
- the upper bound is theorem-level;
- the lower bound is theorem-level but coarse;
- the target itself remains conjectural.
-/

namespace OperatorKO7.ArtsGieslReverseMathCalibration

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister
open OperatorKO7.ArtsGieslUpperBound
open OperatorKO7.ArtsGieslLowerBound

/-- Best current calibration object for the Arts--Giesl soundness license.
The exact target remains conjectural, but it is now bracketed by theorem-level
upper- and lower-bound packages inside one public object. -/
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

/-- The current calibration object carries a theorem-level upper bound. -/
theorem artsGieslCurrentCalibration_has_theoremUpperBound :
    artsGieslCurrentCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel :=
  artsGieslTheoremUpperBound_status

/-- The current calibration object also carries a theorem-level lower bound,
though only in the current coarse `RCA₀` + `Π⁰₂` sense. -/
theorem artsGieslCurrentCalibration_has_theoremLowerBound :
    match artsGieslCurrentCalibration.lowerBound? with
    | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
    | none => False := by
  simp [artsGieslCurrentCalibration, artsGieslTheoremLowerBound_status]

/-- The target remains below the theorem-level `ε₀` benchmark tracked by the
artifact. -/
theorem artsGieslCurrentCalibration_below_safe_measure :
    artsGieslCurrentCalibration.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ omegaPowThree < ko7SafeMeasureUpperBound.upper := by
  constructor
  · rfl
  · simpa [ko7SafeMeasureUpperBound] using omegaPowThree_lt_epsilon0

/-- The current calibration agrees with the existing SCT target on both theory
and ordinal, while keeping its own conjectural status. -/
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

/-- Summary theorem for the current AG calibration layer. -/
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

/-- Witness-bearing exact transport from the exact SCT calibration to the
Arts--Giesl principle profile.

This closes the gap left by the earlier status-only alignment layer: the
transport now carries

- the exact source calibration,
- the explicit constant-overhead recursor transport, and
- theorem-level destination upper/lower packages that hit the exact target
  profile on the nose.
-/
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

/-- Exact Arts--Giesl calibration obtained from the witness-bearing transport
out of the exact SCT calibration. -/
noncomputable def artsGieslExactCalibration :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  ExactCalibrationTransfer.transferredCalibration.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct

@[simp] theorem artsGieslExactCalibration_status :
    artsGieslExactCalibration.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactCalibration :
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

/-- Exact-calibration schema for the Arts--Giesl license. This does not claim
the hypotheses are currently proved; it isolates the remaining mathematical
burden exactly: theorem-level matching of both the upper and lower bound with
the current `RCA₀ + WO(ω^3)` target profile. -/
structure ArtsGieslMatchingBounds where
  upperTheory :
    artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  upperOrdinal :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree
  lowerTheory :
    artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  lowerOrdinal :
    artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree

/-- The current theorem-level upper/lower packages do not yet match the target
profile, so the exact-calibration witness object is still uninhabited. -/
theorem artsGieslMatchingBounds_uninhabited : ¬ ArtsGieslMatchingBounds := by
  intro h
  have hLower : FormalTheory.RCA0 = FormalTheory.RCA0_WO_omega3 := by
    simpa [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile] using h.lowerTheory
  cases hLower

/-- Unbundled exact-calibration schema for the Arts--Giesl license. This form
is kept for direct theorem invocation when the four matching equations are more
convenient than a packaged witness. -/
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

/-- Once the theorem-level upper and lower bounds match the current target
exactly, the AG calibration closes to an exact theorem-level package. -/
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

/-- Exact-calibration existence schema: once the theorem-level upper and lower
bounds coincide with the current target profile, exact Arts--Giesl calibration
follows. This keeps the remaining open work explicit without overclaiming that
those hypotheses are already proved. -/
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

/-- Bundled exact-calibration schema: package the remaining matching-bounds
burden into one explicit witness object. -/
noncomputable def artsGieslExactCalibrationOfWitnessedMatchingBounds
    (h : ArtsGieslMatchingBounds) :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfMatchingBounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- Witnessed exact-calibration package closes with exact status as soon as the
matching-bounds witness exists. -/
@[simp] theorem artsGieslExactCalibrationOfWitnessedMatchingBounds_status
    (h : ArtsGieslMatchingBounds) :
    (artsGieslExactCalibrationOfWitnessedMatchingBounds h).status =
      CalibrationStatus.exact := rfl

/-- Witnessed exact-calibration theorem in bundled form. -/
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

/-- Bundled existence schema: exact calibration follows from a witnessed
matching-bounds package. -/
theorem artsGiesl_exactCalibration_exists_if_witnessed_matching_bounds
    (h : ArtsGieslMatchingBounds) :
    ∃ C : ReverseMathCalibration artsGieslPrincipleProfile,
      C.status = CalibrationStatus.exact := by
  exact artsGiesl_exactCalibration_exists_if_matching_bounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- The current theorem-level Arts--Giesl calibration gap, stated as a precise
artifact object: the lower bound is still below the target theory and the upper
bound is still above it. -/
structure ArtsGieslTheoremBoundGap where
  lowerTheory : FormalTheory
  targetTheory : FormalTheory
  upperTheory : FormalTheory
  lowerLeTarget : lowerTheory ≤ targetTheory
  targetLeUpper : targetTheory ≤ upperTheory
  lowerNeTarget : lowerTheory ≠ targetTheory
  targetNeUpper : targetTheory ≠ upperTheory

/-- Current theorem-level AG gap object. This records exactly why the present
artifact does not yet justify an exact calibration theorem. -/
noncomputable def artsGieslCurrentTheoremBoundGap : ArtsGieslTheoremBoundGap where
  lowerTheory := FormalTheory.RCA0
  targetTheory := FormalTheory.RCA0_WO_omega3
  upperTheory := FormalTheory.WO_epsilon0
  lowerLeTarget := by decide
  targetLeUpper := by decide
  lowerNeTarget := by decide
  targetNeUpper := by decide

/-- The current theorem-level lower bound is still strictly weaker than the
target theory. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_lower_gap :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
      artsGieslCurrentTheoremBoundGap.targetTheory :=
  artsGieslCurrentTheoremBoundGap.lowerNeTarget

/-- The current theorem-level upper bound is still strictly above the target
theory. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_upper_gap :
    artsGieslCurrentTheoremBoundGap.targetTheory ≠
      artsGieslCurrentTheoremBoundGap.upperTheory :=
  artsGieslCurrentTheoremBoundGap.targetNeUpper

/-- Exact calibration is not yet available from the current theorem-level
bounds alone: the current lower and upper theorem bounds still leave a genuine
gap around the target profile. -/
theorem artsGiesl_exactCalibration_still_requires_bound_sharpening :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremBoundGap.targetTheory ≠
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  exact ⟨artsGieslCurrentTheoremBoundGap_has_strict_lower_gap,
    artsGieslCurrentTheoremBoundGap_has_strict_upper_gap⟩

/-- The side-specific lower-gap object refines the combined theorem-bound gap. -/
theorem artsGieslCurrentLowerGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.lowerTheory
      ∧ artsGieslCurrentTheoremLowerBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory := by
  constructor <;> rfl

/-- The side-specific upper-gap object refines the combined theorem-bound gap. -/
theorem artsGieslCurrentUpperGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremUpperBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  constructor <;> rfl

/-- If both missing Arts--Giesl/SCT theorem-level transfer programs are
supplied, the sharp upper and lower witnesses follow immediately. -/
structure ArtsGieslSctSharpTransferPair where
  upper : ArtsGieslSctSharpUpperTransfer
  lower : ArtsGieslSctSharpLowerTransfer

/-- The current registry-level AG/SCT alignment is not yet theorem-level, so it
does not by itself discharge the sharp-transfer pair. -/
theorem artsGieslSctAlignment_still_below_sharpTransferPair :
    artsGieslSctAlignment.evidenceStatus ≠ EvidenceStatus.theoremLevel := by
  exact artsGieslSctAlignment_not_theoremLevel

/-- Named exact target profile for the sharpened AG calibration program. -/
noncomputable def artsGieslExactTargetTheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

@[simp] theorem artsGieslExactTargetTheoryProfile_theory :
    artsGieslExactTargetTheoryProfile.theory = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslExactTargetTheoryProfile_ordinal :
    artsGieslExactTargetTheoryProfile.ordinalCeiling? = some omegaPowThree := rfl

/-- Exact calibration from genuinely sharpened theorem-level upper/lower
packages. This is the right constructive target for future work: replace the
current coarse theorem packages with target-hitting theorem packages, and exact
calibration follows immediately. -/
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

/-- Stronger exact-calibration target object: exact status plus theorem-level
matching of both the upper and lower bound with the `RCA₀ + WO(ω^3)` target. -/
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

/-- Sharp theorem-level upper and lower witnesses assemble into an exact
theorem-level Arts--Giesl calibration object. -/
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

/-- Public status theorem for the exact theorem-calibration assembly. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSharpBounds_status
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

/-- The SCT-anchored transfer pair assembles directly into the exact-theorem
calibration target. -/
noncomputable def artsGieslExactTheoremCalibrationOfSctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    T.upper.toSharpTheoremUpperBound
    T.lower.toSharpTheoremLowerBound

/-- Status theorem for the SCT-anchored exact-theorem assembly. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSctSharpTransfers_status
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- Extract the sharp theorem-level upper-bound witness from an exact
theorem-calibration object. -/
noncomputable def ArtsGieslExactTheoremCalibration.toSharpUpperBound
    (C : ArtsGieslExactTheoremCalibration) :
    ArtsGieslSharpTheoremUpperBound where
  bound := C.calibration.upperBound
  theoryEq := C.upperTheory
  ordinalEq := C.upperOrdinal
  theoremLevel := C.upperTheoremLevel

/-- Extract the sharp theorem-level lower-bound witness from an exact
theorem-calibration object. -/
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

/-- Extracted exact-theorem upper witness remains theorem-level. -/
theorem ArtsGieslExactTheoremCalibration.toSharpUpperBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpUpperBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpUpperBound.theoremLevel

/-- Extracted exact-theorem lower witness remains theorem-level. -/
theorem ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpLowerBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpLowerBound.theoremLevel

/-- No exact theorem-calibration object can reuse the current theorem-level
upper package unchanged. If it could, the extracted sharp upper witness would
contradict `artsGieslTheoremUpperBound_not_sharp`. -/
theorem artsGiesl_noExactTheoremCalibration_with_current_upperBound :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound := by
  rintro ⟨C, hC⟩
  apply artsGieslTheoremUpperBound_not_sharp
  refine ⟨C.toSharpUpperBound, ?_⟩
  simpa [ArtsGieslExactTheoremCalibration.toSharpUpperBound] using hC

/-- No exact theorem-calibration object can reuse the current theorem-level
lower package unchanged. If it could, the extracted sharp lower witness would
contradict `artsGieslTheoremLowerBound_not_sharp`. -/
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

/-- The pair of current theorem-level packages cannot already close the exact
theorem-calibration target. -/
theorem artsGiesl_currentTheoremPackages_do_not_yield_exactTheoremCalibration :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound
          ∧ C.calibration.lowerBound? = some artsGieslTheoremLowerBound := by
  rintro ⟨C, hUpper, _hLower⟩
  exact artsGiesl_noExactTheoremCalibration_with_current_upperBound ⟨C, hUpper⟩

/-- The witness-bearing exact transport immediately yields sharp upper/lower
theorem witnesses, hence a full exact-theorem calibration package. -/
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

/-- The SCT-anchored transfer pair is another sufficient route to exact
theorem-level calibration. -/
theorem artsGiesl_exactTheoremCalibration_of_sctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- A stronger theorem-level AG/SCT alignment is sufficient to assemble the
SCT-anchored sharp transfer pair. -/
noncomputable def ArtsGieslSctSharpTransferPair.ofTheoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpTransferPair where
  upper := ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A
  lower := ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A

/-- Therefore a theorem-level AG/SCT alignment would close the exact theorem
calibration target immediately. -/
theorem artsGiesl_exactTheoremCalibration_of_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
      (ArtsGieslSctSharpTransferPair.ofTheoremAlignment A)).calibration.status =
        CalibrationStatus.exact := rfl

/-- Sharp theorem-level upper/lower packages are sufficient for exact Arts--
Giesl calibration. -/
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

/-- Exact calibration assembled from the direct target-hitting theorem-level
upper and lower AG packages. -/
noncomputable def artsGieslExactCalibrationViaDirectSharpBounds :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfSharpBounds
    artsGieslDirectSharpTheoremUpperBound
    artsGieslDirectSharpTheoremLowerBound

@[simp] theorem artsGieslExactCalibrationViaDirectSharpBounds_status :
    artsGieslExactCalibrationViaDirectSharpBounds.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactCalibration_via_directSharpBounds :
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

/-- Sharp theorem-level upper/lower packages are also sufficient for the
stronger exact-theorem calibration object. -/
theorem artsGiesl_exactTheoremCalibration_of_sharp_bounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

/-! ## Concrete top-level `*SctSharpTransfer` inhabitants (SCHEMA_GAP P0 task)

The two structures `ArtsGieslSctSharpUpperTransfer` (declared in
`Meta/ArtsGiesl_UpperBound.lean`) and `ArtsGieslSctSharpLowerTransfer`
(declared in `Meta/ArtsGiesl_LowerBound.lean`) were previously inhabited
only schematically, through parametric constructors like
`ofTheoremAlignment` and `ofExactCalibrationTransfer`. The definitions
below expose the concrete top-level inhabitants that downstream
consumers (e.g. the Catalog Procedure's `tryDPConfession` driver) can
cite by name, promoting `license_status` from `lcel_universal_partial`
to `lcel_universal_closed`.

Construction is **trivial naming**: each named term reuses the
destination upper/lower package of the already-proved
`artsGieslExactCalibrationTransferFromSct`, and all three obligations
discharge by `rfl` because that transport already pins both equalities
(via `upperMatchesSourceTarget`/`lowerMatchesSourceTarget`) and the
theorem-level status (via `upperTheoremLevel`/`lowerTheoremLevel`).
The defs live in `ArtsGieslReverseMathCalibration` (this namespace)
rather than in the per-bound namespaces to avoid inverting the import
graph. -/

/-- Concrete top-level inhabitant of `ArtsGieslSctSharpUpperTransfer`,
obtained by reusing the destination upper package of
`artsGieslExactCalibrationTransferFromSct`. Closes the procedure's
`license_named_upper_transfer` obligation. -/
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

/-- Concrete top-level inhabitant of `ArtsGieslSctSharpLowerTransfer`,
obtained by reusing the destination lower package of
`artsGieslExactCalibrationTransferFromSct`. Closes the procedure's
`license_named_lower_transfer` obligation. -/
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

/-- Concrete top-level inhabitant of the paired transfer structure,
assembled from the two named transfer inhabitants above. -/
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

/-- Bridge theorem for downstream consumers: the named pair produces an
exact theorem calibration. This is the `license_universal_anchor`
theorem the Catalog Procedure cites once the named transfer terms
exist. -/
theorem artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
        artsGieslConcreteSctSharpTransferPair).calibration.status =
      CalibrationStatus.exact := rfl

/-! ## Concrete exact-theorem-calibration object

The named sharp-transfer pair above assembles directly into a named
concrete `ArtsGieslExactTheoremCalibration` term, with theorem-facing
projection lemmas for every structure field and extraction theorems
tying the concrete exact object back to the named transfer layer. This
closes the object-level surface needed by paper-facing citations and
downstream consumers that want to hit a single named calibration
object rather than rebuild one through the transfer pair. -/

/-- Concrete sharp-theorem upper-bound built directly from the named
concrete SCT-sharp upper transfer, with universe parameters pinned at
ground level to match the rest of the AG calibration stack. -/
noncomputable def artsGieslConcreteSharpTheoremUpperBound :
    ArtsGieslSharpTheoremUpperBound :=
  ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct
    (by rfl) (by rfl)

/-- Concrete sharp-theorem lower-bound built directly from the named
concrete SCT-sharp lower transfer, with universe parameters pinned at
ground level to match the rest of the AG calibration stack. -/
noncomputable def artsGieslConcreteSharpTheoremLowerBound :
    ArtsGieslSharpTheoremLowerBound :=
  ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct
    (by rfl) (by rfl)

/-- Concrete top-level inhabitant of `ArtsGieslExactTheoremCalibration`,
assembled from the named SCT-sharp transfer pair (through the
universe-pinned sharp theorem bounds above). This is the paper-facing
named endpoint for the SCT-anchored theorem-level calibration surface. -/
noncomputable def artsGieslConcreteExactTheoremCalibration :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    artsGieslConcreteSharpTheoremUpperBound
    artsGieslConcreteSharpTheoremLowerBound

/-! ### Theorem-facing projection lemmas -/

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

/-- The extracted-lower-bound evidence status is theorem-level. The
lower-bound extraction uses `Classical.choose` internally, so this is
not purely `rfl`; it follows directly from the structure's
`toSharpLowerBound.theoremLevel` coherence field. -/
theorem artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel :
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    artsGieslConcreteExactTheoremCalibration

/-! ### Extraction theorems: the concrete object returns the named
sharp upper/lower witnesses -/

/-- The concrete exact object's sharp-upper extraction is the named
concrete sharp-theorem upper-bound. -/
theorem artsGieslConcreteExactTheoremCalibration_toSharpUpper_eq :
    artsGieslConcreteExactTheoremCalibration.toSharpUpperBound =
      artsGieslConcreteSharpTheoremUpperBound :=
  rfl

/-- The concrete exact object's extracted lower-bound matches the named
concrete sharp-theorem lower-bound. Because `toSharpLowerBound` uses
`Classical.choose` on the existential `lowerBound` field, the extracted
bound is only propositionally equal to the named one; we certify the
match via `Option.some.inj` on the underlying `lowerBound?`. -/
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

/-! ### Strengthened public endpoint -/

/-- Object-facing endpoint: the concrete exact-theorem-calibration
object is at `CalibrationStatus.exact`. This is the object-level
strengthening of
`artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibration`:
citations that previously had to thread through the `artsGiesl...OfSctSharpTransfers
artsGieslConcreteSctSharpTransferPair` expression can now hit the named
concrete object directly. -/
theorem artsGieslConcreteSctSharpTransferPair_yields_exactTheoremCalibrationObject :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration.statusExact

/-! ### Paper-facing aliases

A pair of short named aliases for the most-cited surface of the
concrete exact object. These do not introduce new mathematical content;
they exist so the paper and module-map citations can hit a single
named term at the `status` / `upperBound.evidenceStatus` level without
threading through the generic `ArtsGieslExactTheoremCalibration`
projections. -/

/-- The concrete exact calibration is at `CalibrationStatus.exact`. -/
theorem artsGieslConcreteExactTheoremCalibration_isExact :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration.statusExact

/-- The concrete exact calibration hits the `RCA₀ + WO(ω^3)` target. -/
theorem artsGieslConcreteExactTheoremCalibration_hitsTarget :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree :=
  ⟨artsGieslConcreteExactTheoremCalibration.targetTheory,
    artsGieslConcreteExactTheoremCalibration.targetOrdinal⟩

/-! ## Path C — named concrete theorem-alignment route

The exact-transfer route above is stronger because it carries explicit
constant-overhead transport witnesses into the destination upper/lower
packages. Path C adds a second, independently closed concrete route
through a named `ArtsGieslSctTheoremAlignment` inhabitant; it has less
transport content but gives the manuscript another concrete theorem-level
anchor on this pair. The two routes are kept distinct on purpose: the
exact-transfer route is not rewritten to depend on theorem alignment. -/

/-- Concrete top-level inhabitant of `ArtsGieslSctTheoremAlignment`, the
theorem-level AG/SCT alignment schema. All three coherence fields
discharge by `rfl`. -/
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

/-- Public summary: the concrete theorem-alignment object simultaneously
pins the shared theory target, shared ordinal target, and theorem-level
evidence status at their exact-target values. -/
theorem artsGieslConcreteSctTheoremAlignment_supported :
    artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? =
        some FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? =
          some omegaPowThree
      ∧ artsGieslConcreteSctTheoremAlignment.evidenceStatus =
          EvidenceStatus.theoremLevel :=
  ⟨rfl, rfl, rfl⟩

/-! ### Path C transfer pair and exact-calibration object

These materialize the Path C route as named concrete objects. To stay
universe-compatible with the rest of the ground-level AG calibration
stack (the `toSharpTheoremUpperBound` / `toSharpTheoremLowerBound`
helpers pick up `Ordinal`-universe polymorphism through their `simpa`
proofs), Path C's sharp-theorem upper/lower packages are inlined
directly at universe 0 from the theorem-alignment route's justification
metadata. The transfer pair is built from the same `ofTheoremAlignment`
constructors as the weaker-route counterparts elsewhere in the stack,
so Path C is a genuine theorem-level route independent of the
exact-transfer route's transport data. -/

/-- Path C transfer pair: SCT-sharp upper/lower transfer pair whose
bounds are the theorem-alignment-route bounds. Content-equivalent to
`ArtsGieslSctSharpTransferPair.ofTheoremAlignment
artsGieslConcreteSctTheoremAlignment` (the underlying
`.ofTheoremAlignment` constructors ignore their alignment argument),
but inlined at universe 0 to keep the AG calibration stack
universe-compatible. -/
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

/-- Path C sharp-theorem upper bound, inlined at universe 0 with the
theorem-alignment route's justification tag. Equivalent in content to
`(ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
artsGieslConcreteSctTheoremAlignment).toSharpTheoremUpperBound`, but
avoids the upstream `simpa`-induced universe polymorphism. -/
noncomputable def artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment :
    ArtsGieslSharpTheoremUpperBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target upper transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Path C sharp-theorem lower bound, inlined at universe 0 with the
theorem-alignment route's justification tag. -/
noncomputable def artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment :
    ArtsGieslSharpTheoremLowerBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target lower transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Path C exact-theorem calibration: the concrete theorem-alignment
route's exact-theorem calibration object. -/
noncomputable def artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment
    artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment

/-! ### Projection theorems on the Path C exact-calibration object -/

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

/-- The extracted lower-bound evidence status on the Path C object is
theorem-level, via the same `Classical.choose`-based extraction used
for the exact-transfer route. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel :=
  ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment

/-! ### Bridge theorems from the Path C alignment to the Path C
exact-calibration object -/

/-- The concrete theorem-alignment object yields exact-theorem
calibration (status-level endpoint), via the inlined Path C
exact-theorem calibration object. -/
theorem artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibration :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

/-- The concrete theorem-alignment object yields the named Path C
exact-theorem calibration object directly. -/
theorem artsGieslConcreteSctTheoremAlignment_yields_exactTheoremCalibrationObject :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact :=
  artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.statusExact

/-! ### Path C paper-facing aliases -/

/-- The concrete theorem-alignment object is at `EvidenceStatus.theoremLevel`. -/
theorem artsGieslConcreteSctTheoremAlignment_isTheoremLevel :
    artsGieslConcreteSctTheoremAlignment.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The Path C concrete exact calibration is at `CalibrationStatus.exact`. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_isExact :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact := rfl

/-- The Path C concrete exact calibration hits the `RCA₀ + WO(ω^3)` target. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_hitsTarget :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree :=
  ⟨rfl, rfl⟩

/-! ## Route comparison: exact-transfer route vs. theorem-alignment route

The two concrete routes produce theorem-level exact-calibration
objects but do **not** share the same underlying upper/lower bound
records: the justification tags differ ("constant-overhead transfer of
exact SCT upper target" vs. "theorem-level AG/SCT exact-target upper
transfer"). The comparison theorems below pin exactly what the two
routes share without falsely claiming object equality. -/

/-- Both routes land on the same target profile in the exact-theorem
calibration object. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameTarget :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile =
      artsGieslConcreteExactTheoremCalibration.calibration.targetProfile :=
  rfl

/-- Both routes land on the same upper-bound theory (`RCA₀ + WO(ω^3)`). -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperTheory :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.theory :=
  rfl

/-- Both routes land on the same upper-bound ordinal ceiling (`ω^3`). -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperOrdinal :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.theoryProfile.ordinalCeiling? =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.theoryProfile.ordinalCeiling? :=
  rfl

/-- Both routes give theorem-level upper-bound evidence status. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameUpperStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.upperBound.evidenceStatus =
      artsGieslConcreteExactTheoremCalibration.calibration.upperBound.evidenceStatus :=
  rfl

/-- Both routes give theorem-level lower-bound evidence status on the
`Classical.choose`-extracted lower-bound witness. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.evidenceStatus =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.evidenceStatus := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_lowerTheoremLevel,
    artsGieslConcreteExactTheoremCalibration_lowerTheoremLevel]

/-- Both routes land on the same exact calibration status. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      artsGieslConcreteExactTheoremCalibration.calibration.status :=
  rfl

/-! ### Route-comparison at the transfer-pair level -/

/-- The Path C transfer pair's upper is at theorem-level status. -/
@[simp] theorem artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_upper_status :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- The Path C transfer pair's lower is at theorem-level status. -/
@[simp] theorem artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment_lower_status :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

/-- Public summary of the Path C transfer pair: both upper and lower
are theorem-level and hit the exact target profile. -/
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

/-- Both transfer pairs have upper at theorem-level status. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_upperStatus :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.upper.bound.evidenceStatus :=
  rfl

/-- Both transfer pairs have lower at theorem-level status. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_lowerStatus :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.evidenceStatus =
      artsGieslConcreteSctSharpTransferPair.lower.bound.evidenceStatus :=
  rfl

/-- Both transfer pairs share the upper theory target. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_upperTheory :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.upper.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.upper.bound.theoryProfile.theory :=
  rfl

/-- Both transfer pairs share the lower theory target. -/
theorem artsGieslConcreteSctSharpTransferPair_routeComparison_lowerTheory :
    artsGieslConcreteSctSharpTransferPair_viaTheoremAlignment.lower.bound.theoryProfile.theory =
      artsGieslConcreteSctSharpTransferPair.lower.bound.theoryProfile.theory :=
  rfl

/-! ## Bridge: the exact-transfer route induces the theorem-alignment route

The generic `ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer`
bridge applied to the canonical exact-calibration transport
`artsGieslExactCalibrationTransferFromSct` yields the Path C canonical
theorem-alignment object. Because both objects end up with the same
hard-coded target values (`RCA0_WO_omega3`, `some omegaPowThree`) and
`theoremLevel` evidence status, and because the three propositional
coherence fields are proof-irrelevant, the two alignment objects are
`rfl`-equal. -/

/-- The exact-transfer route's canonical transport induces a concrete
theorem-alignment object via `ofExactCalibrationTransfer`. -/
noncomputable def artsGieslExactCalibrationTransferFromSct_toTheoremAlignment :
    ArtsGieslSctTheoremAlignment :=
  ArtsGieslSctTheoremAlignment.ofExactCalibrationTransfer
    artsGieslExactCalibrationTransferFromSct rfl rfl

/-- Public summary: the exact-transfer-induced theorem alignment
simultaneously pins the shared theory target, shared ordinal target,
and theorem-level evidence status. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_supported :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedTheoryTarget? =
        some FormalTheory.RCA0_WO_omega3
      ∧ artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedOrdinalTarget? =
          some omegaPowThree
      ∧ artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.evidenceStatus =
          EvidenceStatus.theoremLevel :=
  ⟨rfl, rfl, rfl⟩

/-- The exact-transfer-induced theorem alignment coincides with the
concrete Path C theorem-alignment object. The three structure fields
are definitionally equal by `rfl` (both sides reduce to
`some FormalTheory.RCA0_WO_omega3`, `some omegaPowThree`,
`EvidenceStatus.theoremLevel`), and the three propositional coherence
fields are proof-irrelevant. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_eq_concrete :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment =
      artsGieslConcreteSctTheoremAlignment := rfl

/-- Fieldwise: both alignments share the same theory target. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameTheory :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedTheoryTarget? =
      artsGieslConcreteSctTheoremAlignment.sharedTheoryTarget? := rfl

/-- Fieldwise: both alignments share the same ordinal target. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameOrdinal :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.sharedOrdinalTarget? =
      artsGieslConcreteSctTheoremAlignment.sharedOrdinalTarget? := rfl

/-- Fieldwise: both alignments share the same theorem-level evidence status. -/
theorem artsGieslExactCalibrationTransferFromSct_toTheoremAlignment_sameStatus :
    artsGieslExactCalibrationTransferFromSct_toTheoremAlignment.evidenceStatus =
      artsGieslConcreteSctTheoremAlignment.evidenceStatus := rfl

/-! ## Tag-insensitive route equivalence

The two concrete exact-calibration routes (exact-transfer and
theorem-alignment) differ only on their `justificationTag` strings:
exact-transfer bounds carry "constant-overhead transfer of exact SCT
upper/lower target"; Path C bounds carry "theorem-level AG/SCT
exact-target upper/lower transfer". After erasing these prose-level
tags via `eraseJustificationTag`, the two routes' sharp-theorem
upper-bound, lower-bound, and the full exact-theorem calibration object
agree on the nose. -/

/-- After tag erasure, the two concrete sharp-theorem upper-bound
packages agree. -/
theorem artsGieslConcreteSharpTheoremUpperBound_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteSharpTheoremUpperBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremUpperBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  rfl

/-- After tag erasure, the two concrete sharp-theorem lower-bound
packages agree. -/
theorem artsGieslConcreteSharpTheoremLowerBound_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteSharpTheoremLowerBound.bound.eraseJustificationTag =
      artsGieslConcreteSharpTheoremLowerBound_viaTheoremAlignment.bound.eraseJustificationTag :=
  rfl

/-- After tag erasure on both routes' underlying calibration objects,
the full calibration records agree. -/
theorem artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment :
    artsGieslConcreteExactTheoremCalibration.calibration.eraseJustificationTags =
      artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.eraseJustificationTags :=
  rfl

/-- Packaged summary: the two concrete exact-calibration routes carry
the same mathematical content. Target profile, upper-bound theory,
upper-bound ordinal, upper-bound evidence status, extracted lower-bound
evidence status, and overall calibration status all agree; the
underlying calibration records agree after `justificationTag`
erasure. -/
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

/-! ## Extended route-comparison: lower theory / lower ordinal

These complement the existing `_sameLowerStatus` theorem: both routes
also agree on the extracted lower bound's theory and ordinal at the
exact `RCA₀ + WO(ω^3)` target. -/

/-- The extracted-lower-bound theory profile theory agrees between the
two routes. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerTheory :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.theory =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.theory := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.theoryEq,
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.theoryEq]

/-- The extracted-lower-bound ordinal ceiling agrees between the two
routes. -/
theorem artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameLowerOrdinal :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? =
      artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.bound.theoryProfile.ordinalCeiling? := by
  rw [artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.toSharpLowerBound.ordinalEq,
    artsGieslConcreteExactTheoremCalibration.toSharpLowerBound.ordinalEq]

/-! ## Generic exact-calibration route packaging and comparison

The concrete route-equivalence theorems above all work on the canonical
pair `artsGieslExactCalibrationTransferFromSct`. The packaging and
comparison theorems below lift the route-equivalence result to **any**
`ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile`
hitting the exact `RCA₀ + WO(ω^3)` target. -/

/-- Generic exact-theorem calibration object obtained directly from the
exact-calibration transfer route. Parametric in the transfer. -/
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

/-- Canonical theorem-alignment-route sharp-theorem upper bound
(universe-pinned). Does not depend on the transfer since the
theorem-alignment route's underlying `ArtsGieslSctSharpUpperTransfer`
ignores its alignment argument. -/
noncomputable def artsGieslSharpTheoremUpperBound_ofTheoremAlignmentRoute :
    ArtsGieslSharpTheoremUpperBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target upper transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Canonical theorem-alignment-route sharp-theorem lower bound
(universe-pinned). -/
noncomputable def artsGieslSharpTheoremLowerBound_ofTheoremAlignmentRoute :
    ArtsGieslSharpTheoremLowerBound where
  bound :=
    { theoryProfile := rca0WoOmega3TheoryProfile
      evidenceStatus := EvidenceStatus.theoremLevel
      justificationTag := "theorem-level AG/SCT exact-target lower transfer" }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

/-- Generic exact-theorem calibration object obtained from the
theorem-alignment route induced by an exact-calibration transfer.
Parametric in the transfer via `T`, `hTheory`, `hOrdinal`; the produced
sharp-theorem upper/lower bounds are the canonical alignment-route
bounds, which are definitionally identical to what
`(ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment ...).toSharpTheoremUpperBound`
(and the lower analogue) would produce, but inlined at universe 0 to
stay compatible with the rest of the AG calibration stack. -/
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

/-! ### Generic fieldwise route-equivalence theorems -/

/-- Both generic routes land on the same target profile. -/
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

/-- Generic route equivalence: upper theory. -/
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

/-- Generic route equivalence: upper ordinal ceiling. -/
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

/-- Generic route equivalence: upper evidence status. -/
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

/-- Generic route equivalence: overall calibration status. -/
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

/-- Generic route equivalence: extracted lower-bound theory. -/
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

/-- Generic route equivalence: extracted lower-bound ordinal ceiling. -/
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

/-- Generic route equivalence: extracted lower-bound evidence status. -/
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

/-- Generic tag-erased equality at the upper-bound level: given the
additional source-profile hypothesis matching
`sctExactUpperBound.theoryProfile`, the two generic routes' calibration
upper-bound records agree after tag erasure. -/
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

/-- Generic tag-erased equality at the lower-bound level: given the
additional source-profile hypothesis matching
`sctExactLowerBound.theoryProfile`, the two generic routes' calibration
lower-bound records agree after tag erasure. Stated symmetrically with
the upper-bound version through the route-built `lowerBound?` fields,
rather than against the raw `T.dstLower`. -/
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

/-- Generic presentation-erased equality at the **upper-bound** level.
Strictly stronger hypothesis-wise than the eraseTags version: the
source-calibration target profile need only agree on theory and ordinal
ceiling with the exact target, not on the full `SecondOrderTheoryProfile`
record. -/
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

/-- Generic presentation-erased equality at the **lower-bound** level.
Mirror of the upper-bound version; only `hTheory` and `hOrdinal` are
needed. Stated through the route-built `lowerBound?` fields,
symmetrically with the eraseTags lower-bound theorem. -/
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

/-! ### Full-calibration tag-erased equality

Note: the full-calibration-level `eraseJustificationTags` equality is
deliberately exposed only via the two fieldwise helpers
`..._eraseTags_eq_ofTheoremAlignment_upperBound` and
`..._eraseTags_eq_ofTheoremAlignment_lowerBound` above. A
full-`ReverseMathCalibration` equality-after-erasure theorem at the
generic level runs into `Ordinal`-universe polymorphism in the
`ReverseMathCalibration` record type; the concrete instantiation at
`artsGieslExactCalibrationTransferFromSct` already closes the
calibration-level erased equality by `rfl` via
`artsGieslConcreteExactTheoremCalibration_eraseTags_eq_viaTheoremAlignment`,
which is where downstream consumers cite it. -/

/-- Packaged generic route-equivalence summary. Consolidates the
upper-side and calibration-level fieldwise route-equivalence theorems
into a single conjunction (target profile, upper theory, upper
ordinal, upper status, overall calibration status). The lower-side
fieldwise theorems `_sameLowerTheory`, `_sameLowerOrdinal`,
`_sameLowerStatus` are kept as separate theorems rather than
in-lined here, because `ArtsGieslExactTheoremCalibration.toSharpLowerBound`
is universe-polymorphic via its internal `Classical.choose`; the
concrete-pair packaging theorem
`artsGieslConcreteExactTheoremCalibration_sameMathematicalContent_as_viaTheoremAlignment`
already bundles those at the canonical pair where universes resolve
cleanly. -/
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

/-- Packaged generic **semantic-content** route-equivalence summary.
Stronger than `sameMathematicalContent`: in addition to the 5 fieldwise
comparisons, carries the two presentation-erased bound equalities that
hold with only `hTheory` and `hOrdinal` (no full-profile hypothesis). -/
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
