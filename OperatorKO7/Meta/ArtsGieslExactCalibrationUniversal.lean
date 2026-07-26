import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration

/-!
# Arts-Giesl Calibration Interfaces

This module exports a coarse calibration summary and conditional schemas for a
target at `RCA₀ + WO(omega^3)`. Status fields in the summary are record metadata.
The target-level upper and lower reverse-mathematical directions appear as
explicit hypotheses in the conditional schemas.
-/

namespace OperatorKO7.ArtsGieslExactCalibrationUniversal

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.ArtsGieslReverseMathCalibration

/-! ## Calibration summary -/

/--
Project the imported coarse upper and lower packages together with the target
status field. This declaration is a metadata summary; target-level reverse
implications are supplied separately.
-/
theorem arts_giesl_current_calibration_theorem_backed :
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural
      ∧ artsGieslCurrentCalibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslCurrentCalibration.upperBound.evidenceStatus =
          EvidenceStatus.theoremLevel
      ∧ (match artsGieslCurrentCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact OperatorKO7.ArtsGieslUpperBound.artsGieslTheoremUpperBound_status
  · change
      (match some OperatorKO7.ArtsGieslLowerBound.artsGieslTheoremLowerBound with
        | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
        | none => False)
    exact OperatorKO7.ArtsGieslLowerBound.artsGieslTheoremLowerBound_status

/--
Show that the witness type assembled from the imported coarse-status package is
uninhabited. The conclusion blocks that record-level shortcut and leaves the
conditional target schemas as the calibration interface.
-/
theorem arts_giesl_exact_calibration_metadata_shortcut_quarantined :
    ¬ ArtsGieslMatchingBounds
      ∧ ¬ ∃ C : ArtsGieslExactTheoremCalibration,
          C.calibration.upperBound =
              OperatorKO7.ArtsGieslUpperBound.artsGieslTheoremUpperBound
            ∧ C.calibration.lowerBound? =
              some OperatorKO7.ArtsGieslLowerBound.artsGieslTheoremLowerBound := by
  exact
    ⟨artsGieslMatchingBounds_uninhabited,
      artsGiesl_currentTheoremPackages_do_not_yield_exactTheoremCalibration⟩

/-- Metadata anchor identifying the coarse-summary and conditional-schema surface. -/
def arts_giesl_exact_calibration_quarantine_anchor : String :=
  "OperatorKO7.ArtsGieslExactCalibrationUniversal." ++
    "arts_giesl_exact_calibration_metadata_shortcut_quarantined"

end OperatorKO7.ArtsGieslExactCalibrationUniversal
