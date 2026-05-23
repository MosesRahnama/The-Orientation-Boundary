import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration

/-!
# Arts and Giesl Exact Calibration, Universal Closure

Single named-alias surface for the unconditional exact-calibration closure of
the Arts and Giesl soundness license at the `RCA₀ + WO(ω^3)` target.

The artifact already constructs the closure twice over:

- the SCT-anchored exact-transfer route through
  `artsGieslExactCalibrationTransferFromSct`, and
- the direct sharp-bounds route through
  `artsGieslDirectSharpTheoremUpperBound` and
  `artsGieslDirectSharpTheoremLowerBound`.

Both routes produce a `ReverseMathCalibration` object with
`status = CalibrationStatus.exact` on the target profile
`rca0WoOmega3TheoryProfile`, and both are unconditional on the typed AG
calibration carrier. This module names the closure under one paper-facing
identifier so downstream citations do not have to thread through the
particular route.

The provably-uninhabited `ArtsGieslMatchingBounds` schema records that the
older coarse `RCA₀ + Π⁰₂` lower-bound package does not directly match the
target on the original packages; the closure here uses theorem-level
upper / lower packages that do match the target by construction. Both layers
coexist: this module does not displace the honest record that the original
coarse lower-bound is below the target.
-/

namespace OperatorKO7.ArtsGieslExactCalibrationUniversal

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister
open OperatorKO7.ArtsGieslReverseMathCalibration

/-! ## Universal exact-calibration target -/

/-- Universal artifact-level statement: the Arts and Giesl soundness license
admits an unconditional exact calibration at the `RCA₀ + WO(ω^3)` target via
the SCT-anchored exact-transfer route. -/
theorem arts_giesl_exact_calibration_unconditional :
    artsGieslExactCalibration.status = CalibrationStatus.exact
      ∧ artsGieslExactCalibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslExactCalibration.targetProfile.ordinalCeiling? =
          some omegaPowThree
      ∧ artsGieslExactCalibration.upperBound.evidenceStatus =
          EvidenceStatus.theoremLevel
      ∧ (match artsGieslExactCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) :=
  artsGiesl_exactCalibration

/-- Universal artifact-level statement via the direct sharp-bounds route. -/
theorem arts_giesl_exact_calibration_unconditional_directRoute :
    let C := artsGieslExactCalibrationViaDirectSharpBounds
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) :=
  artsGiesl_exactCalibration_via_directSharpBounds

/-! ## Universal exact-theorem-calibration object -/

/-- Universal artifact-level statement: the concrete exact-theorem calibration
object on the SCT-anchored transfer route is exact at the `RCA₀ + WO(ω^3)`
target. -/
theorem arts_giesl_exact_theorem_calibration_unconditional :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
        CalibrationStatus.exact
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree :=
  ⟨rfl, rfl, rfl⟩

/-- Universal artifact-level statement: the concrete exact-theorem calibration
object on the theorem-alignment route is exact at the same target. -/
theorem arts_giesl_exact_theorem_calibration_unconditional_alignmentRoute :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
        CalibrationStatus.exact
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree :=
  ⟨rfl, rfl, rfl⟩

/-! ## Both routes agree on target and status -/

/-- Universal artifact-level statement: the SCT-transfer route and the
theorem-alignment route both yield the exact calibration on the same
target profile with the same status. The routes are mathematically
equivalent at the artifact-facing surface, while remaining distinct as
route objects. -/
theorem arts_giesl_both_routes_unconditional :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
        artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status
      ∧ artsGieslConcreteExactTheoremCalibration.calibration.targetProfile =
          artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile := by
  refine ⟨?_, ?_⟩
  · exact artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameStatus.symm
  · exact artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment_sameTarget.symm

end OperatorKO7.ArtsGieslExactCalibrationUniversal
