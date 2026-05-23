import OperatorKO7.Meta.ArtsGieslExactCalibrationUniversal

/-!
# Reach test for `Meta/ArtsGieslExactCalibrationUniversal.lean`

Exercises every public theorem of the unconditional Arts and Giesl exact-
calibration alias module. The five core targets are the SCT-transfer-route
calibration, the direct-sharp-bounds-route calibration, the SCT-transfer-route
exact-theorem-calibration object, the theorem-alignment-route exact-theorem-
calibration object, and the route-agreement theorem.
-/

namespace OperatorKO7.Test.ArtsGieslExactCalibrationUniversalReach

open OperatorKO7
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.ArtsGieslReverseMathCalibration
open OperatorKO7.ArtsGieslExactCalibrationUniversal

#check @OperatorKO7.ArtsGieslExactCalibrationUniversal.arts_giesl_exact_calibration_unconditional
#check @OperatorKO7.ArtsGieslExactCalibrationUniversal.arts_giesl_exact_calibration_unconditional_directRoute
#check @OperatorKO7.ArtsGieslExactCalibrationUniversal.arts_giesl_exact_theorem_calibration_unconditional
#check @OperatorKO7.ArtsGieslExactCalibrationUniversal.arts_giesl_exact_theorem_calibration_unconditional_alignmentRoute
#check @OperatorKO7.ArtsGieslExactCalibrationUniversal.arts_giesl_both_routes_unconditional

/-! ## Concrete projection exercises -/

/-- The SCT-anchored exact calibration is at `CalibrationStatus.exact`. -/
example : artsGieslExactCalibration.status = CalibrationStatus.exact :=
  arts_giesl_exact_calibration_unconditional.1

/-- The SCT-anchored exact calibration hits the `RCA₀ + WO(ω^3)` target theory. -/
example :
    artsGieslExactCalibration.targetProfile.theory =
      FormalTheory.RCA0_WO_omega3 :=
  arts_giesl_exact_calibration_unconditional.2.1

/-- The SCT-anchored exact calibration hits the `ω^3` target ordinal. -/
example :
    artsGieslExactCalibration.targetProfile.ordinalCeiling? =
      some omegaPowThree :=
  arts_giesl_exact_calibration_unconditional.2.2.1

/-- The concrete exact-theorem calibration object is at exact status. -/
example :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      CalibrationStatus.exact :=
  rfl

/-- The Path C concrete exact-theorem calibration object is at exact status. -/
example :
    artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status =
      CalibrationStatus.exact :=
  rfl

/-- Both routes agree on the exact target profile. -/
example :
    artsGieslConcreteExactTheoremCalibration.calibration.targetProfile =
      artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.targetProfile :=
  rfl

/-- Both routes agree on the calibration status. -/
example :
    artsGieslConcreteExactTheoremCalibration.calibration.status =
      artsGieslConcreteExactTheoremCalibration_viaTheoremAlignment.calibration.status :=
  rfl

end OperatorKO7.Test.ArtsGieslExactCalibrationUniversalReach
