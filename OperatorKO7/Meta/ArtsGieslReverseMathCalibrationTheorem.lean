import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration
import OperatorKO7.Meta.ProofTheoreticRegister

/-!
# Arts-Giesl reverse-math calibration as a theorem

`artsGieslReverseMathCalibration` records theory profiles and status fields.
This module proves its target and upper values, their order relation, and that
`ArtsGieslMatchingBounds` is uninhabited. Reverse-mathematical equivalence of
the Arts-Giesl license with `RCA₀ + WO(ω³)` remains `CalibrationStatus.conjectural`.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ArtsGieslReverseMathCalibrationTheorem

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ArtsGieslReverseMathCalibration

/-- Proves the recorded target and upper theory values, their order, that
`ArtsGieslMatchingBounds` is uninhabited, and the conjectural calibration status. -/
theorem artsGieslReverseMathCalibration_theorem :
    artsGieslReverseMathCalibration.target = FormalTheory.RCA0_WO_omega3 ∧
    artsGieslReverseMathCalibration.upperBenchmark = FormalTheory.WO_epsilon0 ∧
    artsGieslReverseMathCalibration.target <
      artsGieslReverseMathCalibration.upperBenchmark ∧
    ¬ ArtsGieslMatchingBounds ∧
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural :=
  ⟨arts_giesl_reverse_math_target,
    rfl,
    artsGieslReverseMathCalibration.targetBelowUpper,
    artsGieslMatchingBounds_uninhabited,
    artsGieslCurrentCalibration_status⟩

end OperatorKO7.Meta.ArtsGieslReverseMathCalibrationTheorem
