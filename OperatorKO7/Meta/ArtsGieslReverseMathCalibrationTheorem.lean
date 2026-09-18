import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration
import OperatorKO7.Meta.ProofTheoreticRegister

/-!
# Arts-Giesl reverse-math calibration as a theorem

`artsGieslReverseMathCalibration` is a register object. This module states the
proved register facts as one theorem and compiles that the naive matching-bounds
exactness record is uninhabited. Mathematical reverse-math equivalence of the
Arts-Giesl license with `RCA₀ + WO(ω³)` remains `CalibrationStatus.conjectural`.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ArtsGieslReverseMathCalibrationTheorem

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ArtsGieslReverseMathCalibration

/-- **The calibration theorem.** Target and upper sit in the `FormalTheory`
order; matching-bounds exactness is impossible; the live status flag is
conjectural. -/
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
