import OperatorKO7.Meta.BoundaryGeneral.QECOmegaCapacity
import OperatorKO7.Meta.QuantumBoundary.KnillLaflammeOperator

/-!
# Knill-Laflamme correctability and Omega evidence

The operator-level Knill-Laflamme condition concerns a code projector and an error family. Omega concerns an operational terminal envelope paired with a licensed evidence channel. These are different carriers, so KL correctability alone does not determine Omega; an explicit mapping between operator errors and operational error classes is required.

The finite model pairs two operator errors with two operational classes. The operator error family satisfies the Knill-Laflamme condition. On the error-class carrier, echo evidence gives Omega one, while perfect syndrome information gives Omega zero. The same operator correctability result holds for both evidence choices.

Relation: finite `ErrorBranchStep (Fin 2)` for Omega and a concrete two-by-two real operator algebra for KL. Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OmegaKnillLaflammeBoundary

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.QECOmegaCapacity
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

abbrev KLM := OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.M

/-- Explicit coupling between the two operational error classes and the two
operator errors.  The equivalence prevents either operational class from being
unrelated to, or duplicating, an operator error. -/
structure CoupledKLOmegaModel where
  operatorErrors : Fin 2 → KLM
  classToOperator : Fin 2 ≃ Fin 2
  operatorErrors_match : ∀ c,
    operatorErrors (classToOperator.symm c) =
      OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.E c
  correctable :
    OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.KLCorrectable
      OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.P operatorErrors
      (1 : Matrix (Fin 2) (Fin 2) Real)

/-- The KL fixture coupled to the operational classes by the identity equivalence. -/
def liveCoupledKLOmegaModel : CoupledKLOmegaModel where
  operatorErrors := OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.E
  classToOperator := Equiv.refl (Fin 2)
  operatorErrors_match := by intro c; rfl
  correctable := OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.kl_holds

/-- The two-error-class carrier with echo evidence has one bit of Omega. -/
theorem twoError_echo_omega_eq_one :
    overproductionGap (ErrorBranchStep (Fin 2)) none
      unitSurface uniformChannelWeights echoChannel = 1 := by
  unfold overproductionGap terminalHartleyEntropy
  rw [error_terminalMultiplicity_eq_card, echoChannel_deficitBits_zero, sub_zero]
  norm_num [Real.logb]

/-- The same two-error-class carrier with perfect syndrome information has zero
Omega. -/
theorem twoError_perfectSyndrome_omega_eq_zero :
    overproductionGap (ErrorBranchStep (Fin 2)) none
      qecMu (qecNu (E := Fin 2)) (qecPerfectSyndrome (E := Fin 2)) = 0 :=
  qec_perfectSyndrome_omega_eq_zero

/-- The live operator-level two-error fixture satisfies Knill-Laflamme. -/
theorem twoError_operator_KL_correctable :
    OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.KLCorrectable
      OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.P
      OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.E
      (1 : Matrix (Fin 2) (Fin 2) Real) :=
  OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.kl_holds

/-- One coupled model satisfies Knill-Laflamme while the supplied evidence channel gives either zero or positive Omega. -/
theorem KL_correctability_alone_does_not_determine_omega :
    ∃ M : CoupledKLOmegaModel,
      OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.KLCorrectable
          OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.P M.operatorErrors
          (1 : Matrix (Fin 2) (Fin 2) Real) ∧
      (∀ c, M.operatorErrors (M.classToOperator.symm c) =
        OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.E c) ∧
      overproductionGap (ErrorBranchStep (Fin 2)) none
          unitSurface uniformChannelWeights echoChannel = 1 ∧
      overproductionGap (ErrorBranchStep (Fin 2)) none
          qecMu (qecNu (E := Fin 2)) (qecPerfectSyndrome (E := Fin 2)) = 0 :=
  ⟨liveCoupledKLOmegaModel,
    liveCoupledKLOmegaModel.correctable,
    liveCoupledKLOmegaModel.operatorErrors_match,
    twoError_echo_omega_eq_one,
    twoError_perfectSyndrome_omega_eq_zero⟩

/-- Perfect syndrome information gives zero Omega on the finite error-class carrier. KL correctability alone does not determine the evidence channel or Omega value. -/
theorem qec_omega_KL_scope_resolved :
    (overproductionGap (ErrorBranchStep (Fin 2)) none
        qecMu (qecNu (E := Fin 2)) (qecPerfectSyndrome (E := Fin 2)) = 0) ∧
    (overproductionGap (ErrorBranchStep (Fin 2)) none
        unitSurface uniformChannelWeights echoChannel ≠ 0) ∧
    OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.KLCorrectable
        OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.P
        OperatorKO7.Meta.QuantumBoundary.KnillLaflamme.E
        (1 : Matrix (Fin 2) (Fin 2) Real) := by
  constructor
  · exact twoError_perfectSyndrome_omega_eq_zero
  constructor
  · rw [twoError_echo_omega_eq_one]
    norm_num
  · exact twoError_operator_KL_correctable

end OperatorKO7.Meta.BoundaryGeneral.OmegaKnillLaflammeBoundary
