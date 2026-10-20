import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapLowerBound
import OperatorKO7.Meta.InformationalIncompleteness.SemideciderCollapseSchema

/-!
# Omega on the halting-collapse envelope

W28 asked for one computed Ω lower bound on the halting semidecider collapse
carrier. `JointSemideciderSchema` is a decision-procedure constructor, not a
finite rewriting relation, so it does not by itself determine Omega. The
computed bound lives on the two-outcome halt/loop star (`starStep 2`), the
smallest envelope that can host a halt-versus-loop query, with the echo channel
as zero licensed evidence.

The bound is carrier-specific: the same accounting on `starStep m` yields
`log₂ m`, not a uniform constant across Gödel, Rice, Tarski, and halting.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.HaltingCollapseOmega

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapLowerBound
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.SemideciderCollapseSchema
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

noncomputable section

/-- The two-outcome halt/loop envelope. -/
def haltLoopStep : Fin 3 → Fin 3 → Prop := starStep 2

theorem one_le_two : 1 ≤ (2 : ℕ) := by decide

theorem two_logb : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
  norm_cast
  exact Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)

/-- Echo channel on the halt/loop star has zero licensed gain. -/
theorem haltLoop_echo_deficitBits_zero :
    deficitBits unitSurface (uniformRoleWeights 2) (roleEcho 2) = 0 :=
  (deficitBits_eq_zero_iff _ _ _).mpr
    (circular_reference_zero_deficit unitSurface (uniformRoleWeights 2)
      (roleEcho 2) (uniformRoleWeights_sum_one one_le_two)
      (fun _ _ => (1 : ℝ) / 2) (fun _ _ => rfl))

/-- Hartley entropy of the halt/loop envelope is one bit. -/
theorem haltLoop_hartley_eq_one :
    terminalHartleyEntropy haltLoopStep 0 = 1 := by
  unfold haltLoopStep
  rw [star_terminalHartleyEntropy one_le_two, two_logb]

/-- **The computed bound.** Ω on the halt/loop star against zero evidence is 1. -/
theorem haltLoop_omega_eq_one :
    overproductionGap haltLoopStep 0 unitSurface (uniformRoleWeights 2)
      (roleEcho 2) = 1 := by
  unfold haltLoopStep
  rw [roleEcho_gap_log one_le_two, two_logb]

/-- W28 bridge: lowerBits = 1, evidenceUpperBits = 0, echo channel explicit. -/
def haltLoopZeroEvidenceBridge :
    QuantitativeObstructionBridge haltLoopStep 0 unitSurface
      (uniformRoleWeights 2) (roleEcho 2) where
  lowerBits := 1
  evidenceUpperBits := 0
  evidenceUpper_lt_lower := by norm_num
  envelopeLower := by
    rw [haltLoop_hartley_eq_one]
  evidenceUpper := by
    rw [haltLoop_echo_deficitBits_zero]

/-- The inhabited bridge is a boundary event. -/
theorem haltLoop_boundaryEvent :
    BoundaryEvent haltLoopStep 0 unitSurface (uniformRoleWeights 2)
      (roleEcho 2) :=
  haltLoopZeroEvidenceBridge.boundaryEvent

/-- The collapse schema manufactures a decision procedure. That is not Omega. -/
def collapse_supplies_decision
    {Machine Input : Type} (H : Machine → Input → Prop)
    (S : JointSemideciderSchema (Machine × Input)
      (fun x y : Machine × Input => x = y ∧ H x.1 x.2)) :
    ∀ x y : Machine × Input, Decidable (x = y ∧ H x.1 x.2) :=
  halting_semidecider_collapse_decides H S

/-- A resolving audit of the same envelope closes the gap: the numeric face of
holding a decision. -/
theorem haltLoop_resolving_gap_zero :
    overproductionGap haltLoopStep 0 unitSurface (uniformRoleWeights 2)
      (roleResolving 2) = 0 := by
  unfold haltLoopStep
  exact roleResolving_gap_zero_m one_le_two

/-- The bound is carrier-specific: arity 4 yields two bits, not one. -/
theorem haltLoop_omega_not_uniform :
    overproductionGap (starStep 2) 0 unitSurface (uniformRoleWeights 2)
        (roleEcho 2) ≠
      overproductionGap (starStep 4) 0 unitSurface (uniformRoleWeights 4)
        (roleEcho 4) := by
  have h2 := roleEcho_gap_log (by decide : 1 ≤ 2)
  have h4 := roleEcho_gap_log (by decide : 1 ≤ 4)
  have hlog2 : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := two_logb
  have hlog4 : Real.logb 2 ((4 : ℕ) : ℝ) = 2 := by
    norm_cast
    unfold Real.logb
    have hmul : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 * 2 := by norm_num
      rw [this, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hmul]
    field_simp [log_two_ne_zero]
  rw [h2, h4, hlog2, hlog4]
  norm_num

end

end OperatorKO7.Meta.InformationalIncompleteness.HaltingCollapseOmega
