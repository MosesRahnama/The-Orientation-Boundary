import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# Finite QEC error-class capacity model for Omega

A source branches to one terminal state per error class. A perfect syndrome
channel names the error class exactly. Under a uniform prior the channel supplies
exactly the Hartley error-class envelope, so Omega closes to zero.
-/
set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.QECOmegaCapacity

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapOrder
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

inductive ErrorBranchStep (E : Type) : Option E → Option E → Prop where
  | emit (e : E) : ErrorBranchStep E none (some e)

section

variable {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]

omit [Fintype E] [DecidableEq E] [Nonempty E] in
/-- Error-class terminals are normal forms. -/
theorem error_terminal_normal (e : E) : NormalForm (ErrorBranchStep E) (some e) := by
  intro y h
  cases h

omit [Fintype E] [DecidableEq E] in
/-- The source itself is not terminal. -/
theorem error_source_not_normal : ¬ NormalForm (ErrorBranchStep E) none := by
  intro h
  let e : E := Classical.choice inferInstance
  exact h (some e) (ErrorBranchStep.emit e)

/-- Terminal support is exactly all `some e` states. -/
theorem error_terminalSupport_eq :
    terminalSupport (ErrorBranchStep E) none = Finset.univ.erase none := by
  classical
  ext x
  cases x with
  | none =>
      constructor
      · intro hx
        exact False.elim (error_source_not_normal (mem_terminalSupport.mp hx).2)
      · simp
  | some e =>
      constructor
      · intro _
        simp
      · intro _
        exact mem_terminalSupport.mpr
          ⟨reach_step (ErrorBranchStep.emit e), error_terminal_normal e⟩

/-- Terminal multiplicity is the number of error classes. -/
theorem error_terminalMultiplicity_eq_card :
    terminalMultiplicity (ErrorBranchStep E) none = Fintype.card E := by
  classical
  unfold terminalMultiplicity
  rw [error_terminalSupport_eq, Finset.card_erase_of_mem]
  · simp
  · simp

omit [Fintype E] [DecidableEq E] in
/-- The error-class branching system normalizes at its source. -/
theorem error_normalizingAt : NormalizingAt (ErrorBranchStep E) none := by
  intro y hy
  cases y with
  | none =>
      let e : E := Classical.choice inferInstance
      exact ⟨some e, reach_step (ErrorBranchStep.emit e), error_terminal_normal e⟩
  | some e => exact ⟨some e, reach_refl _, error_terminal_normal e⟩

/-- One direct-surface cell. -/
def qecMu : Fin 1 → Real := fun _ => 1

/-- Uniform syndrome/error-class prior. -/
noncomputable def qecNu : Fin 1 → E → Real := fun _ => uniformMass E

/-- Perfect syndrome readout: syndrome label `c` determines error class `c`. -/
noncomputable def qecPerfectSyndrome : Fin 1 → E → E → Real :=
  fun _ c => pointMass c

/-- The perfect syndrome mixture recovers the uniform error-class distribution. -/
theorem qecPerfectSyndrome_mixture (w : Fin 1) :
    (fun x : E => ∑ c : E, qecNu w c * qecPerfectSyndrome w c x) = uniformMass E := by
  classical
  funext x
  unfold qecNu qecPerfectSyndrome uniformMass pointMass
  rw [Finset.sum_eq_single x]
  · simp
  · intro b hb hbx
    have hxb : x ≠ b := fun h => hbx h.symm
    simp [hxb]
  · simp

/-- Direct uncertainty is the uniform error-class entropy. -/
theorem qec_condEntropyDirect_eq_log_card :
    condEntropyDirect qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) =
      Real.log (Fintype.card E : Real) := by
  unfold condEntropyDirect qecMu
  rw [Fin.sum_univ_one, one_mul, qecPerfectSyndrome_mixture]
  exact H_uniformMass_eq_log_card E

omit [Nonempty E] in
/-- Conditional entropy of the error class given the perfect syndrome is zero. -/
theorem qec_condEntropyLicensed_eq_zero :
    condEntropyLicensed qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) = 0 := by
  unfold condEntropyLicensed qecMu qecNu qecPerfectSyndrome
  rw [Fin.sum_univ_one, one_mul]
  apply Finset.sum_eq_zero
  intro c hc
  rw [H_pointMass]
  ring

/-- A perfect syndrome supplies the full error-class entropy in bits. -/
theorem qec_perfectSyndrome_deficitBits_eq_logb_card :
    deficitBits qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) =
      Real.logb 2 (Fintype.card E : Real) := by
  unfold deficitBits deficit
  rw [qec_condEntropyDirect_eq_log_card, qec_condEntropyLicensed_eq_zero]
  simp [Real.logb]

/-- The operational Hartley envelope is the same log-cardinality. -/
theorem qec_errorClass_hartley_eq_logb_card :
    terminalHartleyEntropy (ErrorBranchStep E) none =
      Real.logb 2 (Fintype.card E : Real) := by
  unfold terminalHartleyEntropy
  rw [error_terminalMultiplicity_eq_card]

/-- Perfect syndrome information equals the error-class Hartley envelope, so Omega is zero. -/
theorem qec_perfectSyndrome_omega_eq_zero :
    overproductionGap (ErrorBranchStep E) none qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) = 0 := by
  unfold overproductionGap
  rw [qec_errorClass_hartley_eq_logb_card,
    qec_perfectSyndrome_deficitBits_eq_logb_card, sub_self]

/-- For an arbitrary syndrome/evidence channel on the same error-class carrier,
zero Omega is exactly equality between licensed gain and the full error-class
Hartley envelope. -/
theorem qec_zero_omega_iff_full_syndrome_information
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    overproductionGap (ErrorBranchStep E) none μ ν r = 0 ↔
      deficitBits μ ν r = Real.logb 2 (Fintype.card E : Real) := by
  unfold overproductionGap
  rw [qec_errorClass_hartley_eq_logb_card]
  constructor <;> intro h <;> linarith

/-- Correctability in this finite perfect-syndrome model is capacity compatibility. -/
theorem qec_perfectSyndrome_capacityCompatible :
    CapacityCompatible (ErrorBranchStep E) none qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) := by
  unfold CapacityCompatible
  rw [qec_errorClass_hartley_eq_logb_card,
    qec_perfectSyndrome_deficitBits_eq_logb_card]

/-- The theorem gives zero Omega and full error-class information under the perfect syndrome channel. -/
theorem qec_omega_capacity_law :
    overproductionGap (ErrorBranchStep E) none qecMu (qecNu (E := E))
        (qecPerfectSyndrome (E := E)) = 0 ∧
    deficitBits qecMu (qecNu (E := E)) (qecPerfectSyndrome (E := E)) =
      Real.logb 2 (Fintype.card E : Real) :=
  ⟨qec_perfectSyndrome_omega_eq_zero,
    qec_perfectSyndrome_deficitBits_eq_logb_card⟩

end

end OperatorKO7.Meta.BoundaryGeneral.QECOmegaCapacity
