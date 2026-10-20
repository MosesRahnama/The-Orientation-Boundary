import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Quantitative

/-!
# Terminal abstraction monotonicity for Omega

A finite abstraction is represented by a map from concrete states to abstract
states that maps concrete terminal support into abstract terminal support and is
surjective onto the abstract support.  Therefore abstraction cannot increase the
number of reachable terminal alternatives.  With the evidence channel held
fixed, it cannot increase Omega either.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapAbstraction

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork

/-- A finite abstraction maps the concrete terminal support onto the abstract terminal support. -/
structure TerminalAbstraction
    {A B : Type} [Fintype A] [Fintype B]
    (RA : A → A → Prop) (a : A) (RB : B → B → Prop) (b : B) where
  map : B → A
  mapsTerminal : Set.MapsTo map (↑(terminalSupport RB b) : Set B)
    (↑(terminalSupport RA a) : Set A)
  ontoTerminal : Set.SurjOn map (↑(terminalSupport RB b) : Set B)
    (↑(terminalSupport RA a) : Set A)

/-- A support-surjective abstraction cannot increase the number of reachable terminal states. -/
theorem terminalMultiplicity_le_of_abstraction
    {A B : Type} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {a : A} {RB : B → B → Prop} {b : B}
    (F : TerminalAbstraction RA a RB b) :
    terminalMultiplicity RA a ≤ terminalMultiplicity RB b := by
  unfold terminalMultiplicity
  exact Finset.card_le_card_of_surjOn F.map F.ontoTerminal

/-- Hartley terminal entropy cannot increase under a support-surjective abstraction when the abstract system normalizes. -/
theorem terminalHartleyEntropy_le_of_abstraction
    {A B : Type} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {a : A} {RB : B → B → Prop} {b : B}
    (F : TerminalAbstraction RA a RB b)
    (hA : NormalizingAt RA a) :
    terminalHartleyEntropy RA a ≤ terminalHartleyEntropy RB b := by
  unfold terminalHartleyEntropy
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast terminalMultiplicity_pos_of_normalizingAt hA
  · exact_mod_cast terminalMultiplicity_le_of_abstraction F

/-- Holding the evidence channel fixed, a support-surjective finite abstraction cannot increase Omega. -/
theorem overproductionGap_le_of_abstraction
    {A B : Type} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {a : A} {RB : B → B → Prop} {b : B}
    (F : TerminalAbstraction RA a RB b)
    (hA : NormalizingAt RA a)
    {X W C : Type} [Fintype X] [Fintype W] [Fintype C]
    (μ : W → Real) (ν : W → C → Real) (r : W → C → X → Real) :
    overproductionGap RA a μ ν r ≤ overproductionGap RB b μ ν r := by
  unfold overproductionGap
  have hH := terminalHartleyEntropy_le_of_abstraction F hA
  linarith

/-- The Fork3 guard maps both raw terminal verdicts to the licensed equal verdict and is surjective on terminal support. -/
def fork3GuardAbstraction :
    TerminalAbstraction Fork3LicensedStep Fork3.source Fork3Step Fork3.source where
  map := fun _ => Fork3.equal
  mapsTerminal := by
    intro x hx
    rw [fork3_licensed_terminalSupport_eq]
    simp
  ontoTerminal := by
    intro y hy
    rw [fork3_licensed_terminalSupport_eq] at hy
    have hyEq : y = Fork3.equal := by simpa using hy
    subst y
    refine ⟨Fork3.equal, ?_, rfl⟩
    rw [fork3_raw_terminalSupport_eq]
    simp

/-- The abstraction theorem gives an Omega inequality for the Fork3 guarded repair. -/
theorem fork3_guard_abstraction_lowers_omega :
    overproductionGap Fork3LicensedStep Fork3.source
        unitSurface uniformChannelWeights echoChannel ≤
      overproductionGap Fork3Step Fork3.source
        unitSurface uniformChannelWeights echoChannel := by
  exact overproductionGap_le_of_abstraction fork3GuardAbstraction
    fork3_licensed_normalizingAt_source
    unitSurface uniformChannelWeights echoChannel

/-- The Fork3 guard abstraction lowers the Omega gap by one bit. -/
theorem fork3_guard_abstraction_strict :
    overproductionGap Fork3LicensedStep Fork3.source
        unitSurface uniformChannelWeights echoChannel <
      overproductionGap Fork3Step Fork3.source
        unitSurface uniformChannelWeights echoChannel := by
  rw [fork3_licensed_overproduction_eq_zero, fork3_raw_overproduction_eq_one]
  norm_num

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapAbstraction



