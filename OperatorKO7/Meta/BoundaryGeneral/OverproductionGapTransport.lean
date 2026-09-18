import OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitativeKO7Transport
import OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryDetermination

/-!
# Transport laws for the overproduction gap

The operational half of Omega is invariant under exact relation isomorphism.
Because the licensed-channel deficit is independent data, the full gap is
therefore invariant under a relation isomorphism when the channel is held fixed.
Mere forward simulation is not enough: the canonical two-terminal fork can be
collapsed onto a one-terminal Boolean fork by a step-preserving map, changing
Omega by one bit against the same echo channel.

The final section answers the coupling question raised by BoundaryDetermination.
A `ReleaseIso` determines the released ensemble law but says nothing about the
licensed information channel used by Omega.  Even with identity boundary and
identical release data, changing the channel from echo to resolving changes the
gap.  Thus boundary/release determination alone does not determine Omega; a
channel coupling is load bearing.

Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor
open OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryDetermination
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory

noncomputable section

universe u v

/-- Exact relation isomorphism preserves terminal Hartley entropy. -/
theorem relIso_terminalHartleyEntropy_eq
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB) (source : A) :
    terminalHartleyEntropy RA source =
      terminalHartleyEntropy RB (e.toEquiv source) := by
  unfold terminalHartleyEntropy
  rw [e.terminalMultiplicity_eq source]

/-- **W4 positive theorem.** Exact operational isomorphism leaves Omega
unchanged when the licensed channel is held fixed. -/
theorem relIso_overproductionGap_eq
    {A : Type} {B : Type} [Fintype A] [Fintype B]
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB) (source : A)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap RA source μ ν r =
      overproductionGap RB (e.toEquiv source) μ ν r := by
  unfold overproductionGap
  rw [relIso_terminalHartleyEntropy_eq e source]

/-! ## Simulation is not enough -/

/-- Forward one-step simulation.  It need not reflect edges or preserve distinct
terminal states. -/
def ForwardSimulation {A B : Type}
    (f : A → B) (RA : A → A → Prop) (RB : B → B → Prop) : Prop :=
  ∀ ⦃x y⦄, RA x y → RB (f x) (f y)

/-- Deterministic one-edge Boolean fork. -/
inductive BoolForkStep : Bool → Bool → Prop
  | go : BoolForkStep true false

/-- Collapse both canonical Fork3 verdicts to the one Boolean terminal. -/
def fork3Collapse : Fork3 → Bool
  | .source => true
  | .equal => false
  | .different => false

/-- The collapse is a forward simulation. -/
theorem fork3Collapse_forwardSimulation :
    ForwardSimulation fork3Collapse Fork3Step BoolForkStep := by
  intro x y h
  cases h <;> exact BoolForkStep.go

/-- `false` is the only Boolean terminal. -/
theorem boolFork_terminalSupport_eq :
    terminalSupport BoolForkStep true = {false} := by
  classical
  ext b
  cases b with
  | false =>
      simp only [mem_terminalSupport, Finset.mem_singleton]
      constructor
      · intro _; trivial
      · intro _
        exact ⟨reach_step BoolForkStep.go, by intro y h; cases h⟩
  | true =>
      simp only [mem_terminalSupport, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hnf⟩
        exact False.elim (hnf false BoolForkStep.go)
      · intro h
        cases h

/-- The simulated Boolean system has terminal multiplicity one. -/
theorem boolFork_terminalMultiplicity_eq_one :
    terminalMultiplicity BoolForkStep true = 1 := by
  simp [terminalMultiplicity, boolFork_terminalSupport_eq]

/-- The simulated Boolean system has zero Hartley branch entropy. -/
theorem boolFork_terminalHartleyEntropy_eq_zero :
    terminalHartleyEntropy BoolForkStep true = 0 := by
  simp [terminalHartleyEntropy, boolFork_terminalMultiplicity_eq_one]

/-- Against the echo channel, the simulated Boolean system has zero gap. -/
theorem boolFork_echo_overproduction_eq_zero :
    overproductionGap BoolForkStep true unitSurface uniformChannelWeights echoChannel = 0 := by
  unfold overproductionGap
  rw [boolFork_terminalHartleyEntropy_eq_zero, echoChannel_deficitBits_zero]
  ring

/-- **W4 negative theorem.** A forward simulation can collapse the two terminal
branches and change Omega. -/
theorem forwardSimulation_does_not_preserve_overproduction :
    ForwardSimulation fork3Collapse Fork3Step BoolForkStep ∧
    overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap BoolForkStep (fork3Collapse Fork3.source)
        unitSurface uniformChannelWeights echoChannel := by
  refine ⟨fork3Collapse_forwardSimulation, ?_⟩
  simp [fork3Collapse, fork3_raw_overproduction_eq_one,
    boolFork_echo_overproduction_eq_zero]

/-! ## Boundary-isomorphism bridge -/

/-- Every `BoundaryIso` is an exact relation isomorphism of the restricted
boundary dynamics. -/
noncomputable def boundaryIsoRelIso
    {A B : LicensingDatum} (e : BoundaryIso A B) :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso
      (restrictedDynamics A) (restrictedDynamics B) where
  toEquiv := e.toEquiv
  map_rel_iff := e.dynamics_iff _ _

/-- Boundary isomorphism preserves the Hartley emission term. -/
theorem boundaryIso_terminalHartleyEntropy_eq
    {A B : LicensingDatum}
    [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
    (e : BoundaryIso A B) (source : BdCarrier A) :
    terminalHartleyEntropy (restrictedDynamics A) source =
      terminalHartleyEntropy (restrictedDynamics B) (e.toEquiv source) :=
  relIso_terminalHartleyEntropy_eq (boundaryIsoRelIso e) source

/-- Boundary isomorphism preserves the full gap when the evidence channel is
literally the same audited channel. -/
theorem boundaryIso_overproductionGap_eq
    {A B : LicensingDatum}
    [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
    (e : BoundaryIso A B) (source : BdCarrier A)
    {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap (restrictedDynamics A) source μ ν r =
      overproductionGap (restrictedDynamics B) (e.toEquiv source) μ ν r :=
  relIso_overproductionGap_eq (boundaryIsoRelIso e) source μ ν r

/-! ## Why ReleaseIso alone cannot determine Omega -/

/-- Identity boundary transport and identical release data satisfy the coupled
`ReleaseIso` law. -/
noncomputable def releaseDataA_reflIso :
    ReleaseIso staticBoolBoundaryIso releaseDataA releaseDataA where
  mass_commutes := fun _ => rfl
  release_commutes := fun _ => rfl

/-- For any operational relation, changing only the canonical evidence channel
from echo to perfectly resolving lowers the gap by exactly one bit. -/
theorem echo_gap_minus_resolving_gap_eq_one
    {T : Type} [Fintype T] (R : T → T → Prop) (source : T) :
    overproductionGap R source unitSurface uniformChannelWeights echoChannel -
      overproductionGap R source unitSurface uniformChannelWeights resolvingChannel = 1 := by
  unfold overproductionGap
  rw [echoChannel_deficitBits_zero, resolvingChannel_deficitBits_eq_one]
  ring

/-- **Sharp coupled-determination answer.** Even an identity boundary isomorphism
with identical release data does not determine Omega unless the licensed
information channel is also coupled. -/
theorem releaseIso_alone_does_not_determine_overproduction :
    Nonempty (ReleaseIso staticBoolBoundaryIso releaseDataA releaseDataA) ∧
    overproductionGap (restrictedDynamics staticBoolDatum) (boolBoundary false)
        unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap (restrictedDynamics staticBoolDatum) (boolBoundary false)
        unitSurface uniformChannelWeights resolvingChannel := by
  refine ⟨⟨releaseDataA_reflIso⟩, ?_⟩
  have h := echo_gap_minus_resolving_gap_eq_one
    (restrictedDynamics staticBoolDatum) (boolBoundary false)
  intro heq
  rw [heq, sub_self] at h
  norm_num at h

/-- W4 receipt: exact isomorphism invariance, a simulation counterexample, and
the proof that BoundaryDetermination's release coupling must be augmented by a
channel coupling to determine Omega. -/
theorem overproduction_transport_law :
    (∀ {A B : Type} [Fintype A] [Fintype B]
      {RA : A → A → Prop} {RB : B → B → Prop}
      (e : OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso RA RB) (source : A)
      {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
      (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ),
      overproductionGap RA source μ ν r =
        overproductionGap RB (e.toEquiv source) μ ν r) ∧
    ForwardSimulation fork3Collapse Fork3Step BoolForkStep ∧
    (overproductionGap Fork3Step Fork3.source unitSurface uniformChannelWeights echoChannel ≠
      overproductionGap BoolForkStep (fork3Collapse Fork3.source)
        unitSurface uniformChannelWeights echoChannel) ∧
    Nonempty (ReleaseIso staticBoolBoundaryIso releaseDataA releaseDataA) :=
  by
    refine ⟨?_, fork3Collapse_forwardSimulation,
      forwardSimulation_does_not_preserve_overproduction.2,
      ⟨releaseDataA_reflIso⟩⟩
    intro A B instA instB RA RB e source X W Cn instX instW instCn μ ν r
    exact relIso_overproductionGap_eq e source μ ν r

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport
