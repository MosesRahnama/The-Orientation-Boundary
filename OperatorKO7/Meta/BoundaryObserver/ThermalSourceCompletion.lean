import OperatorKO7.Meta.BoundaryObserver.SourceApexInstrument
import OperatorKO7.Meta.BoundaryObserver.ThermalStaircase
import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics

/-!
# Thermal and same-source boundary completion

The physical experiment begins with one state, a Gibbs bath at a strictly positive
inverse temperature and a joint unitary. Heat is the energy gained by that bath,
not a declaration about external work. The source has one retained record and
an independent charge for the logical reading. Entropy of that retained memory
is not deleted when deriving a cycle bound.

A finite high-gap swap and a finite low-dissipation staircase use different baths
and have different heat limits. The strong infinite-stage entropy claim requires
uniform control of entropy tails, not merely convergence of states in trace norm.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver.ThermalSourceCompletion

open BoundaryReconstruction.Thermal
open BoundarySingularity.Thermal

/-- A full-rank two-level state never has an exactly pure output from any
finite-bath joint Gibbs operation, but finite baths approximate the zero-entropy
boundary arbitrarily closely. The inverse temperature is strictly positive. -/
theorem finiteFullRankResetBoundary
    {rho : Matrix Bool Bool ℂ} (hrho : rho.PosDef) (htr : rho.trace = 1)
    {β : ℝ} (hβ : 0 < β) :
    (∀ {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
        (u : Matrix.unitaryGroup (Bool × κ) ℂ)
        {h : Matrix κ κ ℂ} (hh : h.IsHermitian),
        0 < entropy (marginalLeft (thermalJoint u rho hh β))) ∧
    (∀ η : ℝ, 0 < η → ∃ E : ℝ,
       entropy (marginalLeft (thermalJoint
         OperatorKO7.Meta.BoundaryObserver.ThermalReset.swapUnitary rho
         (OperatorKO7.Meta.BoundaryObserver.ThermalReset.twoLevel_hermitian E) β)) < η) :=
  OperatorKO7.Meta.BoundaryObserver.ThermalReset.reset_boundary hrho htr β hβ

/-- The single-swap gap route has divergent heat; a separately constructed
finite staircase approaches Landauer heat with arbitrarily small entropy and
dissipation error. Neither result identifies heat with external work. -/
theorem fairPairTwoThermalRegimes {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto
      (fun E : ℝ => reservoirHeat
        OperatorKO7.Meta.BoundaryObserver.ThermalReset.swapUnitary
        fairPair
        (OperatorKO7.Meta.BoundaryObserver.ThermalReset.twoLevel_hermitian E) β)
      Filter.atTop Filter.atTop ∧
    (∀ η : ℝ, 0 < η →
      ∃ T : OperatorKO7.Meta.BoundaryObserver.ThermalStaircase.ThermalOperation Bool,
        entropy (T.output fairPair β) < η ∧
        |β * T.heat fairPair β - Real.log 2| < η) :=
  ⟨OperatorKO7.Meta.BoundaryObserver.ThermalStaircase.fair_pair_single_swap_heat_diverges hβ,
   fun _ hη =>
     OperatorKO7.Meta.BoundaryObserver.ThermalStaircase.fair_pair_heat_attains hβ hη⟩

/-- The geometric finite stages have both quantified entropy and energy tail
controls, hence physical entropy and heat limits. This does not assert entropy
continuity for arbitrary trace-norm convergent states. -/
def GuardedGeometricLimitGoal (q r : ℝ) : Prop :=
    ReconstructionLimitThermodynamics.UniformFiniteEntropyTailControl q ∧
    ReconstructionLimitThermodynamics.UniformFiniteEnergyTailControl q r ∧
    Filter.Tendsto
      (fun n => entropy (ReconstructionLimitThermodynamics.geometricDensity q n))
      Filter.atTop
      (nhds (ReconstructionLimitThermodynamics.infiniteEntropy q)) ∧
    Filter.Tendsto
      (fun n => ReconstructionLimitThermodynamics.geometricHeat q r n)
      Filter.atTop
      (nhds (ReconstructionLimitThermodynamics.infiniteHeat q r))

theorem guardedGeometricLimitGoal
    {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    GuardedGeometricLimitGoal q r :=
  ⟨ReconstructionLimitThermodynamics.geometric_uniform_entropy_tails hq0 hq1,
   ReconstructionLimitThermodynamics.geometric_uniform_energy_tails
     hq0.le hq1 hr0 hr1,
   ReconstructionLimitThermodynamics.geometricEntropy_limit_by_license hq0 hq1,
   ReconstructionLimitThermodynamics.geometricHeat_limit_by_license
     hq0.le hq1 hr0 hr1⟩

/-- A counterexample rules out promotion of trace-norm convergence to entropy
convergence: the states approach a pure state, but their entropy tails are
not uniformly controlled. -/
theorem entropyTailNegativeControl :
    Filter.Tendsto
      ReconstructionLimitThermodynamics.controlledLogarithmicState
      Filter.atTop (nhds ReconstructionLimitThermodynamics.pureState) ∧
    ¬ ReconstructionLimitThermodynamics.UniformTailControl
      (fun n k => Real.negMulLog
        (ReconstructionLimitThermodynamics.controlledLogarithmicState n k)) :=
  ⟨ReconstructionLimitThermodynamics.controlledLogarithmicState_tendsto,
   ReconstructionLimitThermodynamics.controlledLogarithmic_not_uniformTailControl⟩

/-- The actual system entropy, including its final memory, remains explicitly
in the cycle's Landauer inequality. A source recording cost is not substituted
for reservoir heat. -/
theorem physicalHeatBoundsEntropyDrop
    {n m : ℕ} (e : UniversalObservation.Reconstruction.ThermalExperiment n m) :
    UniversalObservation.Reconstruction.entropyDrop e ≤
      e.β * UniversalObservation.Reconstruction.heat e := by
  have h := UniversalObservation.Reconstruction.thermalIdentityGoal n m e
  rcases h with ⟨hbal, hcorr, hrel⟩
  linarith


/-- Both limits use the same states and their separate uniform-tail conditions. -/
theorem entropyEnergyJointLimit_of_uniformTails
    (p : ℕ → ℕ → ℝ) (pinf : ℕ → ℝ)
    (E : ℕ → ℕ → ℝ) (Einf : ℕ → ℝ)
    (hp : ∀ n, Summable (fun k => Real.negMulLog (p n k)))
    (hpinf : Summable (fun k => Real.negMulLog (pinf k)))
    (hEp : ∀ n, Summable (fun k => E n k * p n k))
    (hEinf : Summable (fun k => Einf k * pinf k))
    (hpt : ∀ k, Filter.Tendsto (fun n => p n k) Filter.atTop (nhds (pinf k)))
    (hEt : ∀ k, Filter.Tendsto (fun n => E n k) Filter.atTop (nhds (Einf k)))
    (hEnt : ReconstructionLimitThermodynamics.UniformTailControl
      (fun n k => Real.negMulLog (p n k)))
    (hEnergy : ReconstructionLimitThermodynamics.UniformTailControl
      (fun n k => E n k * p n k)) :
    Filter.Tendsto (fun n => ∑' k, Real.negMulLog (p n k))
      Filter.atTop (nhds (∑' k, Real.negMulLog (pinf k))) ∧
    Filter.Tendsto (fun n => ∑' k, E n k * p n k)
      Filter.atTop (nhds (∑' k, Einf k * pinf k)) :=
  ⟨ReconstructionLimitThermodynamics.entropy_tendsto_of_uniformTailControl
     p pinf hp hpinf hpt hEnt,
   ReconstructionLimitThermodynamics.energy_tendsto_of_uniformTailControl
     p pinf E Einf hEp hEinf hpt hEt hEnergy⟩

/-- The declared geometric states and Hamiltonians satisfy both tail conditions. -/
theorem geometricJointEntropyEnergyTailLicense
    {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ReconstructionLimitThermodynamics.UniformFiniteEntropyTailControl q ∧
    ReconstructionLimitThermodynamics.UniformFiniteEnergyTailControl q r ∧
    Filter.Tendsto
      (fun n => entropy (ReconstructionLimitThermodynamics.geometricDensity q n))
      Filter.atTop
      (nhds (ReconstructionLimitThermodynamics.infiniteEntropy q)) ∧
    Filter.Tendsto
      (fun n => BoundaryReconstruction.Thermal.meanEnergy
        (ReconstructionLimitThermodynamics.geometricHamiltonian r n)
        (ReconstructionLimitThermodynamics.geometricDensity q n))
      Filter.atTop
      (nhds (ReconstructionLimitThermodynamics.infiniteMeanEnergy q r)) :=
  ⟨ReconstructionLimitThermodynamics.geometric_uniform_entropy_tails hq0 hq1,
   ReconstructionLimitThermodynamics.geometric_uniform_energy_tails
     hq0.le hq1 hr0 hr1,
   ReconstructionLimitThermodynamics.geometricEntropy_limit_by_license hq0 hq1,
   ReconstructionLimitThermodynamics.geometricMeanEnergy_limit_by_license
     hq0.le hq1 hr0 hr1⟩

/-- Convergence to a pure state does not supply the entropy-tail condition. -/
theorem noUnlicensedEntropyLimit :
    Filter.Tendsto
      ReconstructionLimitThermodynamics.controlledLogarithmicState
      Filter.atTop (nhds ReconstructionLimitThermodynamics.pureState) ∧
    ¬ ReconstructionLimitThermodynamics.UniformTailControl
      (fun n k => Real.negMulLog
        (ReconstructionLimitThermodynamics.controlledLogarithmicState n k)) :=
  entropyTailNegativeControl

end OperatorKO7.Meta.BoundaryObserver.ThermalSourceCompletion

namespace UniversalObservation.Reconstruction
namespace ThermalSourceCompletion

open SourceApexInstrument
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Operational

/-- The actual CNOT source satisfies the single-source instrument, Gibbs,
recorded-branch, prior, stopped-protocol, heat and information premises
simultaneously. Each native branch is tested for all matrices through the
instrument law, not by agreement at a single endpoint. -/
def SameSourceCNOTGoal : Prop :=
    ApexInstanceGoal quantumData qubit (Fin 2) Unit (Fin 2) Unit (Fin 2)
      cnotSourceContract cnotSource cnotSourceBinding
      (cnotProtocolData cnotSource) 2 ∧
    ImplementsInstrument quantumData qubit (Fin 2) cnotSource
      quantumData_realization cnotSourceExperiment sourceCoordinateProjector ∧
    (∀ z y : Fin 2,
      quantumData.weight (cnotSource.branch y) (basisState qubit z) =
        if y = z then 1 else 0) ∧
    (∀ (u : Unit) (z : Fin 2),
      (cnotProtocolData cnotSource).protocol.initialJoint.mass (u,z) = 1 / 2) ∧
    (Protocol.conditionalExpectedCost (cnotProtocolData cnotSource).protocol
        (cnotProtocolData cnotSource).rounds
        (cnotProtocolData cnotSource).bank = 1) ∧
    (spectralMatrix cnotSourceExperiment.initialSystem =
      sourceEnsemble quantumData_realization (cnotProtocolData cnotSource)) ∧
    (cnotSourceExperiment.β * heat cnotSourceExperiment =
      entropyDrop cnotSourceExperiment +
        correlation cnotSourceExperiment + bathRelativeEntropy cnotSourceExperiment) ∧
    0 ≤ correlation cnotSourceExperiment ∧
    0 ≤ bathRelativeEntropy cnotSourceExperiment

theorem sameSourceCNOTGoal : SameSourceCNOTGoal := by
  have hphysical := thermalIdentityGoal 2 2 cnotSourceExperiment
  exact ⟨apexInstanceGoal,
    cnotInstrument,
    cnot_native_branch_weight,
    cnotInitialJoint_mass cnotSource,
    cnotProtocol_expectedCost cnotSource,
    cnotInitialEnsemble,
    hphysical.1, hphysical.2.1, hphysical.2.2⟩

/-- A binary record genuinely separates two different physical preparations,
and this same source has the all-input CNOT implementation. -/
theorem sameSourceNontrivialRecordedInstrument :
    ImplementsInstrument quantumData qubit (Fin 2) cnotSource
      quantumData_realization cnotSourceExperiment sourceCoordinateProjector ∧
    (∃ s t : quantumData.State qubit,
      s ≠ t ∧ Pure quantumData s ∧ Pure quantumData t ∧
        quantumData.weight (cnotSource.branch 0) s = 1 ∧
        quantumData.weight (cnotSource.branch 0) t = 0) :=
  ⟨cnotInstrument, cnot_nontrivial_record⟩

/-- One worked physical example preserves final recorded memory entropy and
uses the same experiment as the branch instrument and demand contract. -/
theorem sameSourceMemoryEntropyBound :
    spectralEntropy cnotSourceExperiment.initialSystem -
        spectralEntropy cnotSourceExperiment.finalSystem ≤
          cnotSourceExperiment.β * heat cnotSourceExperiment := by
  have h := thermalIdentityGoal 2 2 cnotSourceExperiment
  dsimp [entropyDrop] at h
  linarith [h.1, h.2.1, h.2.2]

end ThermalSourceCompletion
end UniversalObservation.Reconstruction
