import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics

/-!
# S4.3: guarded physical entropy and energy limits


These results use the actual finite geometric density matrices and their physical
energy observables. The two uniform-tail hypotheses are independent. Normalized
positive density matrices converging in trace norm do not, without these
licenses, guarantee convergence of von Neumann entropy.

No identity between an arbitrary GNS functional and this physical density
family is asserted. The primary alone performs Lean and axiom validation.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped BigOperators ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitThermodynamics
open OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction.Thermal

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionEntropyTail

/-- The two distinct licenses needed for entropy and energy of a single
family of finite states. A pointwise convergence hypothesis is separate. -/
def JointUniformTailLicense (p : ℕ → ℕ → ℝ)
    (E : ℕ → ℕ → ℝ) : Prop :=
  UniformTailControl (fun n k => Real.negMulLog (p n k)) ∧
  UniformTailControl (fun n k => E n k * p n k)

/-- Separate uniform entropy and energy tails give both infinite-sum limits
for the SAME finite probabilities p and the SAME finite energy observables E.
All pointwise and summability assumptions appear in the theorem type. -/
theorem jointEntropyEnergyLimit
    (p : ℕ → ℕ → ℝ) (pinf : ℕ → ℝ)
    (E : ℕ → ℕ → ℝ) (Einf : ℕ → ℝ)
    (hp : ∀ n, Summable (fun k => Real.negMulLog (p n k)))
    (hpinf : Summable (fun k => Real.negMulLog (pinf k)))
    (hEp : ∀ n, Summable (fun k => E n k * p n k))
    (hEinf : Summable (fun k => Einf k * pinf k))
    (hpt : ∀ k, Tendsto (fun n => p n k) atTop (nhds (pinf k)))
    (hEt : ∀ k, Tendsto (fun n => E n k) atTop (nhds (Einf k)))
    (htails : JointUniformTailLicense p E) :
    Tendsto (fun n => ∑' k, Real.negMulLog (p n k))
      atTop (nhds (∑' k, Real.negMulLog (pinf k))) ∧
    Tendsto (fun n => ∑' k, E n k * p n k)
      atTop (nhds (∑' k, Einf k * pinf k)) :=
  ⟨entropy_tendsto_of_uniformTailControl
     p pinf hp hpinf hpt htails.1,
   energy_tendsto_of_uniformTailControl
     p pinf E Einf hEp hEinf hpt hEt htails.2⟩

/-- For a given q and reservoir r, the geometric family has both tail
licenses. Finite densities and their actual energy levels are retained. -/
theorem geometricJointUniformTailLicense
    {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    JointUniformTailLicense (fun n k => paddedGeometric q n k)
      (fun n k => padFunction (geometricEnergy r n) k) :=
  ⟨geometric_entropy_uniformTailControl hq0 hq1,
   geometric_energy_uniformTailControl hq0.le hq1 hr0 hr1⟩

/-- The finite geometric preparations are genuine full-rank normalized
density matrices; this is not an arbitrary sequence of abstract states. -/
theorem geometricFiniteDensity
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (geometricDensity q n).PosDef ∧ (geometricDensity q n).trace = 1 :=
  ⟨geometricDensity_posDef hq0 hq1 n, geometricDensity_trace q n⟩

/-- Physical entropy, mean energy and heat converge with their declared
uniform finite-stage controls for one geometric family. The heat limit
also needs the reservoir's separate r-state limit. -/
def GeometricPhysicalTailGoal (q r : ℝ) : Prop :=
    UniformFiniteEntropyTailControl q ∧
    UniformFiniteEnergyTailControl q r ∧
    Tendsto (fun n => entropy (geometricDensity q n))
      atTop (nhds (infiniteEntropy q)) ∧
    Tendsto (fun n => meanEnergy (geometricHamiltonian r n) (geometricDensity q n))
      atTop (nhds (infiniteMeanEnergy q r)) ∧
    Tendsto (fun n => geometricHeat q r n)
      atTop (nhds (infiniteHeat q r))

theorem geometricPhysicalTailGoal
    {q r : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    GeometricPhysicalTailGoal q r :=
  ⟨geometric_uniform_entropy_tails hq0 hq1,
   geometric_uniform_energy_tails hq0.le hq1 hr0 hr1,
   geometricEntropy_limit_by_license hq0 hq1,
   geometricMeanEnergy_limit_by_license hq0.le hq1 hr0 hr1,
   geometricHeat_limit_by_license hq0.le hq1 hr0 hr1⟩

/-- Concrete selected cutoff controls include source reports and physical
heat, rather than replacing either one by a generic limit parameter. -/
def SelectedThermodynamicRecoveryGoal : Prop :=
    UniformFiniteEntropyTailControl (1 / 2) ∧
    UniformFiniteEnergyTailControl (1 / 2) (1 / 4) ∧
    UniformFiniteEnergyTailControl (1 / 4) (1 / 4) ∧
    Tendsto (paddedGeometric (1 / 2)) atTop (nhds selectedState) ∧
    Tendsto (fun n => entropy (selectedDensity n)) atTop
      (nhds (2 * Real.log 2)) ∧
    Tendsto selectedHeat atTop (nhds ((2 / 3) * Real.log 4)) ∧
    LimitReportsGoal selectedReports selectedLimitReports

theorem selectedThermodynamicRecoveryGoal :
    SelectedThermodynamicRecoveryGoal :=
  selected_controlled_thermodynamic_limits

/-- The logarithmic family consists of genuine normalized positive finite
density matrices and converges in diagonal trace norm to a pure state. Its
entropy instead converges to one while the limiting pure state has zero
entropy, so the uniform entropy-tail license fails. -/
def LogarithmicEntropyNegativeControl : Prop :=
    (∀ n, (controlledLogarithmicDensity n).PosSemidef ∧
      (controlledLogarithmicDensity n).trace = 1) ∧
    Tendsto (fun n => ‖controlledLogarithmicState n - pureState‖)
      atTop (nhds 0) ∧
    Tendsto controlledLogarithmicState atTop (nhds pureState) ∧
    Tendsto (fun n => entropy (controlledLogarithmicDensity n))
      atTop (nhds 1) ∧
    (∑' k, Real.negMulLog (pureState k)) = 0 ∧
    ¬ Tendsto (fun n => entropy (controlledLogarithmicDensity n))
      atTop (nhds (∑' k, Real.negMulLog (pureState k))) ∧
    ¬ UniformTailControl
      (fun n k => Real.negMulLog (controlledLogarithmicState n k))

theorem logarithmicEntropyNegativeControl :
    LogarithmicEntropyNegativeControl :=
  ⟨controlledLogarithmicDensity_density,
   controlledLogarithmicState_norm_tendsto,
   controlledLogarithmicState_tendsto,
   controlledLogarithmicDensity_entropy_tendsto,
   pureState_entropy,
   controlledLogarithmic_entropy_not_tendsto_pure,
   controlledLogarithmic_not_uniformTailControl⟩

/-- The positive and negative controls are presented together without
identifying the arbitrary compatible GNS state with this geometric source. -/
def GuardedTailAndCountercontrolGoal : Prop :=
    (∀ q r : ℝ, 0 < q → q < 1 → 0 < r → r < 1 →
      GeometricPhysicalTailGoal q r) ∧
    SelectedThermodynamicRecoveryGoal ∧
    LogarithmicEntropyNegativeControl

theorem guardedTailAndCountercontrolGoal :
    GuardedTailAndCountercontrolGoal :=
  ⟨fun _ _ hq0 hq1 hr0 hr1 =>
    geometricPhysicalTailGoal hq0 hq1 hr0 hr1,
   selectedThermodynamicRecoveryGoal,
   logarithmicEntropyNegativeControl⟩

end OperatorKO7.Meta.BoundaryObserver.ReconstructionEntropyTail
