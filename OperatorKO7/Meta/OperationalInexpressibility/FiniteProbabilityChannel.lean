import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

/-!
# Typed finite probability channels

This module packages finite probability masses and finite-output conditional
kernels with pointwise nonnegativity and total-mass-one laws. A finite channel
then carries a source prior, a target, an observation, and a normalized target
posterior model at every observation. Its residual is the prior-weighted entropy
of those modeled posterior rows in natural-log units. `FiniteChannel` does not
itself impose a Bayes-consistency equation deriving the posterior from the
prior, target, and observation; clients that need that stronger reading must
prove it separately.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.FiniteProbabilityChannel

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite

universe uSource uObservation uTarget uInput uOutput

/-- A probability distribution on a finite carrier. -/
structure FiniteDistribution (X : Type uSource) [Fintype X] where
  mass : X -> Real
  nonnegative : forall x : X, 0 <= mass x
  total : (Finset.univ.sum mass) = 1

namespace FiniteDistribution

/-- Universe-polymorphic point mass used by the typed channel layer. The older
`ShannonFinite.pointMass` is intentionally universe-zero. -/
def pointMassU {X : Type uSource} [DecidableEq X] (selected : X) : X -> Real :=
  fun x => if x = selected then 1 else 0

/-- The two distribution laws as a named proposition. -/
theorem normalized {X : Type uSource} [Fintype X]
    (distribution : FiniteDistribution X) :
    (forall x : X, 0 <= distribution.mass x)
      ∧ (Finset.univ.sum distribution.mass) = 1 :=
  ⟨distribution.nonnegative, distribution.total⟩

/-- A point distribution at a selected finite outcome. -/
def point {X : Type uSource} [Fintype X] [DecidableEq X]
    (selected : X) : FiniteDistribution X where
  mass := pointMassU selected
  nonnegative := by
    intro x
    by_cases h : x = selected <;> simp [pointMassU, h]
  total := by
    classical
    simp [pointMassU]

end FiniteDistribution

/-- A finite-output conditional probability kernel. The input need not itself
be finite; normalization is required separately at every input. -/
structure ConditionalKernel (Input : Type uInput) (Output : Type uOutput)
    [Fintype Output] where
  mass : Input -> Output -> Real
  nonnegative : forall input : Input, forall output : Output,
    0 <= mass input output
  total : forall input : Input, (Finset.univ.sum (mass input)) = 1

namespace ConditionalKernel

/-- Each row of a conditional kernel is a finite distribution. -/
def row {Input : Type uInput} {Output : Type uOutput} [Fintype Output]
    (kernel : ConditionalKernel Input Output) (input : Input) :
    FiniteDistribution Output where
  mass := kernel.mass input
  nonnegative := kernel.nonnegative input
  total := kernel.total input

/-- A deterministic conditional kernel, represented by point distributions. -/
def deterministic {Input : Type uInput} {Output : Type uOutput}
    [Fintype Output] [DecidableEq Output]
    (decode : Input -> Output) : ConditionalKernel Input Output where
  mass := fun input => FiniteDistribution.pointMassU (decode input)
  nonnegative := by
    intro input output
    by_cases h : output = decode input <;>
      simp [FiniteDistribution.pointMassU, h]
  total := by
    intro input
    classical
    simp [FiniteDistribution.pointMassU]

/-- Every deterministic row assigns mass one to its selected output. -/
theorem deterministic_selected_mass
    {Input : Type uInput} {Output : Type uOutput}
    [Fintype Output] [DecidableEq Output]
    (decode : Input -> Output) (input : Input) :
    (deterministic decode).mass input (decode input) = 1 := by
  simp [deterministic, FiniteDistribution.pointMassU]

end ConditionalKernel

/-- The fair binary mass function. -/
def fairBinaryMass : Bool -> Real :=
  fun _ => (1 : Real) / 2

/-- The fair binary mass is a normalized distribution. -/
def fairBinaryDistribution : FiniteDistribution Bool where
  mass := fairBinaryMass
  nonnegative := by
    intro outcome
    norm_num [fairBinaryMass]
  total := by
    rw [Fintype.sum_bool]
    norm_num [fairBinaryMass]

/-- A fair binary conditional kernel at every input. -/
def ConditionalKernel.fairBinary (Input : Type uInput) :
    ConditionalKernel Input Bool where
  mass := fun _ => fairBinaryMass
  nonnegative := by
    intro input outcome
    norm_num [fairBinaryMass]
  total := by
    intro input
    rw [Fintype.sum_bool]
    norm_num [fairBinaryMass]

/-- The fair binary entropy is exactly `log 2` in natural-log units. -/
theorem fairBinaryMass_entropy :
    H fairBinaryMass = Real.log 2 := by
  unfold H fairBinaryMass
  rw [Fintype.sum_bool]
  simp [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- A typed finite probability channel. The observation type may be rich or
infinite; the source prior and target alphabet are finite, and every posterior
row is normalized. The posterior is supplied model data. This structure alone
does not assert that it is the Bayes conditional induced by the other fields. -/
structure FiniteChannel
    (Source : Type) (Observation : Type uObservation)
    (Target : Type) [Fintype Source] [Fintype Target] where
  prior : FiniteDistribution Source
  target : Source -> Target
  observe : Source -> Observation
  posterior : ConditionalKernel Observation Target

namespace FiniteChannel

/-- Expected target entropy after conditioning on the channel observation. -/
noncomputable def residual
    {Source : Type} {Observation : Type uObservation}
    {Target : Type} [Fintype Source] [Fintype Target]
    (channel : FiniteChannel Source Observation Target) : Real :=
  Finset.univ.sum (fun source : Source => channel.prior.mass source *
    H (channel.posterior.mass (channel.observe source)))

/-- Named normalization receipt for both the source prior and every posterior
row of a finite channel. -/
theorem normalized
    {Source : Type} {Observation : Type uObservation}
    {Target : Type} [Fintype Source] [Fintype Target]
    (channel : FiniteChannel Source Observation Target) :
    (Finset.univ.sum channel.prior.mass = 1)
      ∧ (forall observation : Observation,
          Finset.univ.sum (channel.posterior.mass observation) = 1) :=
  ⟨channel.prior.total, channel.posterior.total⟩

end FiniteChannel

/-- The fair binary distribution is genuinely two-sided. -/
theorem fairBinaryDistribution_nonvacuous :
    0 < fairBinaryDistribution.mass false
      ∧ 0 < fairBinaryDistribution.mass true
      ∧ false ≠ true := by
  norm_num [fairBinaryDistribution, fairBinaryMass]

end OperatorKO7.Meta.OperationalInexpressibility.FiniteProbabilityChannel
