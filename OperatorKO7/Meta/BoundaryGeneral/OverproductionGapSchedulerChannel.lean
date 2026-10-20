import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapShannon

/-!
# Exact scheduler-channel endpoints for Shannon Omega

This module constructs the two canonical evidence channels directly on the
reachable-terminal subtype.

* `schedulerEchoConditional` returns the scheduler marginal regardless of the
  channel cell.  The licensed deficit is zero, so Shannon Omega is exactly the
  scheduler entropy.
* `schedulerResolvingConditional` uses the terminal point itself as the channel
  cell and returns a Dirac target conditional.  The direct target marginal is
  the scheduler distribution, the residual licensed entropy is zero, and the
  licensed deficit equals the full scheduler entropy.  Hence Shannon Omega is
  exactly zero.

This discharges the roadmap's sharp endpoint without an alignment hypothesis.
Trust: kernel checked; no proof holes or user axioms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGapSchedulerChannel

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapShannon

noncomputable section

/-- Singleton direct-surface mass for scheduler experiments. -/
def schedulerUnitMass : Unit → ℝ := fun _ => 1

/-- Singleton echo-channel weight. -/
def schedulerEchoWeight : Unit → Unit → ℝ := fun _ _ => 1

/-- Echo evidence: every channel cell returns the scheduler marginal itself. -/
def schedulerEchoConditional
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    Unit → Unit → TerminalPoint R source → ℝ :=
  fun _ _ x => σ.mass x

/-- Echo scheduler data have direct entropy equal to scheduler entropy. -/
theorem schedulerEcho_condEntropyDirect
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    condEntropyDirect schedulerUnitMass schedulerEchoWeight
      (schedulerEchoConditional σ) = H σ.mass := by
  simp [condEntropyDirect, schedulerUnitMass, schedulerEchoWeight,
    schedulerEchoConditional]

/-- Echo scheduler data have the same licensed residual entropy. -/
theorem schedulerEcho_condEntropyLicensed
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    condEntropyLicensed schedulerUnitMass schedulerEchoWeight
      (schedulerEchoConditional σ) = H σ.mass := by
  -- `H` is applied to the partially applied conditional, so `simp` cannot reach
  -- inside it. Discharge that argument by eta first, then reduce the two
  -- singleton sums.
  have hcell : schedulerEchoConditional σ () () = σ.mass := rfl
  simp [condEntropyLicensed, schedulerUnitMass, schedulerEchoWeight, hcell]

/-- Echo evidence carries zero licensed information about the scheduler target. -/
theorem schedulerEcho_deficit_eq_zero
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    deficit schedulerUnitMass schedulerEchoWeight
      (schedulerEchoConditional σ) = 0 := by
  unfold deficit
  rw [schedulerEcho_condEntropyDirect, schedulerEcho_condEntropyLicensed]
  ring

/-- Shannon Omega under scheduler echo evidence is exactly scheduler entropy. -/
theorem schedulerEcho_shannonGap_eq_entropyBits
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    shannonOverproductionGap R source σ schedulerUnitMass schedulerEchoWeight
      (schedulerEchoConditional σ) = schedulerEntropyBits σ := by
  unfold shannonOverproductionGap deficitBits
  rw [schedulerEcho_deficit_eq_zero]
  ring

/-- Resolving-channel weights are the scheduler probabilities themselves. -/
def schedulerResolvingWeight
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    Unit → TerminalPoint R source → ℝ :=
  fun _ c => σ.mass c

open scoped Classical in
/-- Resolving target conditional: observing channel cell `c` makes the target a
Dirac mass at exactly `c`.

The carrier `T` is an arbitrary `Fintype`, so equality on the reachable-terminal
subtype need not be decidable. Classical decidability keeps the statement at full
generality; requiring `DecidableEq T` would narrow every downstream theorem. -/
def schedulerResolvingConditional
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T} :
    Unit → TerminalPoint R source → TerminalPoint R source → ℝ :=
  fun _ c x => if c = x then 1 else 0

/-- Marginalizing the resolving channel recovers the scheduler distribution. -/
theorem schedulerResolving_mixture
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) (x : TerminalPoint R source) :
    (∑ c : TerminalPoint R source,
      schedulerResolvingWeight σ () c * schedulerResolvingConditional () c x) =
      σ.mass x := by
  unfold schedulerResolvingWeight schedulerResolvingConditional
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hbx
    simp [hbx]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- Direct target entropy under the resolving channel is the scheduler entropy. -/
theorem schedulerResolving_condEntropyDirect
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    condEntropyDirect schedulerUnitMass (schedulerResolvingWeight σ)
      schedulerResolvingConditional = H σ.mass := by
  unfold condEntropyDirect schedulerUnitMass
  simp_rw [schedulerResolving_mixture σ]
  simp

/-- Every resolving-channel target conditional is a point mass and has zero
entropy. -/
theorem schedulerResolving_conditional_entropy_zero
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (c : TerminalPoint R source) :
    H (schedulerResolvingConditional () c) = 0 := by
  -- Proved directly instead of through `H_dirac_eq_zero`, whose `DecidableEq`
  -- instance is not the classical one this conditional was defined with.
  unfold H schedulerResolvingConditional
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : c = x
  · simp [h, Real.negMulLog, Real.log_one]
  · simp [h, Real.negMulLog]

/-- Licensed residual entropy under exact terminal revelation is zero. -/
theorem schedulerResolving_condEntropyLicensed_eq_zero
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    condEntropyLicensed schedulerUnitMass (schedulerResolvingWeight σ)
      schedulerResolvingConditional = 0 := by
  -- The outer sum binds `w : Unit`, so a rewrite stated at the literal `()`
  -- has nothing to match until the singleton sum is reduced first.
  simp [condEntropyLicensed, schedulerUnitMass, schedulerResolvingWeight,
    schedulerResolving_conditional_entropy_zero]

/-- The resolving licensed deficit equals the full scheduler entropy. -/
theorem schedulerResolving_deficit_eq_entropy
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    deficit schedulerUnitMass (schedulerResolvingWeight σ)
      schedulerResolvingConditional = H σ.mass := by
  unfold deficit
  rw [schedulerResolving_condEntropyDirect,
    schedulerResolving_condEntropyLicensed_eq_zero]
  ring

/-- **Exact W2 endpoint.** If the channel reveals the reached terminal normal
form itself, Shannon Omega is zero. -/
theorem schedulerResolving_shannonGap_eq_zero
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    shannonOverproductionGap R source σ schedulerUnitMass
      (schedulerResolvingWeight σ) schedulerResolvingConditional = 0 := by
  unfold shannonOverproductionGap schedulerEntropyBits HBits deficitBits
  rw [schedulerResolving_deficit_eq_entropy]
  ring

/-- The canonical endpoints differ by exactly the scheduler entropy. -/
theorem scheduler_channel_endpoint_difference
    {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
    (σ : TerminalScheduler R source) :
    shannonOverproductionGap R source σ schedulerUnitMass schedulerEchoWeight
        (schedulerEchoConditional σ) -
      shannonOverproductionGap R source σ schedulerUnitMass
        (schedulerResolvingWeight σ) schedulerResolvingConditional =
      schedulerEntropyBits σ := by
  rw [schedulerEcho_shannonGap_eq_entropyBits,
    schedulerResolving_shannonGap_eq_zero]
  ring

/-- Scheduler-channel receipt. -/
theorem scheduler_channel_law :
    (∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
      (σ : TerminalScheduler R source),
      shannonOverproductionGap R source σ schedulerUnitMass
          (schedulerResolvingWeight σ) schedulerResolvingConditional = 0) ∧
    (∀ {T : Type} [Fintype T] {R : T → T → Prop} {source : T}
      (σ : TerminalScheduler R source),
      shannonOverproductionGap R source σ schedulerUnitMass schedulerEchoWeight
        (schedulerEchoConditional σ) = schedulerEntropyBits σ) :=
  ⟨schedulerResolving_shannonGap_eq_zero,
    schedulerEcho_shannonGap_eq_entropyBits⟩

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGapSchedulerChannel
