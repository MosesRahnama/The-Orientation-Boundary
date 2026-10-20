import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
import OperatorKO7.Meta.DistinctionBoundary.GateTheorem

/-!
# The one-bit exchange on the live KO7 cone, with the actual DP channel

`OverproductionGapDPExchange` proves the exchange on the canonical fork with a
constructed resolving channel over the role alphabet. This module closes the
three links between that theorem and the Gate:

* the actual dependency-pair channel `actualDPChannel`, read as an evidence
  kernel, is that resolving channel (`dpEvidence_eq_roleResolving`), so the
  live channel itself supplies the bit and closes the gap;
* a channel that factors through the value coordinate is role-constant on the
  duplicated generator pair (`valueFactored_pair_is_roleConstant`), so
  "value-blind" is a theorem about the occurrence carrier, not a naming choice;
* the exchange transports along `fork3LocalRawIso` to the KO7 local cone at
  `eqW void void` (`ko7_gap_of_fork3`), where the Gate's refused bit lives, and
  the two bits are equated (`ko7_exchange_bit_eq_gate_refused_bit`).

The capstone `omega_dp_exchange_ko7_law` conjoins the exchange with
`GateTheorem.refused_bit_eq_spent_bit_ko7` on one carrier and one source.
Arts and Giesl soundness remains the separate consuming theorem.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

open OperatorKO7
open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone
open OperatorKO7.Meta.DistinctionBoundary.GateTheorem
open OperatorKO7.Meta.SafeStep.BranchEntropyGeneral
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport

noncomputable section

/-! ## The actual channel's two answers -/

/-- The frame occurrence is never selected. -/
theorem actualDPChannel_frame_eq_false (b s n : Trace) :
    actualDPChannel b s n (((), Role.frame) : Occ Unit) = false := by
  have h := actualDPChannel_decodes_isActive b s n (((), Role.frame) : Occ Unit)
  simpa [decodeActive, isActive] using h

/-- The active occurrence is always selected. -/
theorem actualDPChannel_active_eq_true (b s n : Trace) :
    actualDPChannel b s n (((), Role.active) : Occ Unit) = true := by
  have h := actualDPChannel_decodes_isActive b s n (((), Role.active) : Occ Unit)
  simpa [decodeActive, isActive] using h

/-! ## The actual channel as an evidence kernel -/

/-- The target cell a Boolean answer selects. -/
def dpTarget : Bool → Fin 2
  | false => 0
  | true => 1

/-- **The live dependency-pair channel as evidence.** Each role answers through
`actualDPChannel`, and the answer determines the target cell. -/
def dpEvidence (b s n : Trace) : Fin 1 → Role → Fin 2 → ℝ :=
  fun _ c => pointMass (dpTarget (actualDPChannel b s n (((), c) : Occ Unit)))

theorem roleEquiv_symm_frame : roleEquiv.symm Role.frame = 0 := by decide

theorem roleEquiv_symm_active : roleEquiv.symm Role.active = 1 := by decide

/-- The live channel, read as evidence, is the resolving channel keyed by role. -/
theorem dpEvidence_eq_roleResolving (b s n : Trace) :
    dpEvidence b s n = roleResolving := by
  funext w c x
  cases c with
  | frame =>
      simp only [dpEvidence, roleResolving, relabelConditional, resolvingChannel,
        Equiv.refl_symm, Equiv.refl_apply, actualDPChannel_frame_eq_false, dpTarget,
        roleEquiv_symm_frame]
  | active =>
      simp only [dpEvidence, roleResolving, relabelConditional, resolvingChannel,
        Equiv.refl_symm, Equiv.refl_apply, actualDPChannel_active_eq_true, dpTarget,
        roleEquiv_symm_active]

/-- The live channel supplies one bit of licensed gain. -/
theorem dpEvidence_deficitBits_one (b s n : Trace) :
    deficitBits unitSurface roleWeights (dpEvidence b s n) = 1 := by
  rw [dpEvidence_eq_roleResolving]
  exact roleResolving_deficitBits_one

/-- The live channel closes the gap on the canonical fork. -/
theorem dpEvidence_gap_zero (b s n : Trace) :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights
      (dpEvidence b s n) = 0 := by
  rw [dpEvidence_eq_roleResolving]
  exact roleResolving_gap_zero

/-! ## Value-factored channels on the duplicated generator pair -/

/-- A channel on the occurrence carrier, read at the two occurrences of the
duplicated generator `s`. -/
def pairConditional (s : Trace) (R : Fin 1 → Occ Trace → Fin 2 → ℝ) :
    Fin 1 → Role → Fin 2 → ℝ :=
  fun w ρ => R w (s, ρ)

/-- **Value-blindness is role-constancy.** A channel that factors through the
value coordinate answers identically on the frame and active occurrences of
the duplicated generator, because both carry the value `s`. -/
theorem valueFactored_pair_is_roleConstant (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    ∀ w c, pairConditional s R w c = g w s := by
  intro w c
  unfold pairConditional
  rw [hfac]

/-- A value-factored channel leaves the full one-bit gap on the canonical fork. -/
theorem valueFactored_pair_gap_one (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights
      (pairConditional s R) = 1 :=
  valueBlind_gap_one (pairConditional s R) (fun w => g w s)
    (valueFactored_pair_is_roleConstant s R g hfac)

/-! ## Transport to the live KO7 cone -/

/-- The cone isomorphism sends the fork source to the `eqW void void` source. -/
theorem fork3LocalRawIso_source :
    fork3LocalRawIso.toEquiv Fork3.source = EqWBreakerNode.source := rfl

/-- The gap at the live KO7 source equals the gap at the canonical fork source,
for every evidence channel. -/
theorem ko7_gap_of_fork3 {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap LocalRaw EqWBreakerNode.source μ ν r =
      overproductionGap Fork3Step Fork3.source μ ν r := by
  have h := relIso_overproductionGap_eq fork3LocalRawIso Fork3.source μ ν r
  rw [fork3LocalRawIso_source] at h
  exact h.symm

/-- On the live cone, a value-factored channel leaves the one-bit gap. -/
theorem ko7_valueFactored_pair_gap_one (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (pairConditional s R) = 1 := by
  rw [ko7_gap_of_fork3]
  exact valueFactored_pair_gap_one s R g hfac

/-- On the live cone, a value-factored channel leaves the boundary event. -/
theorem ko7_valueFactored_pair_boundary_event (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (pairConditional s R) := by
  unfold BoundaryEvent
  rw [ko7_valueFactored_pair_gap_one s R g hfac]
  norm_num

/-- On the live cone, the live channel closes the gap. -/
theorem ko7_dpEvidence_gap_zero (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (dpEvidence b s n) = 0 := by
  rw [ko7_gap_of_fork3]
  exact dpEvidence_gap_zero b s n

/-- On the live cone, the live channel refuses the boundary event. -/
theorem ko7_dpEvidence_not_boundary_event (b s n : Trace) :
    ¬ BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (dpEvidence b s n) := by
  unfold BoundaryEvent
  rw [ko7_dpEvidence_gap_zero]
  exact lt_irrefl 0

/-- The exchange on the live cone: the echo audit exceeds the live-channel audit
by one bit. -/
theorem ko7_one_bit_dp_exchange (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        roleEcho -
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        (dpEvidence b s n) = 1 := by
  rw [ko7_gap_of_fork3, ko7_gap_of_fork3, dpEvidence_eq_roleResolving]
  exact one_bit_dp_exchange

/-- **The refused bit is the spent bit.** The gap the echo audit leaves above the
live-channel audit equals the Gate's raw-to-licensed branch-entropy collapse on
the same cone and the same source. -/
theorem ko7_exchange_bit_eq_gate_refused_bit (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        roleEcho -
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        (dpEvidence b s n) =
    branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) -
      branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source) := by
  rw [ko7_one_bit_dp_exchange, refused_bit_eq_spent_bit_ko7.1, branchEntropy_two]

/-! ## Capstone -/

/-- **The DP exchange law on the live cone.** At `eqW void void`: every channel
factoring through the value coordinate leaves the one-bit gap and the boundary
event on the duplicated generator pair; the live dependency-pair channel, read
as evidence, supplies one bit, closes the gap, and refuses the event; the
exchanged bit equals the Gate's refused bit; the live channel separates the two
roles; and the Gate's own accounting identity is carried alongside. -/
theorem omega_dp_exchange_ko7_law :
    (∀ (s : Trace) (R : Fin 1 → Occ Trace → Fin 2 → ℝ)
        (g : Fin 1 → Trace → Fin 2 → ℝ),
      (∀ w o, R w o = g w o.1) →
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
          (pairConditional s R) = 1 ∧
      BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
        (pairConditional s R)) ∧
    (∀ b s n : Trace,
      deficitBits unitSurface roleWeights (dpEvidence b s n) = 1 ∧
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
          (dpEvidence b s n) = 0 ∧
      ¬ BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
          (dpEvidence b s n)) ∧
    (∀ b s n : Trace,
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
          roleEcho -
        overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
          (dpEvidence b s n) =
      branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) -
        branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source)) ∧
    (∀ b s n : Trace,
      actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
        actualDPChannel b s n (((), Role.active) : Occ Unit)) ∧
    ((branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) -
        branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source) =
      branchEntropy 2) ∧
      structuralHartleyCollapse LocalRaw LocalLicensed EqWBreakerNode.source = 1) :=
  ⟨fun s R g hfac =>
      ⟨ko7_valueFactored_pair_gap_one s R g hfac,
        ko7_valueFactored_pair_boundary_event s R g hfac⟩,
    fun b s n =>
      ⟨dpEvidence_deficitBits_one b s n, ko7_dpEvidence_gap_zero b s n,
        ko7_dpEvidence_not_boundary_event b s n⟩,
    fun b s n => ko7_exchange_bit_eq_gate_refused_bit b s n,
    fun b s n => actual_dp_license_is_exogenous_separator b s n,
    refused_bit_eq_spent_bit_ko7⟩

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
