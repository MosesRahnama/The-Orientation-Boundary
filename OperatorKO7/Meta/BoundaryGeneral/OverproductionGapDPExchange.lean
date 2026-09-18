import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapConceptBridge
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
import OperatorKO7.Meta.BoundaryGeneral.OmegaPreservingTransport
import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

/-!
# The one-bit exchange between the distinction refusal and the DP license

The duplicated generator pair of the recursor is value-diagonal and
role-distinct.  Audited on the value coordinate, any channel is an echo: it is
constant across the two roles, supplies zero licensed gain, and leaves the full
one-bit boundary event standing.  Audited on the role coordinate, the resolving
channel keyed by frame/active supplies exactly one bit and closes the gap.

The exchange equation `one_bit_dp_exchange` states the transaction in Omega
vocabulary: the bit refused on the value diagonal equals the bit the role
channel supplies.  It is the quantitative face of
`GateTheorem.refused_bit_eq_spent_bit_ko7`, with the two-role alphabet here
being the live `actualDPChannel` alphabet, pinned by the exogenous separator.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

instance instFintypeRole : Fintype Role :=
  ⟨{Role.frame, Role.active}, fun r => by cases r <;> simp⟩

end OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

namespace OperatorKO7.Meta.BoundaryGeneral.OverproductionGap

open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel

noncomputable section

/-- The two-point role alphabet as a Boolean carrier. -/
def boolRoleEquiv : Bool ≃ Role where
  toFun b := match b with
    | false => Role.frame
    | true => Role.active
  invFun r := match r with
    | Role.frame => false
    | Role.active => true
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro r; cases r <;> rfl

/-- The binary channel alphabet relabeled as the frame/active role alphabet. -/
def roleEquiv : Fin 2 ≃ Role := finTwoEquiv.trans boolRoleEquiv

/-- Uniform channel weights on the role alphabet. -/
def roleWeights : Fin 1 → Role → ℝ :=
  relabelNu (Equiv.refl (Fin 1)) roleEquiv uniformChannelWeights

/-- **The role channel.** The resolving binary channel keyed by the frame/active
role coordinate: each role determines the target exactly. -/
def roleResolving : Fin 1 → Role → Fin 2 → ℝ :=
  relabelConditional (Equiv.refl (Fin 1)) roleEquiv (Equiv.refl (Fin 2))
    resolvingChannel

/-- **The value-blind channel.** Constant across the two roles, because both
roles carry the same value; the answer is an echo of the direct surface. -/
def roleEcho : Fin 1 → Role → Fin 2 → ℝ := fun _ _ _ => (1 : ℝ) / 2

/-- Role weights are normalized. -/
theorem roleWeights_sum_one : ∀ w, ∑ c, roleWeights w c = 1 := by
  intro w
  show ∑ c : Role, uniformChannelWeights w (roleEquiv.symm c) = 1
  rw [Equiv.sum_comp roleEquiv.symm (fun c : Fin 2 => uniformChannelWeights w c)]
  exact uniformChannelWeights_sum_one w

/-- A value-blind channel leaves the whole one-bit gap standing. -/
theorem valueBlind_gap_one (r : Fin 1 → Role → Fin 2 → ℝ)
    (v : Fin 1 → Fin 2 → ℝ) (hconst : ∀ w c, r w c = v w) :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights r = 1 := by
  rw [overproductionGap_eq_hartley_of_zero_deficit Fork3Step Fork3.source
    unitSurface roleWeights r
    (circular_reference_zero_deficit unitSurface roleWeights r
      roleWeights_sum_one v hconst)]
  exact fork3_raw_terminalHartleyEntropy_eq_one

/-- A value-blind channel leaves the boundary event standing. -/
theorem valueBlind_boundary_event (r : Fin 1 → Role → Fin 2 → ℝ)
    (v : Fin 1 → Fin 2 → ℝ) (hconst : ∀ w c, r w c = v w) :
    BoundaryEvent Fork3Step Fork3.source unitSurface roleWeights r := by
  unfold BoundaryEvent
  rw [valueBlind_gap_one r v hconst]
  norm_num

/-- The role channel supplies exactly one bit of licensed gain. -/
theorem roleResolving_deficitBits_one :
    deficitBits unitSurface roleWeights roleResolving = 1 := by
  have h := deficitBits_relabel (Equiv.refl (Fin 1)) roleEquiv
    (Equiv.refl (Fin 2)) unitSurface uniformChannelWeights resolvingChannel
  rw [resolvingChannel_deficitBits_eq_one] at h
  exact h

/-- The role channel closes the gap. -/
theorem roleResolving_gap_zero :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights
      roleResolving = 0 := by
  have h := overproductionGap_full_relabel
    (OperatorKO7.Meta.BoundaryGeneral.OmegaPreservingTransport.relIsoRefl
      Fork3Step)
    Fork3.source (Equiv.refl (Fin 1)) roleEquiv (Equiv.refl (Fin 2))
    unitSurface uniformChannelWeights resolvingChannel
  rw [fork3_raw_gap_closed_by_resolving_channel] at h
  exact h

/-- The role channel refuses the boundary event. -/
theorem roleResolving_not_boundary_event :
    ¬ BoundaryEvent Fork3Step Fork3.source unitSurface roleWeights
      roleResolving := by
  unfold BoundaryEvent
  rw [roleResolving_gap_zero]
  exact lt_irrefl 0

/-- **The one-bit exchange.** The gap a value-blind audit leaves standing
exceeds the gap the role audit leaves by exactly the one bit the role channel
supplies. The refused value bit is the spent role bit. -/
theorem one_bit_dp_exchange :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights roleEcho -
      overproductionGap Fork3Step Fork3.source unitSurface roleWeights
        roleResolving = 1 := by
  rw [valueBlind_gap_one roleEcho (fun _ _ => (1 : ℝ) / 2) (fun _ _ => rfl),
    roleResolving_gap_zero]
  norm_num

/-- **The DP exchange law.** On the canonical fork audited over the frame/active
role alphabet: every value-blind channel is an echo that leaves the one-bit
boundary event standing; the role-resolving channel supplies exactly one bit,
closes the gap, and refuses the event; the exchange is exactly one bit; and the
live KO7 dependency-pair channel genuinely separates the two roles, so the role
coordinate is an exogenous channel and never a relabeled value. -/
theorem omega_dp_exchange_law :
    (∀ (r : Fin 1 → Role → Fin 2 → ℝ) (v : Fin 1 → Fin 2 → ℝ),
      (∀ w c, r w c = v w) →
      overproductionGap Fork3Step Fork3.source unitSurface roleWeights r = 1 ∧
      BoundaryEvent Fork3Step Fork3.source unitSurface roleWeights r) ∧
    deficitBits unitSurface roleWeights roleResolving = 1 ∧
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights
      roleResolving = 0 ∧
    ¬ BoundaryEvent Fork3Step Fork3.source unitSurface roleWeights
      roleResolving ∧
    (overproductionGap Fork3Step Fork3.source unitSurface roleWeights roleEcho -
      overproductionGap Fork3Step Fork3.source unitSurface roleWeights
        roleResolving = 1) ∧
    (∀ b s n : OperatorKO7.Trace,
      actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
        actualDPChannel b s n (((), Role.active) : Occ Unit)) :=
  ⟨fun r v hconst =>
      ⟨valueBlind_gap_one r v hconst, valueBlind_boundary_event r v hconst⟩,
    roleResolving_deficitBits_one,
    roleResolving_gap_zero,
    roleResolving_not_boundary_event,
    one_bit_dp_exchange,
    fun b s n => actual_dp_license_is_exogenous_separator b s n⟩

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
