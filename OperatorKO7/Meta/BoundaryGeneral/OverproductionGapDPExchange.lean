import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapConceptBridge
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRelabel
import OperatorKO7.Meta.BoundaryGeneral.OmegaPreservingTransport
import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

/-!
# One-bit result for the dependency-pair role channel

The duplicated generator pair has the same value and distinct roles. Any channel constant across those roles has zero licensed gain, an Omega gap of one bit, and a boundary event. The resolving channel keyed by frame and active supplies one bit and gives an Omega gap of zero.

`one_bit_dp_exchange` states that the value-blind gap minus the role-resolving gap is one bit. `GateTheorem.refused_bit_eq_spent_bit_ko7` states the corresponding equality for the dependency-pair channel. `actualDPChannel` distinguishes the frame and active roles through its exogenous separator.

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

/-- The resolving binary channel keyed by the frame and active roles; each role determines the target. -/
def roleResolving : Fin 1 → Role → Fin 2 → ℝ :=
  relabelConditional (Equiv.refl (Fin 1)) roleEquiv (Equiv.refl (Fin 2))
    resolvingChannel

/-- The channel returns the same uniform answer distribution for both roles, whose values agree. -/
def roleEcho : Fin 1 → Role → Fin 2 → ℝ := fun _ _ _ => (1 : ℝ) / 2

/-- Role weights are normalized. -/
theorem roleWeights_sum_one : ∀ w, ∑ c, roleWeights w c = 1 := by
  intro w
  show ∑ c : Role, uniformChannelWeights w (roleEquiv.symm c) = 1
  rw [Equiv.sum_comp roleEquiv.symm (fun c : Fin 2 => uniformChannelWeights w c)]
  exact uniformChannelWeights_sum_one w

/-- A channel constant across roles has an Omega gap of one bit. -/
theorem valueBlind_gap_one (r : Fin 1 → Role → Fin 2 → ℝ)
    (v : Fin 1 → Fin 2 → ℝ) (hconst : ∀ w c, r w c = v w) :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights r = 1 := by
  rw [overproductionGap_eq_hartley_of_zero_deficit Fork3Step Fork3.source
    unitSurface roleWeights r
    (circular_reference_zero_deficit unitSurface roleWeights r
      roleWeights_sum_one v hconst)]
  exact fork3_raw_terminalHartleyEntropy_eq_one

/-- A channel constant across roles satisfies the boundary-event predicate. -/
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

/-- The role-resolving channel gives an Omega gap of zero. -/
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

/-- The role-resolving channel does not satisfy the boundary-event predicate. -/
theorem roleResolving_not_boundary_event :
    ¬ BoundaryEvent Fork3Step Fork3.source unitSurface roleWeights
      roleResolving := by
  unfold BoundaryEvent
  rw [roleResolving_gap_zero]
  exact lt_irrefl 0

/-- The value-blind channel has gap one and the role-resolving channel has gap zero, so their gap difference is one bit. -/
theorem one_bit_dp_exchange :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights roleEcho -
      overproductionGap Fork3Step Fork3.source unitSurface roleWeights
        roleResolving = 1 := by
  rw [valueBlind_gap_one roleEcho (fun _ _ => (1 : ℝ) / 2) (fun _ _ => rfl),
    roleResolving_gap_zero]
  norm_num

/-- For Fork3, channels constant across roles have gap one and a boundary event. The role-resolving channel supplies one licensed bit, has gap zero, and has no boundary event. The gaps differ by one, and `actualDPChannel` distinguishes frame from active for every recursor state. -/
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
