import OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapDPExchange
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapTransport
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.KO7LocalConeBridge
import OperatorKO7.Meta.DistinctionBoundary.GateTheorem

/-!
# Dependency-pair channel and entropy results

The duplicated generator pair has one value and two distinct roles. A channel constant across those roles has zero licensed gain, an Omega gap of one bit, and a boundary event. The dependency-pair channel distinguishes the roles, supplies one bit of licensed information, and gives an Omega gap of zero.

`dpEvidence_eq_roleResolving` identifies the dependency-pair channel with the role-resolving channel. `ko7_exchange_bit_eq_gate_refused_bit` equates the Omega gap difference with the branch-entropy difference from `LocalRaw` to `LocalLicensed`. `GateTheorem.refused_bit_eq_spent_bit_ko7` states the Gate's accounting identity. The Arts and Giesl soundness result is stated by a separate theorem.

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

/-- The dependency-pair channel determines the target cell from the frame or active role using `actualDPChannel`. -/
def dpEvidence (b s n : Trace) : Fin 1 → Role → Fin 2 → ℝ :=
  fun _ c => pointMass (dpTarget (actualDPChannel b s n (((), c) : Occ Unit)))

theorem roleEquiv_symm_frame : roleEquiv.symm Role.frame = 0 := by decide

theorem roleEquiv_symm_active : roleEquiv.symm Role.active = 1 := by decide

/-- The evidence distribution defined by `dpEvidence` equals the role-resolving channel. -/
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

/-- The dependency-pair channel supplies one bit of licensed gain. -/
theorem dpEvidence_deficitBits_one (b s n : Trace) :
    deficitBits unitSurface roleWeights (dpEvidence b s n) = 1 := by
  rw [dpEvidence_eq_roleResolving]
  exact roleResolving_deficitBits_one

/-- On Fork3, the dependency-pair channel gives an Omega gap of zero. -/
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

/-- A channel that factors through the value coordinate gives Fork3 an Omega gap of one bit. -/
theorem valueFactored_pair_gap_one (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    overproductionGap Fork3Step Fork3.source unitSurface roleWeights
      (pairConditional s R) = 1 :=
  valueBlind_gap_one (pairConditional s R) (fun w => g w s)
    (valueFactored_pair_is_roleConstant s R g hfac)

/-! ## Transport to the KO7 local relation -/

/-- The cone isomorphism sends the fork source to the `eqW void void` source. -/
theorem fork3LocalRawIso_source :
    fork3LocalRawIso.toEquiv Fork3.source = EqWBreakerNode.source := rfl

/-- The gap at the KO7 local source equals the gap at the Fork3 source for every evidence channel. -/
theorem ko7_gap_of_fork3 {X W Cn : Type} [Fintype X] [Fintype W] [Fintype Cn]
    (μ : W → ℝ) (ν : W → Cn → ℝ) (r : W → Cn → X → ℝ) :
    overproductionGap LocalRaw EqWBreakerNode.source μ ν r =
      overproductionGap Fork3Step Fork3.source μ ν r := by
  have h := relIso_overproductionGap_eq fork3LocalRawIso Fork3.source μ ν r
  rw [fork3LocalRawIso_source] at h
  exact h.symm

/-- On the KO7 local relation, a value-factored channel has an Omega gap of one bit. -/
theorem ko7_valueFactored_pair_gap_one (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (pairConditional s R) = 1 := by
  rw [ko7_gap_of_fork3]
  exact valueFactored_pair_gap_one s R g hfac

/-- On the KO7 local relation, a value-factored channel satisfies the boundary-event predicate. -/
theorem ko7_valueFactored_pair_boundary_event (s : Trace)
    (R : Fin 1 → Occ Trace → Fin 2 → ℝ) (g : Fin 1 → Trace → Fin 2 → ℝ)
    (hfac : ∀ w o, R w o = g w o.1) :
    BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (pairConditional s R) := by
  unfold BoundaryEvent
  rw [ko7_valueFactored_pair_gap_one s R g hfac]
  norm_num

/-- The dependency-pair channel gives zero gap on the KO7 local relation. -/
theorem ko7_dpEvidence_gap_zero (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (dpEvidence b s n) = 0 := by
  rw [ko7_gap_of_fork3]
  exact dpEvidence_gap_zero b s n

/-- The dependency-pair channel does not satisfy the boundary-event predicate on the KO7 local relation. -/
theorem ko7_dpEvidence_not_boundary_event (b s n : Trace) :
    ¬ BoundaryEvent LocalRaw EqWBreakerNode.source unitSurface roleWeights
      (dpEvidence b s n) := by
  unfold BoundaryEvent
  rw [ko7_dpEvidence_gap_zero]
  exact lt_irrefl 0

/-- On the KO7 local relation, `roleEcho` has an Omega gap one bit larger than `dpEvidence`. -/
theorem ko7_one_bit_dp_exchange (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        roleEcho -
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        (dpEvidence b s n) = 1 := by
  rw [ko7_gap_of_fork3, ko7_gap_of_fork3, dpEvidence_eq_roleResolving]
  exact one_bit_dp_exchange

/-- On the KO7 local relation, the Omega gap difference between `roleEcho` and `dpEvidence` equals the Gate's branch-entropy difference at the same source. -/
theorem ko7_exchange_bit_eq_gate_refused_bit (b s n : Trace) :
    overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        roleEcho -
      overproductionGap LocalRaw EqWBreakerNode.source unitSurface roleWeights
        (dpEvidence b s n) =
    branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) -
      branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source) := by
  rw [ko7_one_bit_dp_exchange, refused_bit_eq_spent_bit_ko7.1, branchEntropy_two]

/-! ## Combined exchange statement -/

/-- At `eqW void void`, each value-factored channel has gap one and a boundary event. The dependency-pair channel supplies one licensed bit, has zero gap, and has no boundary event. The gap difference equals the Gate's branch-entropy difference, and the actual channel distinguishes the roles. The result also includes the Gate's accounting identity. -/
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

/-! ## Fixed protocol and relation restriction

The protocol results below use normalized finite source protocols. The termination theorem also requires the no-fresh-variable condition and well-foundedness of the dependency-pair minimal-chain relation.
-/

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCost
open OperatorKO7.Meta.BoundaryObserver.TerminalGapCostExtensions

/-- The dependency-pair channel returns the Boolean code of the occurrence role. -/
theorem actualDPChannel_boolRole (b s n : Trace) (z : Bool) :
    actualDPChannel b s n ((), boolRoleEquiv z) = z := by
  cases z
  · exact actualDPChannel_frame_eq_false b s n
  · exact actualDPChannel_active_eq_true b s n

/-- A normalized output row obtained from the actual dependency-pair selector. -/
def actualDPRoleRow (b s n : Trace) (z : Bool) : FiniteLaw Bool where
  mass y := if actualDPChannel b s n ((), boolRoleEquiv z) = y then 1 else 0
  nonnegative y := by split_ifs <;> norm_num
  total := by simp

/-- The role has a fair prior, and the initial record and action are fixed. -/
def actualDPRoleProtocol (b s n : Trace) : FiniteProtocol Bool Unit Bool where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ z := actualDPRoleRow b s n z
  stop _ := false
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

def actualDPRoleMenu (b s n : Trace) :
    BinaryMenu (actualDPRoleProtocol b s n) (1 / 2) where
  bias _ _ := 1 / 2
  bound _ _ := (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).le
  source _ _ z y := by
    change (if actualDPChannel b s n ((), boolRoleEquiv z) = y then (1 : ℝ) else 0) =
      binaryKernel (1 / 2) z y
    rw [actualDPChannel_boolRole]
    cases z <;> cases y <;> norm_num [binaryKernel]
  reading_cost _ _ := le_rfl

def actualDPRoleConditional (b s n : Trace) : ConditionalProtocol Unit Bool Unit Bool :=
  unitRecordProtocol (actualDPRoleProtocol b s n)

/-- The dependency-pair role observation supplies one conditional Shannon bit. -/
theorem actualDP_conditionalInformation_one (b s n : Trace) :
    conditionalJointInfo (actualDPRoleConditional b s n) 1 (historyBank Unit Bool 1) = 1 := by
  rw [actualDPRoleConditional, unitRecordProtocol_information, terminalMI_horizon_one]
  have hs : (actualDPRoleProtocol b s n).stop [] = false := rfl
  rw [if_pos hs, Fintype.sum_unique]
  change 1 * localGain (actualDPRoleProtocol b s n) [] () = 1
  rw [one_mul]
  have hw : 0 < historyMass (actualDPRoleProtocol b s n) [] := by
    rw [historyMass_nil_eq_one]
    exact zero_lt_one
  have hp : posterior (actualDPRoleProtocol b s n) [] true = 1 / 2 := by
    rw [posterior, prefixMass_nil, historyMass_nil_eq_one, div_one]
    rfl
  rw [binaryMenu_localGain _ (1 / 2) (actualDPRoleMenu b s n) [] () hw, hp]
  simp only [actualDPRoleMenu]
  rw [binaryJoint_information_positive_endpoint]
  have hh : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hh, div_self (Real.log_pos one_lt_two).ne']

/-- Any stochastic reading of the fixed generator's value has the same row for both roles. -/
def fixedValueProtocol {Y : Type} [Fintype Y] (s : Trace) (K : Trace → FiniteLaw Y) :
    FiniteProtocol Bool Unit Y where
  prior := binaryPriorLaw (1 / 2) (by norm_num) (by norm_num)
  policy _ := unitLaw
  observation _ _ _ := K s
  stop _ := false
  cost _ _ := 1
  cost_nonnegative _ _ := zero_le_one

/-- Its gain vanishes at every posterior and retained history, not merely under the fair prior. -/
theorem fixedValueProtocol_zero_capacity {Y : Type} [Fintype Y]
    (s : Trace) (K : Trace → FiniteLaw Y) : LocalCapacityBound (fixedValueProtocol s K) 0 := by
  intro h a hw _ _
  change jointMI (fun zy : Bool × Y =>
    posterior (fixedValueProtocol s K) h zy.1 * (K s).mass zy.2) ≤ 0 * _
  rw [jointMI_product_zero _ _ (posterior_total _ h hw) (K s).total, zero_mul]

theorem fixedValue_conditionalInformation_zero {Y : Type} [Fintype Y]
    (s : Trace) (K : Trace → FiniteLaw Y) (N : ℕ) :
    conditionalJointInfo (unitRecordProtocol (fixedValueProtocol s K))
      N (historyBank Unit Y N) = 0 := by
  apply conditionalJointInfo_zero_capacity _ N _ (historyBank_complete Unit Y N)
  intro u _
  exact fixedValueProtocol_zero_capacity s K

theorem actualDP_terminalGap_zero (b s n : Trace) :
    terminalGap (actualDPRoleConditional b s n) 1 = 0 := by
  rw [terminalGap, terminalEnvelope_bool, actualDP_conditionalInformation_one, sub_self]

theorem fixedValue_terminalGap_one {Y : Type} [Fintype Y]
    (s : Trace) (K : Trace → FiniteLaw Y) (N : ℕ) :
    terminalGap (unitRecordProtocol (fixedValueProtocol s K)) N = 1 := by
  rw [terminalGap, terminalEnvelope_bool, fixedValue_conditionalInformation_zero, sub_zero]

/-- The theorem compares a fixed-value channel with the role observation under the same fair prior; the entropy difference uses `LocalRaw` and `LocalLicensed`. -/
theorem actualDP_reading_equals_local_restriction {Y : Type} [Fintype Y]
    (b s n : Trace) (K : Trace → FiniteLaw Y) :
    conditionalJointInfo (unitRecordProtocol (fixedValueProtocol s K))
      1 (historyBank Unit Y 1) = 0 ∧
    conditionalJointInfo (actualDPRoleConditional b s n)
      1 (historyBank Unit Bool 1) = 1 ∧
    terminalGap (unitRecordProtocol (fixedValueProtocol s K)) 1 -
      terminalGap (actualDPRoleConditional b s n) 1 =
        branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) -
          branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source) := by
  refine ⟨fixedValue_conditionalInformation_zero s K 1,
    actualDP_conditionalInformation_one b s n, ?_⟩
  rw [fixedValue_terminalGap_one, actualDP_terminalGap_zero, sub_zero,
    refused_bit_eq_spent_bit_ko7.1, branchEntropy_two]

/-- The raw-to-licensed branch-entropy difference is one, with zero information gain on both sides. -/
theorem local_restriction_changes_envelope :
    (branchEntropy (terminalMultiplicity LocalRaw EqWBreakerNode.source) - 0) -
      (branchEntropy (terminalMultiplicity LocalLicensed EqWBreakerNode.source) - 0) = 1 := by
  rw [sub_zero, sub_zero, refused_bit_eq_spent_bit_ko7.1, branchEntropy_two]

/-- The termination theorem requires minimal-chain well-foundedness and the no-fresh-variable condition. The role observation does not replace either premise. -/
theorem dependencyPair_termination_consequence {sigma nu : Type} [DecidableEq nu]
    (R : OperatorKO7.Meta.Rewriting.TRS sigma nu)
    (hvars : ∀ rule ∈ R,
      OperatorKO7.Meta.Rewriting.Term.vars rule.rhs ⊆
        OperatorKO7.Meta.Rewriting.Term.vars rule.lhs)
    (hchain : WellFounded (fun d c =>
      OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness.MinChainStep R c d)) :
    WellFounded (fun u t => OperatorKO7.Meta.Rewriting.Step R t u) :=
  OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness.wellFounded_step_of_minChain_wf
    R hvars hchain

#check @actualDPChannel_boolRole
#print axioms actualDPChannel_boolRole
#check @actualDPRoleRow
#print axioms actualDPRoleRow
#check @actualDPRoleProtocol
#print axioms actualDPRoleProtocol
#check @actualDPRoleMenu
#print axioms actualDPRoleMenu
#check @actualDPRoleConditional
#print axioms actualDPRoleConditional
#check @actualDP_conditionalInformation_one
#print axioms actualDP_conditionalInformation_one
#check @fixedValueProtocol
#print axioms fixedValueProtocol
#check @fixedValueProtocol_zero_capacity
#print axioms fixedValueProtocol_zero_capacity
#check @fixedValue_conditionalInformation_zero
#print axioms fixedValue_conditionalInformation_zero
#check @actualDP_terminalGap_zero
#print axioms actualDP_terminalGap_zero
#check @fixedValue_terminalGap_one
#print axioms fixedValue_terminalGap_one
#check @actualDP_reading_equals_local_restriction
#print axioms actualDP_reading_equals_local_restriction
#check @local_restriction_changes_envelope
#print axioms local_restriction_changes_envelope
#check @dependencyPair_termination_consequence
#print axioms dependencyPair_termination_consequence

end

end OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
