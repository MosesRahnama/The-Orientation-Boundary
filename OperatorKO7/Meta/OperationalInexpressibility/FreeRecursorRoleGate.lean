import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
import OperatorKO7.Meta.DistinctionBoundary.MinimalForkQuantitative

/-!
# Role selection on the free recursor

The generator occurs at paths `[0]` and `[1,1]` in the successor output.
The channel compares each containing branch with the actual extracted call.
Value refusal and role selection concern one output. The uniform law gives one
bit; arbitrary binary laws satisfy the computed joint-posterior factorization.
The binary record fork is not a nonconfluence claim about the free recursor.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord

universe u

def children : RecursorTerm → List RecursorTerm
  | .void => []
  | .delta t | .integrate t => [t]
  | .merge a b | .app a b | .eqWit a b => [a, b]
  | .recR b s n => [b, s, n]

def subtermAt : RecursorTerm → List Nat → Option RecursorTerm
  | t, [] => some t
  | t, i :: p => ((children t)[i]?).bind (fun child => subtermAt child p)

structure LocatedOccurrence (t : RecursorTerm) where
  path : List Nat
  value : RecursorTerm
  at_path : subtermAt t path = some value

/-- Parameters only; all relations, observations and certificates are derived. -/
structure FreeBoundaryKernel where
  base : RecursorTerm
  generator : RecursorTerm
  counter : RecursorTerm

def FreeBoundaryKernel.source (K : FreeBoundaryKernel) : RecursorTerm :=
  .recR K.base K.generator (.delta K.counter)

def FreeBoundaryKernel.callee (K : FreeBoundaryKernel) : RecursorTerm :=
  .recR K.base K.generator K.counter

def FreeBoundaryKernel.output (K : FreeBoundaryKernel) : RecursorTerm :=
  .app K.generator K.callee

theorem FreeBoundaryKernel.extraction (K : FreeBoundaryKernel) :
    extractCall K.source K.output = some K.callee := by
  simp [extractCall, source, output, callee]

theorem FreeBoundaryKernel.step_and_pair (K : FreeBoundaryKernel) :
    FreeRecursorStep K.source K.output ∧ FreeRecursorDPPair K.source K.callee :=
  freeRecursor_extraction_sound K.extraction

def generatorPath : Role → List Nat
  | .frame => [0]
  | .active => [1, 1]

def branchPath : Role → List Nat
  | .frame => [0]
  | .active => [1]

theorem generatorPath_distinct : generatorPath .frame ≠ generatorPath .active := by decide

theorem generator_at_path (K : FreeBoundaryKernel) (r : Role) :
    subtermAt K.output (generatorPath r) = some K.generator := by
  cases r <;> rfl

def generatorOccurrence (K : FreeBoundaryKernel) (r : Role) : LocatedOccurrence K.output where
  path := generatorPath r
  value := K.generator
  at_path := generator_at_path K r

def generatorValue (K : FreeBoundaryKernel) (r : Role) : RecursorTerm :=
  (generatorOccurrence K r).value

def generatorFrame (K : FreeBoundaryKernel) : Occ RecursorTerm :=
  (generatorValue K .frame, .frame)

def generatorActive (K : FreeBoundaryKernel) : Occ RecursorTerm :=
  (generatorValue K .active, .active)

theorem freeRecursor_generator_pair_value_diag (K : FreeBoundaryKernel) :
    (generatorFrame K).1 = (generatorActive K).1 ∧
      subtermAt K.output [0] = some K.generator ∧
      subtermAt K.output [1, 1] = some K.generator := ⟨rfl, rfl, rfl⟩

theorem freeRecursor_generator_pair_role_distinct (K : FreeBoundaryKernel) :
    (generatorFrame K).2 ≠ (generatorActive K).2 := by
  change Role.frame ≠ Role.active
  decide

theorem generator_occurrences_distinct (K : FreeBoundaryKernel) :
    generatorOccurrence K .frame ≠ generatorOccurrence K .active := by
  intro h
  exact generatorPath_distinct (congrArg LocatedOccurrence.path h)

theorem generator_ne_callee (K : FreeBoundaryKernel) : K.generator ≠ K.callee := by
  have hlt : rootWeight K.generator < rootWeight K.callee := by
    simp only [FreeBoundaryKernel.callee, rootWeight]
    nlinarith
  exact fun h => (Nat.ne_of_lt hlt) (congrArg rootWeight h)

/-- Equality with the extracted call, computed from actual output branches. -/
def actualDPChannel (K : FreeBoundaryKernel) (r : Role) : Bool :=
  decide (subtermAt K.output (branchPath r) = extractCall K.source K.output)

theorem actualDPChannel_frame (K : FreeBoundaryKernel) : actualDPChannel K .frame = false := by
  unfold actualDPChannel
  rw [K.extraction]
  change decide (some K.generator = some K.callee) = false
  exact decide_eq_false (fun h => generator_ne_callee K (Option.some.inj h))

theorem actualDPChannel_active (K : FreeBoundaryKernel) : actualDPChannel K .active = true := by
  unfold actualDPChannel
  rw [K.extraction]
  change decide (some K.callee = some K.callee) = true
  simp

theorem freeRecursor_dp_channel_decodes_active (K : FreeBoundaryKernel) (r : Role) :
    actualDPChannel K r = true ↔ r = .active := by
  cases r <;> simp [actualDPChannel_frame, actualDPChannel_active]

theorem actualDPChannel_injective (K : FreeBoundaryKernel) :
    Function.Injective (actualDPChannel K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [actualDPChannel_frame, actualDPChannel_active]

theorem freeRecursor_dp_channel_is_exogenous_separator (K : FreeBoundaryKernel) :
    generatorValue K .frame = generatorValue K .active ∧
      actualDPChannel K .frame ≠ actualDPChannel K .active :=
  ⟨rfl, fun h => Role.noConfusion (actualDPChannel_injective K h)⟩

theorem freeRecursor_dp_channel_not_value_factored (K : FreeBoundaryKernel) :
    ¬ ∃ g : RecursorTerm → Bool, ∀ r, actualDPChannel K r = g (generatorValue K r) := by
  rintro ⟨g, hg⟩
  exact (freeRecursor_dp_channel_is_exogenous_separator K).2
    ((hg .frame).trans (hg .active).symm)

/-- Any channel decodes this actual decision exactly iff it separates the roles. -/
theorem channel_decodes_iff_separates (K : FreeBoundaryKernel)
    {C : Type u} (c : Role → C) :
    (∃ decode : C → Bool, ∀ r, decode (c r) = actualDPChannel K r) ↔
      c .frame ≠ c .active := by
  classical
  constructor
  · rintro ⟨decode, hd⟩ heq
    exact (freeRecursor_dp_channel_is_exogenous_separator K).2
      ((hd .frame).symm.trans ((congrArg decode heq).trans (hd .active)))
  · intro hne
    refine ⟨fun x => decide (x = c .active), ?_⟩
    intro r
    cases r <;> simp [hne, actualDPChannel_frame, actualDPChannel_active]

theorem collapsed_channel_impossible (K : FreeBoundaryKernel) :
    ¬ ∃ g : Unit → Bool, ∀ r, g () = actualDPChannel K r := by
  rintro ⟨g, hg⟩
  exact (freeRecursor_dp_channel_is_exogenous_separator K).2
    ((hg .frame).symm.trans (hg .active))

/-- The existing generic distinction-record relation, with no KO7 term carrier. -/
def HasRecord {W : Type} (a b : W) : Prop :=
  ∃ r, (ko7RecordSurface W).emits a b r ∧ (ko7RecordSurface W).nonnull r

theorem hasRecord_iff_ne {W : Type} (a b : W) : HasRecord a b ↔ a ≠ b := by
  constructor
  · rintro ⟨r, he, hn⟩
    exact nonnull_has_distinction (ko7_distinctionComplete W) he hn
  · intro h
    exact ⟨Rec.diff a b, .inr ⟨h, rfl⟩, True.intro⟩

theorem freeRecursor_value_refusal_role_record (K : FreeBoundaryKernel) :
    ¬ HasRecord (generatorValue K .frame) (generatorValue K .active) ∧
      HasRecord Role.frame Role.active := by
  simp only [hasRecord_iff_ne]
  exact ⟨fun h => h rfl, by decide⟩

theorem freeRecursor_role_record_is_dp_license (K : FreeBoundaryKernel) :
    HasRecord Role.frame Role.active ↔
      FreeRecursorStep K.source K.output ∧
      FreeRecursorDPPair K.source K.callee ∧
      actualDPChannel K .frame ≠ actualDPChannel K .active ∧
      ¬ ∃ g : RecursorTerm → Bool, ∀ r, actualDPChannel K r = g (generatorValue K r) := by
  constructor
  · intro _
    exact ⟨K.step_and_pair.1, K.step_and_pair.2,
      (freeRecursor_dp_channel_is_exogenous_separator K).2,
      freeRecursor_dp_channel_not_value_factored K⟩
  · intro _
    exact (freeRecursor_value_refusal_role_record K).2

/-- One source, output, extracted call and pair of actual payload positions. -/
theorem freeBoundaryKernel_two_actions (K : FreeBoundaryKernel) :
    extractCall K.source K.output = some K.callee ∧
    FreeRecursorStep K.source K.output ∧ FreeRecursorDPPair K.source K.callee ∧
    generatorOccurrence K .frame ≠ generatorOccurrence K .active ∧
    generatorValue K .frame = generatorValue K .active ∧
    ¬ HasRecord (generatorValue K .frame) (generatorValue K .active) ∧
    HasRecord Role.frame Role.active ∧
    ¬ ∃ g : RecursorTerm → Bool, ∀ r, actualDPChannel K r = g (generatorValue K r) :=
  ⟨K.extraction, K.step_and_pair.1, K.step_and_pair.2,
    generator_occurrences_distinct K, rfl,
    (freeRecursor_value_refusal_role_record K).1,
    (freeRecursor_value_refusal_role_record K).2,
    freeRecursor_dp_channel_not_value_factored K⟩

def roleIndexEquiv : Role ≃ Fin 2 where
  toFun
    | .active => 0
    | .frame => 1
  invFun i := if i = 0 then .active else .frame
  left_inv r := by cases r <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem channel_true_iff_index_zero (K : FreeBoundaryKernel) (r : Role) :
    actualDPChannel K r = true ↔ roleIndexEquiv r = 0 := by
  cases r <;> simp [actualDPChannel_frame, actualDPChannel_active, roleIndexEquiv]

/-- Uniform posterior on the actual decision cell; each binary cell is a singleton. -/
def channelEvidence (K : FreeBoundaryKernel) : Fin 1 → Fin 2 → Fin 2 → Real :=
  fun _ c x => if actualDPChannel K (roleIndexEquiv.symm c) =
    actualDPChannel K (roleIndexEquiv.symm x) then 1 else 0

open OperatorKO7.Meta.BoundaryGeneral
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

theorem channelEvidence_eq_dpChannel_one (K : FreeBoundaryKernel) :
    channelEvidence K = OverproductionGapRoleExchangeGeneral.dpChannel 1 := by
  rw [OverproductionGapRoleExchangeGeneral.dpChannel_one_eq_roleResolving_two]
  funext w c x
  have hiff : actualDPChannel K (roleIndexEquiv.symm c) =
      actualDPChannel K (roleIndexEquiv.symm x) ↔ c = x :=
    (actualDPChannel_injective K).eq_iff.trans roleIndexEquiv.symm.injective.eq_iff
  simp only [channelEvidence, hiff,
    OverproductionGapRoleExchange.roleResolving,
    OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite.pointMass, eq_comm]

noncomputable def spentBits (K : FreeBoundaryKernel) : Real :=
  OverproductionGap.deficitBits OverproductionGap.unitSurface
    (OverproductionGapRoleExchange.uniformRoleWeights 2) (channelEvidence K)

theorem spentBits_eq_one (K : FreeBoundaryKernel) : spentBits K = 1 := by
  rw [spentBits, channelEvidence_eq_dpChannel_one,
    OverproductionGapRoleExchangeGeneral.dpChannel_deficitBits (r := 1) (by decide)]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]

/-- Record-fork support loss equals the entropy of the computed role channel. -/
theorem freeRecursor_refused_bit_eq_spent_bit (K : FreeBoundaryKernel) :
    terminalHartleyEntropy Fork3Step .source -
      terminalHartleyEntropy Fork3LicensedStep .source = spentBits K ∧
    spentBits K = 1 := by
  rw [fork3_raw_terminalHartleyEntropy_eq_one,
    fork3_licensed_terminalHartleyEntropy_eq_zero, spentBits_eq_one]
  norm_num

/-- The all-arity formula includes the zero-frame boundary case. -/
theorem all_arity_dp_deficit (r : Nat) :
    OverproductionGap.deficitBits OverproductionGap.unitSurface
      (OverproductionGapRoleExchange.uniformRoleWeights (r + 1))
      (OverproductionGapRoleExchangeGeneral.dpChannel r) =
    Real.logb 2 (r + 1 : Nat) -
      ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  cases r with
  | zero =>
      rw [OverproductionGapRoleExchangeGeneral.rary_zero_nonexample,
        OverproductionGapRoleExchange.roleResolving_deficitBits_log (by decide)]
      norm_num
  | succ r =>
      exact OverproductionGapRoleExchangeGeneral.dpChannel_deficitBits (by omega)

theorem all_arity_frame_residual (r : Nat) :
    OverproductionGap.overproductionGap
      (OverproductionGapRoleExchange.starStep (r + 1)) 0 OverproductionGap.unitSurface
      (OverproductionGapRoleExchange.uniformRoleWeights (r + 1))
      (OverproductionGapRoleExchangeGeneral.dpChannel r) =
    ((r : Real) / (r + 1 : Nat)) * Real.logb 2 (r : Real) := by
  cases r with
  | zero =>
      rw [OverproductionGapRoleExchangeGeneral.rary_zero_nonexample,
        OverproductionGapRoleExchange.roleResolving_gap_zero_m (by decide)]
      norm_num
  | succ r => exact OverproductionGapRoleExchangeGeneral.dpChannel_gap (by omega)

/-- Binary evidence from the actual free extraction is the r=1 member. -/
theorem freeRecursor_binary_recovery (K : FreeBoundaryKernel) :
    channelEvidence K = OverproductionGapRoleExchangeGeneral.dpChannel 1 ∧
    spentBits K = 1 ∧
    OverproductionGap.overproductionGap
      (OverproductionGapRoleExchange.starStep 2) 0 OverproductionGap.unitSurface
      (OverproductionGapRoleExchange.uniformRoleWeights 2) (channelEvidence K) = 0 := by
  refine ⟨channelEvidence_eq_dpChannel_one K, spentBits_eq_one K, ?_⟩
  rw [channelEvidence_eq_dpChannel_one]
  exact OverproductionGapRoleExchangeGeneral.rary_one_frame.1

open scoped BigOperators

theorem channel_index_eq_iff (K : FreeBoundaryKernel) (c x : Fin 2) :
    actualDPChannel K (roleIndexEquiv.symm c) =
      actualDPChannel K (roleIndexEquiv.symm x) ↔ c = x :=
  (actualDPChannel_injective K).eq_iff.trans roleIndexEquiv.symm.injective.eq_iff

/-- Pushforward of any role law through the computed Boolean channel. -/
noncomputable def decisionMass (K : FreeBoundaryKernel) (nu : Fin 2 → Real) (b : Bool) : Real :=
  ∑ c, if actualDPChannel K (roleIndexEquiv.symm c) = b then nu c else 0

theorem decisionMass_at_index (K : FreeBoundaryKernel) (nu : Fin 2 → Real) (c : Fin 2) :
    decisionMass K nu (actualDPChannel K (roleIndexEquiv.symm c)) = nu c := by
  simp [decisionMass, channel_index_eq_iff]

def jointMass (K : FreeBoundaryKernel) (nu : Fin 2 → Real) (c : Fin 2) (b : Bool) : Real :=
  if actualDPChannel K (roleIndexEquiv.symm c) = b then nu c else 0

/-- Joint equals marginal times posterior, including zero-mass cells. -/
theorem channelEvidence_joint_factorization (K : FreeBoundaryKernel)
    (nu : Fin 2 → Real) (c x : Fin 2) :
    jointMass K nu x (actualDPChannel K (roleIndexEquiv.symm c)) =
      decisionMass K nu (actualDPChannel K (roleIndexEquiv.symm c)) *
        channelEvidence K 0 c x := by
  rw [decisionMass_at_index]
  by_cases h : c = x
  · subst x
    simp [jointMass, channelEvidence]
  · simp [jointMass, channelEvidence, channel_index_eq_iff, h, Ne.symm h]

theorem channelEvidence_normalized (K : FreeBoundaryKernel) (c : Fin 2) :
    ∑ x, channelEvidence K 0 c x = 1 := by
  simp [channelEvidence, channel_index_eq_iff]

theorem channelEvidence_nonnegative (K : FreeBoundaryKernel) (c x : Fin 2) :
    0 ≤ channelEvidence K 0 c x := by
  unfold channelEvidence
  split_ifs <;> norm_num

/-- Division form is asserted only at an observation of positive mass. -/
theorem channelEvidence_bayes (K : FreeBoundaryKernel) (nu : Fin 2 → Real)
    (c x : Fin 2) (hc : 0 < decisionMass K nu (actualDPChannel K (roleIndexEquiv.symm c))) :
    jointMass K nu x (actualDPChannel K (roleIndexEquiv.symm c)) /
      decisionMass K nu (actualDPChannel K (roleIndexEquiv.symm c)) =
        channelEvidence K 0 c x := by
  rw [channelEvidence_joint_factorization]
  field_simp

/-- The computed channel resolves every role law, not only the uniform law. -/
theorem channelEvidence_deficitBits_general (K : FreeBoundaryKernel) (nu : Fin 2 → Real) :
    OverproductionGap.deficitBits OverproductionGap.unitSurface
      (OverproductionGapRoleExchangeGeneral.roleWeightsOf nu) (channelEvidence K) =
    OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits nu := by
  rw [channelEvidence_eq_dpChannel_one,
    OverproductionGapRoleExchangeGeneral.dpChannel_one_eq_roleResolving_two]
  exact OverproductionGapRoleExchangeGeneral.general_roleResolving_deficitBits nu

theorem channelEvidence_role_gap_general (K : FreeBoundaryKernel) (nu : Fin 2 → Real) :
    OverproductionGap.overproductionGap
      (OverproductionGapRoleExchange.starStep 2) 0 OverproductionGap.unitSurface
      (OverproductionGapRoleExchangeGeneral.roleWeightsOf nu) (channelEvidence K) =
    1 - OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits nu := by
  rw [channelEvidence_eq_dpChannel_one,
    OverproductionGapRoleExchangeGeneral.dpChannel_one_eq_roleResolving_two,
    OverproductionGapRoleExchangeGeneral.general_role_gap (by decide)]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : Real) < 2)]

end OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
