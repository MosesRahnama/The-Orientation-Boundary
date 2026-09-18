import OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
import OperatorKO7.Meta.OperationalInexpressibility.RolePartitionCore

/-!
# Nonuniform partial-role information: instances

Role laws on enumerated carriers, the licensed-channel deficit and the
overproduction gap of a deterministic role partition, and the identification of
the r-ary dependency-pair channel with the active/frame partition. The entropy
laws are in `RolePartitionCore`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.RolePartitionInformation

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.ConditionalEntropy
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGap
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchange
open OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit

universe u v

/- The entropy library is Type-0. General role carriers are reindexed below. -/
variable {R : Type} {C : Type}
variable [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]


/-! ## Arbitrary-universe finite reindexing -/

/-- A normalized role law on an arbitrary-universe finite carrier, represented
computationally by an explicit enumeration. Entropy is evaluated on the
corresponding `Fin n` index carrier. -/
structure EnumeratedRoleLaw (A : Type u) [DecidableEq A] where
  enum : Enumeration A
  prob : A → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_one : ∑ i : Fin enum.items.length, prob (enumerationEquiv enum i) = 1

/-- Reindex an arbitrary-universe role law onto its finite index carrier. -/
def EnumeratedRoleLaw.toFinRoleLaw
    {A : Type u} [DecidableEq A] (L : EnumeratedRoleLaw A) :
    RoleLaw (Fin L.enum.items.length) where
  prob := fun i => L.prob (enumerationEquiv L.enum i)
  nonneg := fun i => L.nonneg (enumerationEquiv L.enum i)
  sum_one := L.sum_one

/-- Entropy in bits of an arbitrary-universe finite role law, defined through
its explicit finite reindexing. -/
noncomputable def enumeratedRoleEntropyBits
    {A : Type u} [DecidableEq A] (L : EnumeratedRoleLaw A) : ℝ :=
  HBits L.toFinRoleLaw.prob

/-- Reindex a deterministic partition of arbitrary carriers onto finite index
carriers. -/
def reindexedPartition
    {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]
    (EA : Enumeration A) (EB : Enumeration B) (part : A → B) :
    Fin EA.items.length → Fin EB.items.length := fun i =>
  (enumerationEquiv EB).symm (part (enumerationEquiv EA i))

/-- Finite reindexing preserves the actual partition label at every address. -/
@[simp] theorem reindexedPartition_realizes
    {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]
    (EA : Enumeration A) (EB : Enumeration B) (part : A → B)
    (i : Fin EA.items.length) :
    enumerationEquiv EB (reindexedPartition EA EB part i) =
      part (enumerationEquiv EA i) := by
  simp [reindexedPartition]


/-- Arbitrary-universe deterministic partition entropy decomposition, computed
on the finite index representation. The default index affects only zero-mass
conditional cells. -/
theorem enumerated_role_partition_bits_decomposition
    {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]
    (L : EnumeratedRoleLaw A) (EB : Enumeration B) (part : A → B)
    (defaultIndex : Fin L.enum.items.length) :
    enumeratedRoleEntropyBits L =
      partitionSpentBits L.toFinRoleLaw (reindexedPartition L.enum EB part) +
      partitionResidualBits defaultIndex L.toFinRoleLaw
        (reindexedPartition L.enum EB part) := by
  exact role_partition_bits_decomposition defaultIndex L.toFinRoleLaw
    (reindexedPartition L.enum EB part)

/-- One-cell outer weight table for a deterministic role partition. -/
def partitionWeights (L : RoleLaw R) (part : R → C) : Fin 1 → C → ℝ :=
  fun _ c => partitionMass L part c

/-- Evidence channel that reports only the deterministic partition cell. -/
noncomputable def partitionEvidence
    (defaultRole : R) (L : RoleLaw R) (part : R → C) : Fin 1 → C → R → ℝ :=
  fun _ c => withinCell defaultRole L part c

/-- Mixing the partition conditionals reconstructs the original role law. -/
theorem partitionEvidence_mixture_eq_prob
    (defaultRole : R) (L : RoleLaw R) (part : R → C) (w : Fin 1) :
    (fun r : R => ∑ c, partitionWeights L part w c *
      partitionEvidence defaultRole L part w c r) = L.prob := by
  funext r
  calc
    ∑ c, partitionWeights L part w c * partitionEvidence defaultRole L part w c r
        = ∑ c, partitionJoint defaultRole L part (r, c) := by rfl
    _ = ∑ c, deterministicPartitionJoint L part (r, c) := by
      rw [partitionJoint_eq_deterministic defaultRole L part]
    _ = L.prob r := by
      simp [deterministicPartitionJoint]

/-- The licensed-channel deficit generated by a deterministic partition is the
entropy of the partition label. -/
theorem partition_deficitBits_eq_spent
    (defaultRole : R) (L : RoleLaw R) (part : R → C) :
    deficitBits unitSurface (partitionWeights L part)
        (partitionEvidence defaultRole L part) = partitionSpentBits L part := by
  unfold deficitBits deficit condEntropyDirect condEntropyLicensed unitSurface
    partitionWeights partitionEvidence partitionSpentBits
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [one_mul]
  have hmix := partitionEvidence_mixture_eq_prob defaultRole L part (0 : Fin 1)
  have hmix' : (fun r : R => ∑ c, partitionMass L part c *
      withinCell defaultRole L part c r) = L.prob := by
    simpa [partitionWeights, partitionEvidence] using hmix
  change (H (fun r : R => ∑ c, partitionMass L part c *
      withinCell defaultRole L part c r) -
      condEntropy (partitionMass L part) (withinCell defaultRole L part)) /
      Real.log 2 = H (partitionMass L part) / Real.log 2
  rw [hmix', role_partition_entropy_decomposition defaultRole L part]
  ring


/-- The nonuniform active/frame licensed-channel deficit is the spent binary
partition information. -/
theorem activeFrame_partitionDeficitBits {r : Nat}
    (activeMass : ℝ) (frameLaw : Fin r → ℝ)
    (ha0 : 0 ≤ activeMass) (ha1 : activeMass ≤ 1)
    (hf0 : ∀ i, 0 ≤ frameLaw i) (hframe : ∑ i, frameLaw i = 1) :
    let L := activeFrameRoleLaw activeMass frameLaw ha0 ha1 hf0 hframe
    deficitBits unitSurface (partitionWeights L activeFramePartition)
      (partitionEvidence 0 L activeFramePartition) = activeFrameSpentBits activeMass := by
  dsimp
  rw [partition_deficitBits_eq_spent,
    activeFrame_partitionSpentBits activeMass frameLaw ha0 ha1 hf0 hframe]

/-- The corresponding overproduction gap uses the actual terminal-support size
of the `(r+1)`-terminal star and subtracts the information spent by the actual
active/frame partition. -/
theorem activeFrame_partitionGap {r : Nat}
    (activeMass : ℝ) (frameLaw : Fin r → ℝ)
    (ha0 : 0 ≤ activeMass) (ha1 : activeMass ≤ 1)
    (hf0 : ∀ i, 0 ≤ frameLaw i) (hframe : ∑ i, frameLaw i = 1) :
    let L := activeFrameRoleLaw activeMass frameLaw ha0 ha1 hf0 hframe
    overproductionGap (starStep (r + 1)) 0 unitSurface
        (partitionWeights L activeFramePartition)
        (partitionEvidence 0 L activeFramePartition) =
      Real.logb 2 (r + 1 : Nat) - activeFrameSpentBits activeMass := by
  dsimp
  unfold overproductionGap
  rw [star_terminalHartleyEntropy (m := r + 1) (by omega),
    activeFrame_partitionDeficitBits activeMass frameLaw ha0 ha1 hf0 hframe]


/-- The live r-ary DP discriminator is exactly the active/frame partition under
`raryOccEquiv`. -/
theorem actual_rary_dp_is_active_frame {r : Nat}
    (o : RaryOcc r) :
    raryDPChannel o = activeFramePartition (raryOccEquiv r o) := by
  cases o <;> simp [raryDPChannel, activeFramePartition, raryOccEquiv]


/-- Under the uniform law, the old DP posterior at any role code agrees with the
new active/frame conditional selected by that code's active/frame partition. -/
theorem uniform_dp_probability_map_agrees {r : Nat} (hr : 1 ≤ r)
    (c x : Fin (r + 1)) :
    dpChannel r 0 c x =
      withinCell 0
        (activeFrameRoleLaw (1 / (r + 1 : ℝ)) (uniformFrameLaw r)
          (uniformActiveMass_mem_unitInterval hr).1
          (uniformActiveMass_mem_unitInterval hr).2
          (uniformFrameLaw_nonneg r)
          (uniformFrameLaw_sum_one hr))
        activeFramePartition (activeFramePartition c) x := by
  let a : ℝ := 1 / (r + 1 : ℝ)
  let FL : Fin r → ℝ := uniformFrameLaw r
  let L : RoleLaw (Fin (r + 1)) :=
    activeFrameRoleLaw a FL
      (uniformActiveMass_mem_unitInterval hr).1
      (uniformActiveMass_mem_unitInterval hr).2
      (uniformFrameLaw_nonneg r)
      (uniformFrameLaw_sum_one hr)
  change dpChannel r 0 c x = withinCell 0 L activeFramePartition
    (activeFramePartition c) x
  have ha0 : a ≠ 0 := by
    dsimp [a]
    positivity
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < r))
  have hden0 : (r + 1 : ℝ) ≠ 0 := by positivity
  have hframeValue : ∀ i : Fin r, FL i = 1 / (r : ℝ) := by
    intro i
    simp [FL, uniformFrameLaw, uniformMass]
  have hmassTrue : partitionMass L activeFramePartition true = a := by
    dsimp [L]
    unfold partitionMass
    rw [Fin.sum_univ_succ]
    simp [activeFrameRoleLaw, activeFramePartition, activeFrameProb]
  have hmassFalse : partitionMass L activeFramePartition false = 1 - a := by
    dsimp [L]
    unfold partitionMass
    rw [Fin.sum_univ_succ]
    simp only [activeFrameRoleLaw, activeFramePartition, activeFrameProb,
      Fin.cases_zero, Fin.cases_succ, Bool.true_eq_false, if_false, if_true, zero_add]
    rw [← Finset.mul_sum]
    change (1 - a) * (∑ i, FL i) = 1 - a
    rw [show (∑ i, FL i) = 1 by
      dsimp [FL]
      exact uniformFrameLaw_sum_one hr]
    ring
  have hframeMass0 : 1 - a ≠ 0 := by
    dsimp [a]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hlt : 1 / (r + 1 : ℝ) < 1 :=
      (div_lt_one (show (0 : ℝ) < r + 1 by positivity)).2 (by linarith)
    exact ne_of_gt (sub_pos.mpr hlt)
  refine Fin.cases ?_ (fun ci => ?_) c
  · rw [dpChannel_active]
    change pointMass 0 x = withinCell 0 L activeFramePartition true x
    unfold withinCell
    rw [hmassTrue]
    simp only [ha0, if_false]
    refine Fin.cases ?_ (fun i => ?_) x
    · simp [L, activeFrameRoleLaw, activeFrameProb, activeFramePartition, pointMass]
      field_simp [ha0]
    · simp [activeFramePartition, pointMass]
  · rw [dpChannel_frame (w := 0) (Fin.succ ci) (Fin.succ_ne_zero ci)]
    change frameUniform r x = withinCell 0 L activeFramePartition false x
    unfold withinCell
    rw [hmassFalse]
    simp only [hframeMass0, if_false, activeFramePartition]
    refine Fin.cases ?_ (fun i => ?_) x
    · simp [frameUniform]
    · simp only [frameUniform, Fin.succ_ne_zero, if_false, L,
        activeFrameRoleLaw, activeFrameProb, Fin.cases_succ]
      rw [hframeValue i]
      have hsub : 1 - a = (r : ℝ) / (r + 1 : ℝ) := by
        dsimp [a]
        field_simp [hden0]
      rw [hsub]
      field_simp [hr0, hden0]
      ring

/-- Existing uniform r-ary information-spend formula, now paired with the
probability-map specialization above. -/
theorem uniform_rary_spent_bits {r : Nat} (hr : 1 ≤ r) :
    deficitBits unitSurface (uniformRoleWeights (r + 1)) (dpChannel r) =
      activeShareEntropyBits r :=
  dpChannel_deficitBits_eq_activeShareEntropy hr

/-- Existing uniform residual formula. The operational term is the actual
terminal support of `starStep (r+1)`, not a label attached to the channel. -/
theorem uniform_rary_residual_gap {r : Nat} (hr : 1 ≤ r) :
    overproductionGap (starStep (r + 1)) 0 unitSurface
        (uniformRoleWeights (r + 1)) (dpChannel r) =
      ((r : ℝ) / (r + 1 : Nat)) * Real.logb 2 (r : ℝ) :=
  dpChannel_gap hr


/-- In the uniform binary one-frame case, the residual frame identity is zero
and the active/frame split supplies the entire role entropy. -/
theorem binary_one_frame_resolves_all :
    overproductionGap (starStep 2) 0 unitSurface
        (uniformRoleWeights 2) (dpChannel 1) = 0 := by
  simpa using (rary_one_frame.1)

end OperatorKO7.Meta.OperationalInexpressibility.RolePartitionInformation
