import Mathlib

/-!
# Finite budgeted channel capacity and Omega

For a finite menu of candidate evidence channels, capacity at budget `b` is the
maximum licensed gain among eligible channels. The menu carries a zero-cost
baseline so the feasible set is never empty.
-/
set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.FiniteChannelCapacity

structure ChannelMenu (I : Type) [Fintype I] where
  envelopeBits : Real
  cost : I → Nat
  gainBits : I → Real
  baseline : I
  baseline_cost : cost baseline = 0
  gain_nonneg : ∀ i, 0 ≤ gainBits i
  gain_le_envelope : ∀ i, gainBits i ≤ envelopeBits

/-- Feasible channel indices at budget `b`. -/
def eligible {I : Type} [Fintype I] (M : ChannelMenu I) (b : Nat) : Finset I :=
  Finset.univ.filter (fun i => M.cost i ≤ b)

/-- The baseline is feasible at every budget. -/
theorem baseline_mem_eligible {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : M.baseline ∈ eligible M b := by
  simp [eligible, M.baseline_cost]

/-- Feasible sets are monotone in budget. -/
theorem eligible_mono {I : Type} [Fintype I]
    (M : ChannelMenu I) {a b : Nat} (hab : a ≤ b) :
    eligible M a ⊆ eligible M b := by
  intro i hi
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans hi hab

/-- A gain-maximizing eligible channel exists at every budget. -/
theorem exists_capacity_witness {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) :
    ∃ i ∈ eligible M b, ∀ j ∈ eligible M b, M.gainBits j ≤ M.gainBits i := by
  exact Finset.exists_max_image (eligible M b) M.gainBits
    ⟨M.baseline, baseline_mem_eligible M b⟩

/-- Chosen maximizing channel. -/
noncomputable def bestChannel {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : I :=
  Classical.choose (exists_capacity_witness M b)

theorem bestChannel_mem {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : bestChannel M b ∈ eligible M b :=
  (Classical.choose_spec (exists_capacity_witness M b)).1

theorem bestChannel_max {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) :
    ∀ j ∈ eligible M b, M.gainBits j ≤ M.gainBits (bestChannel M b) :=
  (Classical.choose_spec (exists_capacity_witness M b)).2

/-- Finite budgeted channel capacity. -/
noncomputable def capacityAt {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : Real :=
  M.gainBits (bestChannel M b)

/-- Capacity is one of the actual channel gains. -/
theorem capacityAt_realized {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) :
    ∃ i ∈ eligible M b, capacityAt M b = M.gainBits i :=
  ⟨bestChannel M b, bestChannel_mem M b, rfl⟩

/-- Capacity is nonnegative. -/
theorem capacityAt_nonneg {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : 0 ≤ capacityAt M b :=
  M.gain_nonneg _

/-- Capacity never exceeds the declared operational envelope. -/
theorem capacityAt_le_envelope {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : capacityAt M b ≤ M.envelopeBits :=
  M.gain_le_envelope _

/-- More budget cannot reduce finite channel capacity. -/
theorem capacityAt_mono {I : Type} [Fintype I]
    (M : ChannelMenu I) : Monotone (capacityAt M) := by
  intro a b hab
  have hmem : bestChannel M a ∈ eligible M b :=
    eligible_mono M hab (bestChannel_mem M a)
  exact bestChannel_max M b (bestChannel M a) hmem

/-- Budgeted Omega against the finite channel capacity. -/
noncomputable def omegaAt {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : Real :=
  M.envelopeBits - capacityAt M b

/-- Budgeted Omega is antitone in the resource budget. -/
theorem omegaAt_nonneg {I : Type} [Fintype I]
    (M : ChannelMenu I) (b : Nat) : 0 ≤ omegaAt M b := by
  unfold omegaAt
  linarith [capacityAt_le_envelope M b]

/-- **W9 headline.** Budgeted Omega is antitone in resource budget. -/
theorem omegaAt_antitone {I : Type} [Fintype I]
    (M : ChannelMenu I) : Antitone (omegaAt M) := by
  intro a b hab
  unfold omegaAt
  linarith [capacityAt_mono M hab]

/-- The decrease in Omega equals the increase in capacity between budgets. -/
theorem omega_drop_eq_capacity_gain {I : Type} [Fintype I]
    (M : ChannelMenu I) (a b : Nat) :
    omegaAt M a - omegaAt M b = capacityAt M b - capacityAt M a := by
  unfold omegaAt
  ring

/-- A two-channel menu whose capacity changes from zero to one bit as budget rises from zero to one. -/
def oneBitMenu : ChannelMenu (Fin 2) where
  envelopeBits := 1
  cost := fun i => if i = 0 then 0 else 1
  gainBits := fun i => if i = 0 then 0 else 1
  baseline := 0
  baseline_cost := by simp
  gain_nonneg := by intro i; split <;> norm_num
  gain_le_envelope := by intro i; split <;> norm_num

/-- At budget zero the one-bit menu has zero capacity. -/
theorem oneBitMenu_capacity_zero : capacityAt oneBitMenu 0 = 0 := by
  have hmem := bestChannel_mem oneBitMenu 0
  have hzero : bestChannel oneBitMenu 0 = 0 := by
    simpa [eligible, oneBitMenu] using hmem
  unfold capacityAt
  rw [hzero]
  rfl

/-- At budget one the full one-bit channel is available and capacity saturates. -/
theorem oneBitMenu_capacity_one : capacityAt oneBitMenu 1 = 1 := by
  have hmax := bestChannel_max oneBitMenu 1 (1 : Fin 2) (by simp [eligible, oneBitMenu])
  have hge : (1 : Real) ≤ capacityAt oneBitMenu 1 := by
    simpa [capacityAt, oneBitMenu] using hmax
  have hle : capacityAt oneBitMenu 1 ≤ (1 : Real) := by
    simpa [oneBitMenu] using capacityAt_le_envelope oneBitMenu 1
  linarith

/-- The one-bit menu has Omega one at budget zero and zero at budget one. -/
theorem oneBitMenu_omega_values :
    omegaAt oneBitMenu 0 = 1 ∧ omegaAt oneBitMenu 1 = 0 := by
  rw [omegaAt, oneBitMenu_capacity_zero, omegaAt, oneBitMenu_capacity_one]
  norm_num [oneBitMenu]

end OperatorKO7.Meta.BoundaryGeneral.FiniteChannelCapacity
