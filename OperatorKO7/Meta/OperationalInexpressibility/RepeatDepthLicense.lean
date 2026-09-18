import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Interval.Finset.Fin

/-!
# Exact record cost for finite-observer recurrence

For an arbitrary finite-horizon observation, `repeatDepth` is the rank of the
current index inside its observation fiber.  Its values on a fiber of size
`k` are exactly `0, ..., k - 1`.  The largest fiber therefore gives both the
exact target multiplicity and the exact minimum fixed-length record cost.

Repeat status costs zero bits exactly for injective observers and one bit
exactly for noninjective observers.  Cardinal pigeonhole bounds are corollaries
of this exact classification.  The rank channel attains the exact depth bound.
No fixed finite side alphabet can license exact repeat depth at every horizon,
even for a constant observer.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

universe u v

section FiniteHorizon

variable {N : Nat} {Q : Type u} [DecidableEq Q]

/-- The indices carrying one observation value. -/
def observationFiber (obs : Fin N → Q) (u : Q) : Finset (Fin N) :=
  Finset.univ.filter (fun n => obs n = u)

/-- Earlier indices carrying the current observation. -/
def priorRepeats (obs : Fin N → Q) (n : Fin N) : Finset (Fin N) :=
  (Finset.Iio n).filter (fun j => obs j = obs n)

/-- The number of earlier occurrences of the current observation. -/
def repeatDepth (obs : Fin N → Q) (n : Fin N) : Nat :=
  (priorRepeats obs n).card

/-- Whether the current observation occurred earlier. -/
def repeatStatus (obs : Fin N → Q) (n : Fin N) : Bool :=
  decide (0 < repeatDepth obs n)

/-- The largest observation-fiber cardinality. -/
def maxFiberCard (obs : Fin N → Q) : Nat :=
  (Finset.univ.image obs).sup (fun u => (observationFiber obs u).card)

@[simp] theorem mem_observationFiber (obs : Fin N → Q) (u : Q) (n : Fin N) :
    n ∈ observationFiber obs u ↔ obs n = u := by
  simp [observationFiber]

@[simp] theorem mem_priorRepeats (obs : Fin N → Q) (n j : Fin N) :
    j ∈ priorRepeats obs n ↔ j < n ∧ obs j = obs n := by
  simp [priorRepeats]

/-- Earlier equal-observation indices form a proper subset of the current
observation fiber. -/
theorem priorRepeats_ssubset_ownFiber (obs : Fin N → Q) (n : Fin N) :
    priorRepeats obs n ⊂ observationFiber obs (obs n) := by
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact (mem_observationFiber obs (obs n) j).2
      ((mem_priorRepeats obs n j).1 hj).2
  · intro heq
    have hnFiber : n ∈ observationFiber obs (obs n) :=
      (mem_observationFiber obs (obs n) n).2 rfl
    have hnPrior : n ∈ priorRepeats obs n := by
      rw [heq]
      exact hnFiber
    exact (lt_irrefl n) ((mem_priorRepeats obs n n).1 hnPrior).1

/-- Repeat depth is strictly smaller than the size of its own fiber. -/
theorem repeatDepth_lt_ownFiberCard (obs : Fin N → Q) (n : Fin N) :
    repeatDepth obs n < (observationFiber obs (obs n)).card := by
  exact Finset.card_lt_card (priorRepeats_ssubset_ownFiber obs n)

/-- Every fiber size is bounded by the largest fiber size. -/
theorem observationFiber_card_le_maxFiberCard (obs : Fin N → Q) (u : Q) :
    (observationFiber obs u).card ≤ maxFiberCard obs := by
  unfold maxFiberCard
  by_cases hu : u ∈ Finset.univ.image obs
  · exact Finset.le_sup (f := fun v => (observationFiber obs v).card) hu
  · have hempty : observationFiber obs u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      apply hu
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_univ n, (mem_observationFiber obs u n).1 hn⟩
    simp [hempty]

/-- Every realized depth fits in the exact largest-fiber alphabet. -/
theorem repeatDepth_lt_maxFiberCard (obs : Fin N → Q) (n : Fin N) :
    repeatDepth obs n < maxFiberCard obs :=
  (repeatDepth_lt_ownFiberCard obs n).trans_le
    (observationFiber_card_le_maxFiberCard obs (obs n))

/-- Within one observation fiber, depth strictly increases with the index. -/
theorem repeatDepth_strict_on_fiber (obs : Fin N → Q) {i j : Fin N}
    (hij : i < j) (hobs : obs i = obs j) :
    repeatDepth obs i < repeatDepth obs j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    have hk' := (mem_priorRepeats obs i k).1 hk
    exact (mem_priorRepeats obs j k).2
      ⟨hk'.1.trans hij, hk'.2.trans hobs⟩
  · intro heq
    have hiRight : i ∈ priorRepeats obs j :=
      (mem_priorRepeats obs j i).2 ⟨hij, hobs⟩
    have hiLeft : i ∈ priorRepeats obs i := by
      rw [heq]
      exact hiRight
    exact (lt_irrefl i) ((mem_priorRepeats obs i i).1 hiLeft).1

/-- Depth is injective on each observation fiber. -/
theorem repeatDepth_injective_on_fiber (obs : Fin N → Q) {i j : Fin N}
    (hobs : obs i = obs j) (hdepth : repeatDepth obs i = repeatDepth obs j) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hlt := repeatDepth_strict_on_fiber obs hij hobs
    omega
  · have hlt := repeatDepth_strict_on_fiber obs hji hobs.symm
    omega

/-- On a fiber of size `k`, repeat depth realizes exactly `0, ..., k - 1`. -/
theorem repeatDepth_values_on_fiber (obs : Fin N → Q) (u : Q) :
    (observationFiber obs u).image (repeatDepth obs) =
      Finset.range (observationFiber obs u).card := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hobs : obs n = u := (mem_observationFiber obs u n).1 hn
    have hlt := repeatDepth_lt_ownFiberCard obs n
    simpa [hobs] using hlt
  · rw [Finset.card_range]
    rw [(Finset.card_image_iff).2]
    intro i hi j hj hij
    apply repeatDepth_injective_on_fiber obs
    · exact ((mem_observationFiber obs u i).1 hi).trans
        ((mem_observationFiber obs u j).1 hj).symm
    · exact hij

/-- The number of depth values in every observer fiber equals that fiber's
cardinality. -/
theorem fiberVerdicts_repeatDepth_card (obs : Fin N → Q) (u : Q) :
    (fiberVerdicts obs (repeatDepth obs) u).card =
      (observationFiber obs u).card := by
  unfold fiberVerdicts observationFiber
  rw [(Finset.card_image_iff).2]
  intro i hi j hj hij
  apply repeatDepth_injective_on_fiber obs
  · exact (Finset.mem_filter.1 hi).2.trans (Finset.mem_filter.1 hj).2.symm
  · exact hij

/-- The target multiplicity of exact depth is exactly the largest observer
fiber, for every finite observation map. -/
theorem repeatDepth_fiberMultiplicity_eq_maxFiberCard (obs : Fin N → Q) :
    fiberMultiplicity obs (repeatDepth obs) = maxFiberCard obs := by
  unfold fiberMultiplicity maxFiberCard
  exact Finset.sup_congr rfl fun u _ => fiberVerdicts_repeatDepth_card obs u

/-- The exact fixed-length depth deficit is the ceiling logarithm of the
largest observation fiber. -/
theorem repeatDepth_fiberCodeDeficit_exact (obs : Fin N → Q) :
    fiberCodeDeficit obs (repeatDepth obs) = Nat.clog 2 (maxFiberCard obs) := by
  unfold fiberCodeDeficit fiberDeficit
  rw [repeatDepth_fiberMultiplicity_eq_maxFiberCard]

/-- Repeat depth itself gives an exact rank channel with the smallest
possible alphabet size. -/
def fiberRankChannel (obs : Fin N → Q) (n : Fin N) : Fin (maxFiberCard obs) :=
  ⟨repeatDepth obs n, repeatDepth_lt_maxFiberCard obs n⟩

@[simp] theorem fiberRankChannel_val (obs : Fin N → Q) (n : Fin N) :
    (fiberRankChannel obs n).val = repeatDepth obs n :=
  rfl

/-- Current observation plus the rank channel determines exact depth. -/
theorem fiberRank_channel_licenses_repeatDepth (obs : Fin N → Q) :
    FactorsThrough (fun n => (obs n, fiberRankChannel obs n)) (repeatDepth obs) := by
  intro i j hij
  exact congrArg (fun p => p.2.val) hij

/-- The rank channel's alphabet has exactly the largest-fiber cardinality. -/
theorem fiberRank_channel_cardinality_exact (obs : Fin N → Q) :
    Fintype.card (Fin (maxFiberCard obs)) = maxFiberCard obs := by
  simp

/-- Exact minimality in both symbols and fixed-length bits. -/
theorem repeatDepth_minimal_record_cost (obs : Fin N → Q) :
    (∃ r : Fin N → Fin (maxFiberCard obs),
        FactorsThrough (fun n => (obs n, r n)) (repeatDepth obs)) ∧
      (∀ {R : Type v} [Fintype R] (r : Fin N → R),
        FactorsThrough (fun n => (obs n, r n)) (repeatDepth obs) →
          maxFiberCard obs ≤ Fintype.card R) ∧
      (∃ r : Fin N → Fin (2 ^ Nat.clog 2 (maxFiberCard obs)),
        FactorsThrough (fun n => (obs n, r n)) (repeatDepth obs)) ∧
      ∀ {R : Type v} [Fintype R] (r : Fin N → R),
        FactorsThrough (fun n => (obs n, r n)) (repeatDepth obs) →
          Nat.clog 2 (maxFiberCard obs) ≤ Nat.clog 2 (Fintype.card R) := by
  have hSymbols :=
    fiberMultiplicity_is_minimum_side_channel_cardinality obs (repeatDepth obs)
  have hBits := fiberCodeDeficit_is_minimum_fixedLength_bits obs (repeatDepth obs)
  rw [repeatDepth_fiberMultiplicity_eq_maxFiberCard] at hSymbols
  rw [repeatDepth_fiberCodeDeficit_exact] at hBits
  exact ⟨hSymbols.1, hSymbols.2, hBits.1, hBits.2⟩

omit [DecidableEq Q] in
/-- Every index channel determines every target on the finite horizon. -/
theorem index_channel_licenses_every_target (obs : Fin N → Q)
    {V : Type v} (P : Fin N → V) :
    FactorsThrough (fun n => (obs n, n)) P := by
  intro i j hij
  have hEq : i = j := congrArg Prod.snd hij
  subst j
  rfl

/-- The full record index determines repeat status and exact depth. -/
theorem index_channel_licenses_repeat_targets (obs : Fin N → Q) :
    FactorsThrough (fun n => (obs n, n)) (repeatStatus obs) ∧
      FactorsThrough (fun n => (obs n, n)) (repeatDepth obs) :=
  ⟨index_channel_licenses_every_target obs (repeatStatus obs),
    index_channel_licenses_every_target obs (repeatDepth obs)⟩

/-! ## Exact recurrence-status classification -/

/-- A noninjective observer has a fiber containing at least two indices. -/
theorem exists_observationFiber_card_gt_one_of_not_injective
    (obs : Fin N → Q) (hobs : ¬ Function.Injective obs) :
    ∃ u : Q, 1 < (observationFiber obs u).card := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hobs
  have hi : i ∈ observationFiber obs (obs i) :=
    (mem_observationFiber obs (obs i) i).2 rfl
  have hj : j ∈ observationFiber obs (obs i) :=
    (mem_observationFiber obs (obs i) j).2 hij.symm
  exact ⟨obs i, Finset.one_lt_card_iff.mpr ⟨i, j, hi, hj, hne⟩⟩

/-- Any fiber with at least two indices contains the rank-zero/rank-one
repeat-status collision. -/
theorem repeat_status_collision_of_large_fiber (obs : Fin N → Q) {u : Q}
    (hu : 1 < (observationFiber obs u).card) :
    ∃ i j : Fin N, OperationallyInexpressibleAt obs (repeatStatus obs) i j := by
  have hzero : 0 ∈ (observationFiber obs u).image (repeatDepth obs) := by
    rw [repeatDepth_values_on_fiber]
    simp only [Finset.mem_range]
    omega
  have hone : 1 ∈ (observationFiber obs u).image (repeatDepth obs) := by
    rw [repeatDepth_values_on_fiber]
    simp only [Finset.mem_range]
    exact hu
  obtain ⟨i, hiFiber, hiDepth⟩ := Finset.mem_image.mp hzero
  obtain ⟨j, hjFiber, hjDepth⟩ := Finset.mem_image.mp hone
  refine ⟨i, j, ?_⟩
  constructor
  · exact ((mem_observationFiber obs u i).1 hiFiber).trans
      ((mem_observationFiber obs u j).1 hjFiber).symm
  · simp [repeatStatus, hiDepth, hjDepth]

/-- Repeat status fails to factor exactly when the observer is noninjective. -/
theorem repeat_status_collision_of_not_injective (obs : Fin N → Q)
    (hobs : ¬ Function.Injective obs) :
    ∃ i j : Fin N, OperationallyInexpressibleAt obs (repeatStatus obs) i j := by
  obtain ⟨u, hu⟩ := exists_observationFiber_card_gt_one_of_not_injective obs hobs
  exact repeat_status_collision_of_large_fiber obs hu

/-- Current observation determines repeat status exactly for injective
observers. -/
theorem repeatStatus_factorsThrough_iff_injective (obs : Fin N → Q) :
    FactorsThrough obs (repeatStatus obs) ↔ Function.Injective obs := by
  constructor
  · intro hfactor
    by_contra hobs
    obtain ⟨i, j, hij⟩ := repeat_status_collision_of_not_injective obs hobs
    exact hij.2 (hfactor hij.1)
  · intro hobs i j hij
    exact congrArg (repeatStatus obs) (hobs hij)

/-- Nonlicensing by current observation is exactly observer noninjectivity. -/
theorem repeat_status_unlicensed_iff_not_injective (obs : Fin N → Q) :
    ¬ FactorsThrough obs (repeatStatus obs) ↔ ¬ Function.Injective obs :=
  not_congr (repeatStatus_factorsThrough_iff_injective obs)

/-- A Boolean target has fiber multiplicity at most two. -/
theorem repeatStatus_fiberMultiplicity_le_two (obs : Fin N → Q) :
    fiberMultiplicity obs (repeatStatus obs) ≤ 2 := by
  unfold fiberMultiplicity
  apply Finset.sup_le
  intro u hu
  calc
    (fiberVerdicts obs (repeatStatus obs) u).card ≤
        (Finset.univ : Finset Bool).card := by
          apply Finset.card_le_card
          intro b hb
          exact Finset.mem_univ b
    _ = 2 := by simp

/-- Every noninjective observer gives repeat status exact multiplicity two. -/
theorem repeatStatus_fiberMultiplicity_eq_two_of_not_injective
    (obs : Fin N → Q) (hobs : ¬ Function.Injective obs) :
    fiberMultiplicity obs (repeatStatus obs) = 2 := by
  have hUpper := repeatStatus_fiberMultiplicity_le_two obs
  obtain ⟨i, j, hcollision⟩ := repeat_status_collision_of_not_injective obs hobs
  have hi : repeatStatus obs i ∈ fiberVerdicts obs (repeatStatus obs) (obs i) :=
    mem_fiberVerdicts.2 ⟨i, rfl, rfl⟩
  have hj : repeatStatus obs j ∈ fiberVerdicts obs (repeatStatus obs) (obs i) :=
    mem_fiberVerdicts.2 ⟨j, hcollision.1.symm, rfl⟩
  have hTwo : 1 < (fiberVerdicts obs (repeatStatus obs) (obs i)).card :=
    Finset.one_lt_card_iff.mpr
      ⟨repeatStatus obs i, repeatStatus obs j, hi, hj, hcollision.2⟩
  have huImage : obs i ∈ Finset.univ.image obs :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hLower := fiberVerdicts_card_le_of_mem
    (q := obs) (P := repeatStatus obs) huImage
  omega

/-- On a nonempty horizon, every injective observer gives repeat status exact
multiplicity one. -/
theorem repeatStatus_fiberMultiplicity_eq_one_of_injective
    (obs : Fin N → Q) (hN : 0 < N) (hobs : Function.Injective obs) :
    fiberMultiplicity obs (repeatStatus obs) = 1 := by
  have hfactor : FactorsThrough obs (repeatStatus obs) :=
    (repeatStatus_factorsThrough_iff_injective obs).2 hobs
  have hUpper := (fiberMultiplicity_le_one_iff obs (repeatStatus obs)).2 hfactor
  let n : Fin N := ⟨0, hN⟩
  have huImage : obs n ∈ Finset.univ.image obs :=
    Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩
  have hmem : repeatStatus obs n ∈ fiberVerdicts obs (repeatStatus obs) (obs n) :=
    mem_fiberVerdicts.2 ⟨n, rfl, rfl⟩
  have hPositive : 0 < (fiberVerdicts obs (repeatStatus obs) (obs n)).card :=
    Finset.card_pos.mpr ⟨repeatStatus obs n, hmem⟩
  have hLower := fiberVerdicts_card_le_of_mem
    (q := obs) (P := repeatStatus obs) huImage
  omega

/-- The empty horizon has repeat-status multiplicity zero. -/
theorem repeatStatus_fiberMultiplicity_eq_zero_of_empty
    (obs : Fin N → Q) (hN : N = 0) :
    fiberMultiplicity obs (repeatStatus obs) = 0 := by
  subst N
  simp [fiberMultiplicity]

/-- Multiplicity zero occurs exactly on the empty horizon. -/
theorem repeatStatus_fiberMultiplicity_eq_zero_iff (obs : Fin N → Q) :
    fiberMultiplicity obs (repeatStatus obs) = 0 ↔ N = 0 := by
  constructor
  · intro hzero
    by_contra hN
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    by_cases hobs : Function.Injective obs
    · have hone := repeatStatus_fiberMultiplicity_eq_one_of_injective obs hNpos hobs
      omega
    · have htwo := repeatStatus_fiberMultiplicity_eq_two_of_not_injective obs hobs
      omega
  · exact repeatStatus_fiberMultiplicity_eq_zero_of_empty obs

/-- Multiplicity one occurs exactly for a nonempty horizon and an injective
observer. -/
theorem repeatStatus_fiberMultiplicity_eq_one_iff (obs : Fin N → Q) :
    fiberMultiplicity obs (repeatStatus obs) = 1 ↔
      0 < N ∧ Function.Injective obs := by
  constructor
  · intro hone
    have hN : 0 < N := by
      by_contra hnot
      have hzeroN : N = 0 := Nat.eq_zero_of_not_pos hnot
      have hzero := repeatStatus_fiberMultiplicity_eq_zero_of_empty obs hzeroN
      omega
    refine ⟨hN, ?_⟩
    by_contra hobs
    have htwo := repeatStatus_fiberMultiplicity_eq_two_of_not_injective obs hobs
    omega
  · rintro ⟨hN, hobs⟩
    exact repeatStatus_fiberMultiplicity_eq_one_of_injective obs hN hobs

/-- Multiplicity two occurs exactly for a noninjective observer. -/
theorem repeatStatus_fiberMultiplicity_eq_two_iff (obs : Fin N → Q) :
    fiberMultiplicity obs (repeatStatus obs) = 2 ↔
      ¬ Function.Injective obs := by
  constructor
  · intro htwo hobs
    by_cases hN : N = 0
    · have hzero := repeatStatus_fiberMultiplicity_eq_zero_of_empty obs hN
      omega
    · have hone := repeatStatus_fiberMultiplicity_eq_one_of_injective obs
        (Nat.pos_of_ne_zero hN) hobs
      omega
  · exact repeatStatus_fiberMultiplicity_eq_two_of_not_injective obs

/-- The repeat-status deficit is zero exactly for injective observers. -/
theorem repeatStatus_fiberCodeDeficit_eq_zero_iff_injective (obs : Fin N → Q) :
    fiberCodeDeficit obs (repeatStatus obs) = 0 ↔ Function.Injective obs :=
  (fiberDeficit_eq_zero_iff_factorsThrough obs (repeatStatus obs)).trans
    (repeatStatus_factorsThrough_iff_injective obs)

/-- The repeat-status deficit is one bit exactly for noninjective observers. -/
theorem repeatStatus_fiberCodeDeficit_eq_one_iff_not_injective
    (obs : Fin N → Q) :
    fiberCodeDeficit obs (repeatStatus obs) = 1 ↔
      ¬ Function.Injective obs := by
  constructor
  · intro hone hobs
    have hzero := (repeatStatus_fiberCodeDeficit_eq_zero_iff_injective obs).2 hobs
    omega
  · intro hobs
    unfold fiberCodeDeficit fiberDeficit
    rw [repeatStatus_fiberMultiplicity_eq_two_of_not_injective obs hobs]
    exact Nat.clog_eq_one (le_refl 2) (le_refl 2)

/-- Every repeat-status deficit is either zero or one bit. -/
theorem repeatStatus_fiberCodeDeficit_dichotomy (obs : Fin N → Q) :
    fiberCodeDeficit obs (repeatStatus obs) = 0 ∨
      fiberCodeDeficit obs (repeatStatus obs) = 1 := by
  classical
  by_cases hobs : Function.Injective obs
  · exact Or.inl ((repeatStatus_fiberCodeDeficit_eq_zero_iff_injective obs).2 hobs)
  · exact Or.inr
      ((repeatStatus_fiberCodeDeficit_eq_one_iff_not_injective obs).2 hobs)

/-! ## Cardinal pigeonhole corollaries -/

/-- If there are more indices than observation values, one observation fiber
has at least two indices. -/
theorem exists_observationFiber_card_gt_one [Fintype Q] (obs : Fin N → Q)
    (hN : Fintype.card Q < N) :
    ∃ u : Q, 1 < (observationFiber obs u).card := by
  obtain ⟨u, -, hu⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset Q)) (f := obs) (n := 1)
      (fun _ _ => Finset.mem_univ _) (by simpa using hN)
  exact ⟨u, by simpa [observationFiber] using hu⟩

/-- The first and second ranks in a repeated fiber have equal current
observation and opposite repeat-status values. -/
theorem repeat_status_collision [Fintype Q] (obs : Fin N → Q)
    (hN : Fintype.card Q < N) :
    ∃ i j : Fin N, OperationallyInexpressibleAt obs (repeatStatus obs) i j := by
  obtain ⟨u, hu⟩ := exists_observationFiber_card_gt_one obs hN
  exact repeat_status_collision_of_large_fiber obs hu

/-- Repeat status does not factor through the current observation whenever
the horizon exceeds the observer alphabet. -/
theorem repeat_status_unlicensed_by_current_observation [Fintype Q] (obs : Fin N → Q)
    (hN : Fintype.card Q < N) :
    ¬ FactorsThrough obs (repeatStatus obs) := by
  obtain ⟨i, j, hij⟩ := repeat_status_collision obs hN
  exact not_factorsThrough_of_collision hij

/-- Under the same sharp pigeonhole premise, repeat status has exact target
multiplicity two. -/
theorem repeatStatus_fiberMultiplicity_eq_two [Fintype Q] (obs : Fin N → Q)
    (hN : Fintype.card Q < N) :
    fiberMultiplicity obs (repeatStatus obs) = 2 := by
  apply repeatStatus_fiberMultiplicity_eq_two_of_not_injective obs
  intro hInjective
  have hCard := Fintype.card_le_of_injective obs hInjective
  have hCard' : N ≤ Fintype.card Q := by simpa using hCard
  omega

/-- Repeat status costs exactly one fixed-length bit. -/
theorem repeatStatus_fiberCodeDeficit_eq_one [Fintype Q] (obs : Fin N → Q)
    (hN : Fintype.card Q < N) :
    fiberCodeDeficit obs (repeatStatus obs) = 1 := by
  unfold fiberCodeDeficit fiberDeficit
  rw [repeatStatus_fiberMultiplicity_eq_two obs hN]
  exact Nat.clog_eq_one (le_refl 2) (le_refl 2)

/-! ## Pigeonhole lower bound -/

/-- The exact largest fiber is at least the ceiling of the average fiber
size. -/
theorem maxFiberCard_ge_ceiling_div [Fintype Q] (obs : Fin N → Q) (hN : 0 < N) :
    N ⌈/⌉ Fintype.card Q ≤ maxFiberCard obs := by
  letI : Nonempty Q := ⟨obs ⟨0, hN⟩⟩
  have hQ : 0 < Fintype.card Q := Fintype.card_pos
  let k := N ⌈/⌉ Fintype.card Q
  have hkpos : 0 < k := by
    by_contra hk
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
    have hNle : N ≤ Fintype.card Q * 0 :=
      (ceilDiv_le_iff_le_mul hQ).1 (by simp [k, hkzero])
    simp at hNle
    omega
  have hAverage : Fintype.card Q * (k - 1) < N := by
    by_contra hnot
    have hNle : N ≤ Fintype.card Q * (k - 1) := Nat.le_of_not_gt hnot
    have hk_le : k ≤ k - 1 := (ceilDiv_le_iff_le_mul hQ).2 hNle
    omega
  obtain ⟨u, -, hu⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset Q)) (f := obs) (n := k - 1)
      (fun _ _ => Finset.mem_univ _) (by simpa using hAverage)
  have hkFiber : k ≤ (observationFiber obs u).card := by
    have : k - 1 < (observationFiber obs u).card := by
      simpa [observationFiber] using hu
    omega
  exact hkFiber.trans (observationFiber_card_le_maxFiberCard obs u)

/-- The exact depth deficit dominates the pigeonhole lower bound. -/
theorem repeatDepth_deficit_ge_ceiling_average [Fintype Q]
    (obs : Fin N → Q) (hN : 0 < N) :
    Nat.clog 2 (N ⌈/⌉ Fintype.card Q) ≤
      fiberCodeDeficit obs (repeatDepth obs) := by
  rw [repeatDepth_fiberCodeDeficit_exact]
  exact Nat.clog_mono_right 2 (maxFiberCard_ge_ceiling_div obs hN)

end FiniteHorizon

/-! ## No fixed finite record alphabet works at every horizon -/

/-- The constant observer is the strongest counterexample for horizon-free
exact-depth coding: every index belongs to one fiber. -/
def constantObserver (N : Nat) : Fin N → Unit := fun _ => ()

@[simp] theorem maxFiberCard_constantObserver (N : Nat) :
    maxFiberCard (constantObserver N) = N := by
  apply le_antisymm
  · unfold maxFiberCard
    apply Finset.sup_le
    intro u hu
    calc
      (observationFiber (constantObserver N) u).card ≤
          (Finset.univ : Finset (Fin N)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = N := by simp
  · have hLower :=
      observationFiber_card_le_maxFiberCard (constantObserver N) ()
    simpa [observationFiber, constantObserver] using hLower

@[simp] theorem repeatDepth_constantObserver (N : Nat) (n : Fin N) :
    repeatDepth (constantObserver N) n = n.val := by
  simp [repeatDepth, priorRepeats, constantObserver]

/-- Any finite side alphabet licensing exact depth for the constant observer
has at least `N` symbols. -/
theorem constant_observer_side_channel_card_lower_bound
    {R : Type v} [Fintype R] (N : Nat) (r : Fin N → R)
    (h : FactorsThrough
      (fun n => (constantObserver N n, r n))
      (repeatDepth (constantObserver N))) :
    N ≤ Fintype.card R := by
  have hLower := additional_channel_card_lower_bound
    (constantObserver N) (repeatDepth (constantObserver N)) r h
  rw [repeatDepth_fiberMultiplicity_eq_maxFiberCard,
    maxFiberCard_constantObserver] at hLower
  exact hLower

/-- No fixed finite side alphabet can license exact repeat depth at every
horizon, even if its encoding is redesigned separately for each horizon. -/
theorem no_fixed_finite_side_channel_licenses_all_repeatDepths
    {R : Type v} [Fintype R] :
    ¬ ∀ N : Nat, ∃ r : Fin N → R,
      FactorsThrough
        (fun n => (constantObserver N n, r n))
        (repeatDepth (constantObserver N)) := by
  intro hAll
  obtain ⟨r, hr⟩ := hAll (Fintype.card R + 1)
  have hLower := constant_observer_side_channel_card_lower_bound
    (Fintype.card R + 1) r hr
  omega

/-- The finite-observer theorem package: exact status cost, exact depth cost,
a tight rank channel, and the horizon-free impossibility all hold without a
KO7-specific carrier. -/
theorem repeat_depth_license_complete :
    (∀ {N : Nat} {Q : Type u} [DecidableEq Q]
      (obs : Fin N → Q),
        fiberMultiplicity obs (repeatDepth obs) = maxFiberCard obs) ∧
    (∀ {N : Nat} {Q : Type u} [DecidableEq Q]
      (obs : Fin N → Q),
        fiberMultiplicity obs (repeatStatus obs) = 0 ↔ N = 0) ∧
    (∀ {N : Nat} {Q : Type u} [DecidableEq Q]
      (obs : Fin N → Q),
        fiberCodeDeficit obs (repeatStatus obs) = 0 ↔ Function.Injective obs) ∧
    (∀ {N : Nat} {Q : Type u} [DecidableEq Q]
      (obs : Fin N → Q),
        fiberCodeDeficit obs (repeatStatus obs) = 1 ↔ ¬ Function.Injective obs) ∧
    (∀ {R : Type v} [Fintype R],
      ¬ ∀ N : Nat, ∃ r : Fin N → R,
        FactorsThrough
          (fun n => (constantObserver N n, r n))
          (repeatDepth (constantObserver N))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N Q instQ obs
    exact repeatDepth_fiberMultiplicity_eq_maxFiberCard obs
  · intro N Q instQ obs
    exact repeatStatus_fiberMultiplicity_eq_zero_iff obs
  · intro N Q instQ obs
    exact repeatStatus_fiberCodeDeficit_eq_zero_iff_injective obs
  · intro N Q instQ obs
    exact repeatStatus_fiberCodeDeficit_eq_one_iff_not_injective obs
  · intro R instR
    exact no_fixed_finite_side_channel_licenses_all_repeatDepths

end OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense
