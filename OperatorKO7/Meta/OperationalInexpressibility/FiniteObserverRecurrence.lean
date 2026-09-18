import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Function.Iterate

/-!
# Finite-observer recurrence

Relation: an arbitrary dynamics `F : X → X` observed through `q : X → Q`.
Closure: iterates `F^[n]`.
Strategy: not applicable.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`.

A finite observer reaches a recurrence within `card Q` steps of any orbit, whether or not the
object reaches a fixed point: two indices below `card Q + 1` carry the same observation. The
repeated indices are adjacent or separated by more than one step. Persistence under later
steps requires compatibility with the dynamics, characterized below by unique dynamics on
the observation image. For every finite decidable observation alphabet, the current
observation alone fails to determine whether it has been seen before. At the first repeated
observation, some earlier stage has the same current observation and opposite repeat-status
verdict. This gives a universal `OperationallyInexpressibleAt` witness within the same
pigeonhole bound. The parity orbit retained below is a concrete executable instance of the
universal theorem. This is the exact mathematical content of the "mirror test" reading: a
memoryless finite observer cannot detect its own recurrence from the current observation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v

/-- **Pigeonhole recurrence.** Any orbit observed through a finite observer repeats an
observation within `card Q` steps. -/
theorem finite_observer_orbit_has_recurrence {X : Type u} {Q : Type v} [Fintype Q]
    (F : X → X) (q : X → Q) (x : X) :
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card Q ∧ q (F^[i] x) = q (F^[j] x) := by
  classical
  let f : Fin (Fintype.card Q + 1) → Q := fun n => q (F^[n.val] x)
  obtain ⟨a, b, hne, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hab | hab
  · exact ⟨a.val, b.val, hab, by omega, hf⟩
  · exact ⟨b.val, a.val, hab, by omega, hf.symm⟩

/-- The repeated observations occur at adjacent indices or at indices farther apart. -/
theorem recurrence_is_fixed_or_cycle {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) (x : X) {i j : Nat} (hij : i < j)
    (h : q (F^[i] x) = q (F^[j] x)) :
    (j = i + 1 ∧ q (F (F^[i] x)) = q (F^[i] x)) ∨ i + 1 < j := by
  rcases Nat.lt_or_ge (i + 1) j with hlt | hge
  · exact Or.inr hlt
  · left
    have hj : j = i + 1 := by omega
    subst hj
    rw [Function.iterate_succ_apply'] at h
    exact ⟨rfl, h.symm⟩

/-! ## Universal memoryless-repeat obstruction -/

/-- Repeat status over an arbitrary decidable observation alphabet: some earlier stage carries
the same current observation. -/
def seenBeforeOf {Q : Type v} [DecidableEq Q] (obs : Nat → Q) (n : Nat) : Bool :=
  (List.range n).any (fun i => decide (obs i = obs n))

/-- The generic repeat-status Boolean has the expected existential semantics. -/
theorem seenBeforeOf_eq_true_iff {Q : Type v} [DecidableEq Q]
    (obs : Nat → Q) (n : Nat) :
    seenBeforeOf obs n = true ↔ ∃ i, i < n ∧ obs i = obs n := by
  rw [seenBeforeOf, List.any_eq_true]
  simp

/-- **First-repeat boundary.** Every finite observed orbit has a least repeated
observation by the pigeonhole bound. At that index repeat status is true, while every earlier
index is still classified as new. -/
theorem finite_observer_has_first_repeat
    {X : Type u} {Q : Type v} [Fintype Q] [DecidableEq Q]
    (F : X → X) (q : X → Q) (x : X) :
    ∃ j : Nat, j ≤ Fintype.card Q ∧
      seenBeforeOf (fun n => q (F^[n] x)) j = true ∧
      ∀ n, n < j → seenBeforeOf (fun m => q (F^[m] x)) n = false := by
  classical
  let obs : Nat → Q := fun n => q (F^[n] x)
  obtain ⟨ir, jr, hirj, hjcard, heq⟩ := finite_observer_orbit_has_recurrence F q x
  have hjseen : seenBeforeOf obs jr = true :=
    (seenBeforeOf_eq_true_iff obs jr).2 ⟨ir, hirj, heq⟩
  have hex : ∃ n, seenBeforeOf obs n = true := ⟨jr, hjseen⟩
  let j0 : Nat := Nat.find hex
  have hj0seen : seenBeforeOf obs j0 = true := by
    dsimp [j0]
    exact Nat.find_spec hex
  have hj0card : j0 ≤ Fintype.card Q := by
    have hj0jr : j0 ≤ jr := by
      dsimp [j0]
      exact Nat.find_min' hex hjseen
    omega
  refine ⟨j0, hj0card, hj0seen, ?_⟩
  intro n hn
  apply Bool.eq_false_of_not_eq_true
  apply Nat.find_min hex
  simpa [j0] using hn

/-- **Universal finite-observer recurrence inexpressibility.** For every orbit observed
through a finite decidable alphabet, before the pigeonhole bound there are two stages with
the same current observation but different repeat-status verdicts. Thus no memoryless
function of the current observation can determine whether that observation has appeared
before. -/
theorem finite_observer_repeat_status_inexpressible
    {X : Type u} {Q : Type v} [Fintype Q] [DecidableEq Q]
    (F : X → X) (q : X → Q) (x : X) :
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card Q ∧
      OperationallyInexpressibleAt
        (fun n => q (F^[n] x))
        (seenBeforeOf (fun n => q (F^[n] x))) i j := by
  classical
  let obs : Nat → Q := fun n => q (F^[n] x)
  obtain ⟨j0, hj0card, hj0seen, hbefore⟩ := finite_observer_has_first_repeat F q x
  obtain ⟨i0, hi0j0, hi0eq⟩ := (seenBeforeOf_eq_true_iff obs j0).1 hj0seen
  have hi0seen : seenBeforeOf obs i0 = false := hbefore i0 hi0j0
  refine ⟨i0, j0, hi0j0, hj0card, ?_⟩
  change obs i0 = obs j0 ∧ seenBeforeOf obs i0 ≠ seenBeforeOf obs j0
  exact ⟨hi0eq, by rw [hi0seen, hj0seen]; decide⟩

/-- **Universal factorization no-go.** The repeat-status target never factors through the
current finite observation along an infinite orbit indexed by `Nat`. -/
theorem finite_observer_repeatStatus_not_factorsThrough
    {X : Type u} {Q : Type v} [Fintype Q] [DecidableEq Q]
    (F : X → X) (q : X → Q) (x : X) :
    ¬ FactorsThrough
      (fun n => q (F^[n] x))
      (seenBeforeOf (fun n => q (F^[n] x))) := by
  obtain ⟨i, j, -, -, hcollision⟩ := finite_observer_repeat_status_inexpressible F q x
  exact not_factorsThrough_of_collision hcollision

/-- **Universal decoder no-go.** No total decoder of the current finite observation can
recover whether that observation has appeared earlier on the orbit. -/
theorem finite_observer_repeatStatus_not_verdictDeterminedBy
    {X : Type u} {Q : Type v} [Fintype Q] [DecidableEq Q]
    (F : X → X) (q : X → Q) (x : X) :
    ¬ VerdictDeterminedBy
      (fun n => q (F^[n] x))
      (seenBeforeOf (fun n => q (F^[n] x))) := by
  intro hdecode
  exact finite_observer_repeatStatus_not_factorsThrough F q x
    (factorsThrough_of_verdictDeterminedBy _ _ hdecode)

/-! ## The repeat-status target is not a function of the current observation -/

/-- Nat specialization of the generic repeat-status predicate. -/
def seenBefore (obs : Nat → Nat) (n : Nat) : Bool := seenBeforeOf obs n

/-- The orbit of `Nat.succ` from `0`. -/
def orbit (n : Nat) : Nat := Nat.succ^[n] 0

theorem orbit_eq (n : Nat) : orbit n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold orbit at ih ⊢
      rw [Function.iterate_succ_apply', ih]

/-- The parity observer read along the orbit. -/
def parityObserve (n : Nat) : Nat := orbit n % 2

theorem parityObserve_eq (n : Nat) : parityObserve n = n % 2 := by
  simp [parityObserve, orbit_eq]

/-- Repeat status of the parity observation along the orbit. -/
def repeatStatus (n : Nat) : Bool := seenBefore parityObserve n

theorem repeatStatus_eq (n : Nat) : repeatStatus n = seenBefore (fun m => m % 2) n := by
  unfold repeatStatus
  have h : parityObserve = fun m => m % 2 := funext parityObserve_eq
  rw [h]

/-- **Memoryless cycle detection is impossible.** Stages `0` and `2` of the orbit carry the
same parity observation and different repeat status, so the repeat-status target does not
factor through the observation. -/
theorem current_observation_does_not_determine_repeat_status :
    OperationallyInexpressibleAt parityObserve repeatStatus 0 2 := by
  refine ⟨?_, ?_⟩
  · rw [parityObserve_eq, parityObserve_eq]
  · rw [repeatStatus_eq, repeatStatus_eq]
    decide

/-- The same fact in the quotient vocabulary: the repeat-status target fails to factor through
the parity observer. -/
theorem repeatStatus_not_factorsThrough :
    ¬ FactorsThrough parityObserve repeatStatus :=
  not_factorsThrough_of_collision current_observation_does_not_determine_repeat_status


/-! ## Dynamics on the observation image -/

/-- Equal observations remain equal after one actual transition. -/
def ObservationCompatible {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) : Prop :=
  ∀ x y, q x = q y → q (F x) = q (F y)

/-- Compatibility with one transition is equivalent to compatibility with every iterate. -/
theorem observationCompatible_iff_all_iterates {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) :
    ObservationCompatible F q ↔
      ∀ n x y, q x = q y → q (F^[n] x) = q (F^[n] y) := by
  constructor
  · intro h n
    induction n with
    | zero => intro x y hxy; exact hxy
    | succ n ih =>
      intro x y hxy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ (ih x y hxy)
  · intro h x y hxy
    simpa only [Function.iterate_one] using h 1 x y hxy

/-- Only values attained by the observer belong to its state space. -/
def ObservedValue {X : Type u} {Q : Type v} (q : X → Q) :=
  { y : Q // ∃ x, q x = y }

def observedValue {X : Type u} {Q : Type v} (q : X → Q) (x : X) :
    ObservedValue q := ⟨q x, x, rfl⟩

/-- Compatibility constructs unique dynamics on the actual observation image. -/
theorem observationCompatible_iff_unique_image_dynamics {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) :
    ObservationCompatible F q ↔
      ∃! G : ObservedValue q → ObservedValue q,
        ∀ x, G (observedValue q x) = observedValue q (F x) := by
  classical
  constructor
  · intro hc
    let G : ObservedValue q → ObservedValue q := fun y =>
      observedValue q (F (Classical.choose y.property))
    have hG : ∀ x, G (observedValue q x) = observedValue q (F x) := by
      intro x
      apply Subtype.ext
      exact hc _ _ (Classical.choose_spec (observedValue q x).property)
    refine ⟨G, hG, ?_⟩
    intro H hH
    funext y
    obtain ⟨x, hx⟩ := y.property
    have hy : observedValue q x = y := Subtype.ext hx
    calc
      H y = H (observedValue q x) := congrArg H hy.symm
      _ = observedValue q (F x) := hH x
      _ = G (observedValue q x) := (hG x).symm
      _ = G y := congrArg G hy
  · rintro ⟨G, hG, _⟩ x y hxy
    have heq : observedValue q x = observedValue q y := Subtype.ext hxy
    have hnext := congrArg G heq
    rw [hG x, hG y] at hnext
    exact congrArg Subtype.val hnext

/-- An observed recurrence persists under every shift when dynamics respects the observer. -/
theorem compatible_recurrence_propagates {X : Type u} {Q : Type v}
    {F : X → X} {q : X → Q} (hc : ObservationCompatible F q)
    (x : X) {i j : Nat} (h : q (F^[i] x) = q (F^[j] x)) (k : Nat) :
    q (F^[i + k] x) = q (F^[j + k] x) := by
  rw [Nat.add_comm i k, Nat.add_comm j k,
    Function.iterate_add_apply, Function.iterate_add_apply]
  exact (observationCompatible_iff_all_iterates F q).mp hc k _ _ h

/-- The transient length plus a positive period is at most the observation count. -/
theorem compatible_finite_observer_eventually_periodic
    {X : Type u} {Q : Type v} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q) (x : X) :
    ∃ start period : Nat, start + period ≤ Fintype.card Q ∧ 0 < period ∧
      ∀ n, start ≤ n → q (F^[n + period] x) = q (F^[n] x) := by
  obtain ⟨i, j, hij, hj, heq⟩ := finite_observer_orbit_has_recurrence F q x
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  intro n hn
  have h := compatible_recurrence_propagates hc x heq (n - i)
  have hleft : i + (n - i) = n := by omega
  have hright : j + (n - i) = n + (j - i) := by omega
  rw [hleft, hright] at h
  exact h.symm

/-! ## Finite observations without any eventual period -/

theorem exponent_lt_pow_two (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

/-- A finite search computes whether a natural number is a power of two. -/
def powerOfTwoObserve (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k => decide (2 ^ k = n))

theorem powerOfTwoObserve_eq_true_iff (n : Nat) :
    powerOfTwoObserve n = true ↔ ∃ k : Nat, 2 ^ k = n := by
  have hfinite :
      powerOfTwoObserve n = true ↔ ∃ k : Nat, k < n + 1 ∧ 2 ^ k = n := by
    simp [powerOfTwoObserve, List.any_eq_true]
  rw [hfinite]
  constructor
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    have hbound := exponent_lt_pow_two k
    exact ⟨k, by omega, hk⟩

theorem no_power_between_successive_powers {k n : Nat}
    (hlo : 2 ^ k < n) (hhi : n < 2 ^ (k + 1)) :
    ¬ ∃ j : Nat, 2 ^ j = n := by
  rintro ⟨j, hj⟩
  by_cases hle : j ≤ k
  · have h := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hle
    omega
  · have hkj : k + 1 ≤ j := by omega
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hkj
    omega

/-- Every proposed positive period fails after every proposed starting index. -/
theorem powerOfTwo_every_eventual_period_refuted (start period : Nat)
    (hp : 0 < period) :
    ∃ n, start ≤ n ∧ powerOfTwoObserve (n + period) ≠ powerOfTwoObserve n := by
  let k := start + period
  have hbound : start + period < 2 ^ k := exponent_lt_pow_two k
  have hlo : 2 ^ k < 2 ^ k + period := by omega
  have hhi : 2 ^ k + period < 2 ^ (k + 1) := by
    rw [pow_succ]
    omega
  have hnot := no_power_between_successive_powers hlo hhi
  have hfalse : powerOfTwoObserve (2 ^ k + period) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hnot ((powerOfTwoObserve_eq_true_iff _).mp h)
  have htrue : powerOfTwoObserve (2 ^ k) = true :=
    (powerOfTwoObserve_eq_true_iff _).mpr ⟨k, rfl⟩
  refine ⟨2 ^ k, by omega, ?_⟩
  rw [hfalse, htrue]
  decide

theorem powerOfTwo_not_eventually_periodic :
    ¬ ∃ start period : Nat, 0 < period ∧
      ∀ n, start ≤ n → powerOfTwoObserve (n + period) = powerOfTwoObserve n := by
  rintro ⟨start, period, hp, hperiod⟩
  obtain ⟨n, hn, hne⟩ := powerOfTwo_every_eventual_period_refuted start period hp
  exact hne (hperiod n hn)

theorem powerOfTwo_recurrence_not_persistent :
    powerOfTwoObserve 1 = powerOfTwoObserve 2 ∧
      powerOfTwoObserve 2 ≠ powerOfTwoObserve 3 := by
  decide

theorem powerOfTwo_not_observationCompatible :
    ¬ ObservationCompatible Nat.succ powerOfTwoObserve := by
  intro hc
  exact powerOfTwo_recurrence_not_persistent.2
    (hc 1 2 powerOfTwo_recurrence_not_persistent.1)

/-- A two-value observer recurs within two steps but has no eventual period. -/
theorem finite_observer_recurrence_without_eventual_periodicity :
    (∃ i j : Nat, i < j ∧ j ≤ Fintype.card Bool ∧
      powerOfTwoObserve (Nat.succ^[i] 0) = powerOfTwoObserve (Nat.succ^[j] 0)) ∧
      ¬ ∃ start period : Nat, 0 < period ∧ ∀ n, start ≤ n →
        powerOfTwoObserve (Nat.succ^[n + period] 0) =
          powerOfTwoObserve (Nat.succ^[n] 0) := by
  constructor
  · exact finite_observer_orbit_has_recurrence Nat.succ powerOfTwoObserve 0
  · intro h
    apply powerOfTwo_not_eventually_periodic
    have hiter (n : Nat) : Nat.succ^[n] 0 = n := orbit_eq n
    simpa only [hiter] using h


/-! ## Finite-time certification of persistent licenses -/

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe w

/-- Observe the evolved state while the target remains a function of the original input. -/
def orbitObserver {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) (n : Nat) (x : X) : Q :=
  q (F^[n] x)

/-- Actual dynamics generates a coarsening sequence exactly when observations
respect one transition. -/
theorem orbitObserver_coarsens_iff {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) :
    ObservationCompatible F q ↔
      ∀ n, ObserverRefines (orbitObserver F q n) (orbitObserver F q (n + 1)) := by
  constructor
  · intro hc n x y hxy
    change q (F^[n + 1] x) = q (F^[n + 1] y)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hc _ _ hxy
  · intro h x y hxy
    exact h 0 hxy

theorem compatible_iterate_mul_of_return {X : Type u} {Q : Type v}
    {F : X → X} {q : X → Q} (hc : ObservationCompatible F q)
    (x : X) {p : Nat} (hp : q (F^[p] x) = q x) (k : Nat) :
    q (F^[p * k] x) = q x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply]
      exact ((observationCompatible_iff_all_iterates F q).mp hc
        (p * k) _ _ hp).trans ih

/-- A transition is injective on observed states that have positive return times. -/
theorem compatible_periodic_cancel {X : Type u} {Q : Type v}
    {F : X → X} {q : X → Q} (hc : ObservationCompatible F q)
    {x y : X} {p r : Nat} (hp : 0 < p) (hr : 0 < r)
    (hx : q (F^[p] x) = q x) (hy : q (F^[r] y) = q y)
    (hnext : q (F x) = q (F y)) : q x = q y := by
  have hxN := compatible_iterate_mul_of_return hc x hx r
  have hyN := compatible_iterate_mul_of_return hc y hy p
  rw [Nat.mul_comm r p] at hyN
  have hpos : 0 < p * r := Nat.mul_pos hp hr
  have heq : q (F^[p * r] x) = q (F^[p * r] y) := by
    have h := (observationCompatible_iff_all_iterates F q).mp hc
      (p * r - 1) (F x) (F y) hnext
    have hn : p * r - 1 + 1 = p * r := by omega
    simpa only [← Function.iterate_succ_apply, Nat.succ_eq_add_one, hn] using h
  exact hxN.symm.trans (heq.trans hyN)

/-- After card(Q)-1 transitions, every observed state has a positive return time. -/
theorem compatible_observer_returns_after_card
    {X : Type u} {Q : Type v} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q)
    (x : X) {n : Nat} (hn : Fintype.card Q - 1 ≤ n) :
    ∃ p : Nat, 0 < p ∧ q (F^[p] (F^[n] x)) = q (F^[n] x) := by
  obtain ⟨start, p, hbound, hp, hperiod⟩ :=
    compatible_finite_observer_eventually_periodic F q hc x
  have hs : start ≤ n := by omega
  have h := hperiod n hs
  rw [Nat.add_comm n p, Function.iterate_add_apply] at h
  exact ⟨p, hp, h⟩

/-- The observer kernel stops growing by card(Q)-1, even when states keep moving. -/
theorem compatible_observer_kernel_stable
    {X : Type u} {Q : Type v} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q)
    {n : Nat} (hn : Fintype.card Q - 1 ≤ n) (x y : X) :
    orbitObserver F q (n + 1) x = orbitObserver F q (n + 1) y ↔
      orbitObserver F q n x = orbitObserver F q n y := by
  constructor
  · intro h
    obtain ⟨p, hp, hx⟩ := compatible_observer_returns_after_card F q hc x hn
    obtain ⟨r, hr, hy⟩ := compatible_observer_returns_after_card F q hc y hn
    apply compatible_periodic_cancel hc hp hr hx hy
    simpa only [orbitObserver, Function.iterate_succ_apply'] using h
  · intro h
    exact (orbitObserver_coarsens_iff F q).mp hc n h

/-- After the cardinality bound, every later observer has exactly the same
kernel as the observer at the bound. This is the full post-bound equality, not
only equality between adjacent stages. -/
theorem compatible_observer_kernel_eq_at_card_pred
    {X : Type u} {Q : Type v} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q)
    {n : Nat} (hn : Fintype.card Q - 1 ≤ n) (x y : X) :
    orbitObserver F q n x = orbitObserver F q n y ↔
      orbitObserver F q (Fintype.card Q - 1) x =
        orbitObserver F q (Fintype.card Q - 1) y := by
  induction n, hn using Nat.le_induction with
  | base => exact Iff.rfl
  | succ n hn ih =>
      exact (compatible_observer_kernel_stable F q hc hn x y).trans ih

theorem compatible_license_loss_dichotomy
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q) (P : X → V) :
    (∀ n, Licensed (orbitObserver F q n) P) ∨
      ∃ k, (∀ n, Licensed (orbitObserver F q n) P ↔ n < k) ∧
        ∃ x y, P x ≠ P y ∧
          (∀ n, n < k → orbitObserver F q n x ≠ orbitObserver F q n y) ∧
          (∀ n, k ≤ n → orbitObserver F q n x = orbitObserver F q n y) :=
  license_coarsening_dichotomy (orbitObserver F q)
    ((orbitObserver_coarsens_iff F q).mp hc) P

/-- Any loss of an original-input target occurs by the finite observation bound. -/
theorem compatible_license_loss_cutoff_le_card_pred
    {X : Type u} {Q : Type v} {V : Type w} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q) (P : X → V)
    {k : Nat} (hcut : ∀ n, Licensed (orbitObserver F q n) P ↔ n < k) :
    k ≤ Fintype.card Q - 1 := by
  by_contra hlate
  obtain ⟨x, y, _, hearly, hafter⟩ :=
    license_cutoff_witness (orbitObserver F q)
      ((orbitObserver_coarsens_iff F q).mp hc) P hcut
  have hk : 0 < k := by omega
  have hcancel := compatible_observer_kernel_stable F q hc
    (n := k - 1) (by omega) x y
  have hcoll : orbitObserver F q ((k - 1) + 1) x =
      orbitObserver F q ((k - 1) + 1) y := by
    have heq : k - 1 + 1 = k := by omega
    rw [heq]
    exact hafter k (Nat.le_refl k)
  exact hearly (k - 1) (by omega) (hcancel.mp hcoll)

/-- A license at one finite stage certifies its validity at every stage. -/
theorem compatible_license_at_card_pred_iff_persistent
    {X : Type u} {Q : Type v} {V : Type w} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q) (P : X → V) :
    Licensed (orbitObserver F q (Fintype.card Q - 1)) P ↔
      ∀ n, Licensed (orbitObserver F q n) P := by
  constructor
  · intro hbound
    rcases compatible_license_loss_dichotomy F q hc P with hall | ⟨k, hcut, _⟩
    · exact hall
    · have hk := compatible_license_loss_cutoff_le_card_pred F q hc P hcut
      have hlt := (hcut _).mp hbound
      omega
  · exact fun h => h _

theorem compatible_license_stable_after_card
    {X : Type u} {Q : Type v} {V : Type w} [Fintype Q]
    (F : X → X) (q : X → Q) (hc : ObservationCompatible F q) (P : X → V)
    {n : Nat} (hn : Fintype.card Q - 1 ≤ n) :
    Licensed (orbitObserver F q n) P ↔
      Licensed (orbitObserver F q (Fintype.card Q - 1)) P := by
  constructor
  · exact licensed_of_coarsening_later (orbitObserver F q)
      ((orbitObserver_coarsens_iff F q).mp hc) P hn
  · intro h
    exact (compatible_license_at_card_pred_iff_persistent F q hc P).mp h n



/-! ## Sharpness of the finite licensing bound -/

/-- Countdown on a finite observation alphabet of k+1 values. -/
def countdown (k : Nat) (x : Fin (k + 1)) : Fin (k + 1) :=
  ⟨x.val - 1, by have hx := x.isLt; omega⟩

theorem countdown_iterate_val (k n : Nat) (x : Fin (k + 1)) :
    ((countdown k)^[n] x).val = x.val - n := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((countdown k)^[n] x).val - 1 = x.val - (n + 1)
      rw [ih]
      omega

/-- The target identifies the largest original input, before any countdown. -/
def countdownTarget (k : Nat) (x : Fin (k + 1)) : Bool :=
  decide (x.val = k)

theorem countdown_compatible (k : Nat) :
    ObservationCompatible (countdown k) (id : Fin (k + 1) → Fin (k + 1)) := by
  intro x y h
  exact congrArg (countdown k) h

/-- For every positive k, recovery fails for the first time at the bound k. -/
theorem countdown_license_iff (k : Nat) (hk : 0 < k) (n : Nat) :
    Licensed (orbitObserver (countdown k) id n) (countdownTarget k) ↔ n < k := by
  constructor
  · intro hlic
    by_contra hn
    let lo : Fin (k + 1) := ⟨0, by omega⟩
    let hi : Fin (k + 1) := ⟨k, by omega⟩
    have heq : orbitObserver (countdown k) id n lo =
        orbitObserver (countdown k) id n hi := by
      apply Fin.ext
      change ((countdown k)^[n] lo).val = ((countdown k)^[n] hi).val
      rw [countdown_iterate_val, countdown_iterate_val]
      simp only [lo, hi, Nat.zero_sub]
      omega
    have hbad := hlic lo hi heq
    have hz : (0 : Nat) ≠ k := by omega
    simp [countdownTarget, lo, hi, hz] at hbad
  · intro hn x y hxy
    have hv := congrArg Fin.val hxy
    change ((countdown k)^[n] x).val = ((countdown k)^[n] y).val at hv
    rw [countdown_iterate_val, countdown_iterate_val] at hv
    by_cases hx : x.val = k
    · have hy : y.val = k := by omega
      simp only [countdownTarget, hx, hy]
    · have hy : y.val ≠ k := by omega
      simp only [countdownTarget, hx, hy]

/-- Every finite bound k>=1 is attained by an actual transition and a Boolean target. -/
theorem finite_license_bound_sharp (k : Nat) (hk : 0 < k) :
    ∃ F : Fin (k + 1) → Fin (k + 1), ∃ P : Fin (k + 1) → Bool,
      ObservationCompatible F id ∧
        ∀ n, Licensed (orbitObserver F id n) P ↔
          n < Fintype.card (Fin (k + 1)) - 1 := by
  refine ⟨countdown k, countdownTarget k, countdown_compatible k, ?_⟩
  intro n
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using countdown_license_iff k hk n


/-! ## Bounds from the attained observation image -/

theorem observedValue_eq_iff {X : Type u} {Q : Type v}
    (q : X → Q) (x y : X) : observedValue q x = observedValue q y ↔ q x = q y :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem observedValue_surjective {X : Type u} {Q : Type v} (q : X → Q) :
    Function.Surjective (observedValue q) := by
  intro y
  obtain ⟨x, hx⟩ := y.property
  exact ⟨x, Subtype.ext hx⟩

theorem observationCompatible_image_iff {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) :
    ObservationCompatible F (observedValue q) ↔ ObservationCompatible F q := by
  constructor
  · intro h x y hxy
    exact congrArg Subtype.val (h x y (Subtype.ext hxy))
  · intro h x y hxy
    exact Subtype.ext (h x y (congrArg Subtype.val hxy))

theorem orbitObserver_image_eq_iff {X : Type u} {Q : Type v}
    (F : X → X) (q : X → Q) (n : Nat) (x y : X) :
    orbitObserver F (observedValue q) n x = orbitObserver F (observedValue q) n y ↔
      orbitObserver F q n x = orbitObserver F q n y :=
  observedValue_eq_iff q (F^[n] x) (F^[n] y)

theorem licensed_orbitObserver_image_iff
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) (P : X → V) (n : Nat) :
    Licensed (orbitObserver F (observedValue q) n) P ↔
      Licensed (orbitObserver F q n) P := by
  constructor
  · intro h x y hxy
    exact h x y ((orbitObserver_image_eq_iff F q n x y).mpr hxy)
  · intro h x y hxy
    exact h x y ((orbitObserver_image_eq_iff F q n x y).mp hxy)

/-- Only attained values need be finite; the ambient observation type may be infinite. -/
theorem finite_image_orbit_has_recurrence
    {X : Type u} {Q : Type v} (F : X → X) (q : X → Q)
    [Finite (ObservedValue q)] (x : X) :
    ∃ i j : Nat, i < j ∧ j ≤ Nat.card (ObservedValue q) ∧
      q (F^[i] x) = q (F^[j] x) := by
  letI := Fintype.ofFinite (ObservedValue q)
  obtain ⟨i, j, hij, hj, heq⟩ := finite_observer_orbit_has_recurrence F (observedValue q) x
  exact ⟨i, j, hij, by simpa only [Nat.card_eq_fintype_card] using hj,
    congrArg Subtype.val heq⟩

theorem compatible_finite_image_eventually_periodic
    {X : Type u} {Q : Type v} (F : X → X) (q : X → Q)
    [Finite (ObservedValue q)] (hc : ObservationCompatible F q) (x : X) :
    ∃ start period : Nat, start + period ≤ Nat.card (ObservedValue q) ∧ 0 < period ∧
      ∀ n, start ≤ n → q (F^[n + period] x) = q (F^[n] x) := by
  letI := Fintype.ofFinite (ObservedValue q)
  obtain ⟨start, period, hb, hp, h⟩ := compatible_finite_observer_eventually_periodic
    F (observedValue q) ((observationCompatible_image_iff F q).mpr hc) x
  exact ⟨start, period, by simpa only [Nat.card_eq_fintype_card] using hb,
    hp, fun n hn => congrArg Subtype.val (h n hn)⟩

theorem compatible_image_kernel_stable
    {X : Type u} {Q : Type v} (F : X → X) (q : X → Q)
    [Finite (ObservedValue q)] (hc : ObservationCompatible F q)
    {n : Nat} (hn : Nat.card (ObservedValue q) - 1 ≤ n) (x y : X) :
    orbitObserver F q (n + 1) x = orbitObserver F q (n + 1) y ↔
      orbitObserver F q n x = orbitObserver F q n y := by
  letI := Fintype.ofFinite (ObservedValue q)
  have h := compatible_observer_kernel_stable F (observedValue q)
    ((observationCompatible_image_iff F q).mpr hc)
    (by simpa only [Nat.card_eq_fintype_card] using hn) x y
  exact (orbitObserver_image_eq_iff F q (n + 1) x y).symm.trans
    (h.trans (orbitObserver_image_eq_iff F q n x y))

/-- The post-bound kernel equals the kernel at the attained-image bound for
every later stage, even when the ambient observation type is infinite. -/
theorem compatible_image_kernel_eq_at_card_pred
    {X : Type u} {Q : Type v} (F : X → X) (q : X → Q)
    [Finite (ObservedValue q)] (hc : ObservationCompatible F q)
    {n : Nat} (hn : Nat.card (ObservedValue q) - 1 ≤ n) (x y : X) :
    orbitObserver F q n x = orbitObserver F q n y ↔
      orbitObserver F q (Nat.card (ObservedValue q) - 1) x =
        orbitObserver F q (Nat.card (ObservedValue q) - 1) y := by
  induction n, hn using Nat.le_induction with
  | base => exact Iff.rfl
  | succ n hn ih =>
      exact (compatible_image_kernel_stable F q hc hn x y).trans ih

theorem compatible_license_loss_cutoff_le_image_card_pred
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V)
    {k : Nat} (hcut : ∀ n, Licensed (orbitObserver F q n) P ↔ n < k) :
    k ≤ Nat.card (ObservedValue q) - 1 := by
  letI := Fintype.ofFinite (ObservedValue q)
  have h := compatible_license_loss_cutoff_le_card_pred F (observedValue q)
    ((observationCompatible_image_iff F q).mpr hc) P
    (fun n => (licensed_orbitObserver_image_iff F q P n).trans (hcut n))
  simpa only [Nat.card_eq_fintype_card] using h

/-- The decisive time is the number of attained values minus one, not the ambient size. -/
theorem compatible_license_at_image_card_pred_iff_persistent
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) :
    Licensed (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P ↔
      ∀ n, Licensed (orbitObserver F q n) P := by
  constructor
  · intro hb
    rcases compatible_license_loss_dichotomy F q hc P with hall | ⟨k, hcut, _⟩
    · exact hall
    · have hk := compatible_license_loss_cutoff_le_image_card_pred F q hc P hcut
      have hlt := (hcut _).mp hb
      omega
  · exact fun h => h _

theorem compatible_license_stable_after_image_card
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V)
    {n : Nat} (hn : Nat.card (ObservedValue q) - 1 ≤ n) :
    Licensed (orbitObserver F q n) P ↔
      Licensed (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P := by
  constructor
  · exact licensed_of_coarsening_later (orbitObserver F q)
      ((orbitObserver_coarsens_iff F q).mp hc) P hn
  · intro h
    exact (compatible_license_at_image_card_pred_iff_persistent F q hc P).mp h n

end OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence
