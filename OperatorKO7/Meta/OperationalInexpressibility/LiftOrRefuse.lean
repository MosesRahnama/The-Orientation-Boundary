import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder

/-!
# Lift or refuse

An observer `q : X → Q` licenses a target `P : X → V` when `q x = q y` forces `P x = P y`. When it
does not, two repairs exist. A lift adds a side channel `s : X → C` and reads the target through
the joint observer `augmentObserver q s`. A refusal keeps a set `S` of states and answers only on
`S`. A mixed repair does both.

This module proves the following. Every repair of a collision separates the two colliding states
by the side channel or drops one of them. The sets a refusal can keep are exactly the sets on which
one decoder is correct; the maximal ones are the correctness sets of decoders whose value on every
fiber is attained in that fiber. The least refused weight is the Bayes risk of guessing the target
from the observer, and the least lift is the fiber multiplicity. A side channel with `k ≥ 1`
symbols repairs a retained set exactly when a menu of at most `k` target values per observation
covers it, so the least refused weight `repairFrontier μ q P k` of a `k`-symbol repair is a minimum
over menus. The frontier equals the total weight at `k = 0` and the Bayes risk at `k = 1`; it never
rises with `k`, its decrements never grow with `k`, and under a prior of full support it vanishes
exactly from the fiber multiplicity on. Neither repair is determined by the observer: every
collision gives two maximal refusals and two licensing lifts that disagree on it.

Relation: equality of observations; retained sets; side channels.
Trust: kernel only; classical choice builds decoders, codes, and exchanges.
Scope: arbitrary types for the collision, refusal, and uniqueness statements; finite carriers and
observation and target types, with rational weights, for the cost statements.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder

universe u v w z

/-! ## Retained sets, decoders, and the collision law -/

section General

variable {X : Type u} {Q : Type v} {V : Type w}

/-- The observer `q` licenses the target `P` on the retained set `S`: two retained states with
equal observations have equal targets. -/
def LicensedOn (S : Set X) (q : X → Q) (P : X → V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, q x = q y → P x = P y

/-- The states on which the decoder `d` reads the target correctly through the observer `q`. -/
def correctSet (q : X → Q) (P : X → V) (d : Q → V) : Set X :=
  {x | P x = d (q x)}

/-- A licensed retained set to which no state can be added without losing the license. -/
def MaximalLicensedOn (S : Set X) (q : X → Q) (P : X → V) : Prop :=
  LicensedOn S q P ∧ ∀ T : Set X, S ⊆ T → LicensedOn T q P → T = S

/-- On the fiber of every state, the decoder `d` takes a value that some state of the fiber has. -/
def FiberAttained (q : X → Q) (P : X → V) (d : Q → V) : Prop :=
  ∀ x, ∃ y, q y = q x ∧ P y = d (q x)

/-- Licensing on the whole carrier is the license criterion. -/
theorem licensedOn_univ_iff (q : X → Q) (P : X → V) :
    LicensedOn Set.univ q P ↔ Licensed q P := by
  constructor
  · intro h x y hxy
    exact h x (Set.mem_univ x) y (Set.mem_univ y) hxy
  · intro h x _ y _ hxy
    exact h x y hxy

/-- Dropping states keeps a license. -/
theorem LicensedOn.mono {S T : Set X} {q : X → Q} {P : X → V} (hST : S ⊆ T)
    (h : LicensedOn T q P) : LicensedOn S q P := by
  intro x hx y hy hxy
  exact h x (hST hx) y (hST hy) hxy

/-- The correctness set of any decoder is licensed. -/
theorem licensedOn_correctSet (q : X → Q) (P : X → V) (d : Q → V) :
    LicensedOn (correctSet q P d) q P := by
  intro x hx y hy hxy
  have hx' : P x = d (q x) := hx
  have hy' : P y = d (q y) := hy
  rw [hx', hy', hxy]

/-- **Collision law.** If `x` and `y` collide and the joint observer `augmentObserver q s`
licenses the target on the retained set `S`, then `S` drops `x`, or `S` drops `y`, or the side
channel separates them. -/
theorem collision_lifted_or_refused {C : Type z} {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) (s : X → C) {S : Set X}
    (h : LicensedOn S (augmentObserver q s) P) : x ∉ S ∨ y ∉ S ∨ s x ≠ s y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy, hs⟩ := hcon
  have hpair : augmentObserver q s x = augmentObserver q s y := by
    simp only [augmentObserver, hxy.1, hs]
  exact hxy.2 (h x hx y hy hpair)

/-- A lift that keeps every state separates every collision. -/
theorem collision_separated_by_lift {C : Type z} {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) (s : X → C)
    (h : Licensed (augmentObserver q s) P) : s x ≠ s y := by
  rcases collision_lifted_or_refused hxy s ((licensedOn_univ_iff _ P).2 h) with hx | hy | hs
  · exact absurd (Set.mem_univ x) hx
  · exact absurd (Set.mem_univ y) hy
  · exact hs

/-- A refusal without a side channel drops one state of every collision. -/
theorem collision_refused {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) {S : Set X} (h : LicensedOn S q P) :
    x ∉ S ∨ y ∉ S := by
  by_contra hcon
  push_neg at hcon
  exact hxy.2 (h x hcon.1 y hcon.2 hxy.1)

open Classical in
/-- The decoder that reads an observation off a retained state with that observation, and
otherwise off any state with that observation. -/
noncomputable def retainedDecoder [Nonempty V] (S : Set X) (q : X → Q) (P : X → V) (o : Q) : V :=
  if hS : ∃ x, x ∈ S ∧ q x = o then P (Classical.choose hS)
  else if hX : ∃ x, q x = o then P (Classical.choose hX) else Classical.arbitrary V

/-- On a licensed retained set, the retained decoder is correct at every retained state. -/
theorem retainedDecoder_of_mem [Nonempty V] {S : Set X} {q : X → Q} {P : X → V}
    (hS : LicensedOn S q P) {x : X} (hx : x ∈ S) : P x = retainedDecoder S q P (q x) := by
  have hex : ∃ z, z ∈ S ∧ q z = q x := ⟨x, hx, rfl⟩
  unfold retainedDecoder
  rw [dif_pos hex]
  obtain ⟨hzS, hzq⟩ := Classical.choose_spec hex
  exact hS x hx _ hzS hzq.symm

/-- The retained decoder takes, on every fiber, a value attained in that fiber. -/
theorem retainedDecoder_fiberAttained [Nonempty V] (S : Set X) (q : X → Q) (P : X → V) :
    FiberAttained q P (retainedDecoder S q P) := by
  intro x
  by_cases hex : ∃ z, z ∈ S ∧ q z = q x
  · refine ⟨Classical.choose hex, (Classical.choose_spec hex).2, ?_⟩
    unfold retainedDecoder
    rw [dif_pos hex]
  · have hX : ∃ z, q z = q x := ⟨x, rfl⟩
    refine ⟨Classical.choose hX, Classical.choose_spec hX, ?_⟩
    unfold retainedDecoder
    rw [dif_neg hex, dif_pos hX]

/-- **Refusal is decoding.** A retained set is licensed exactly when one decoder is correct on
all of it. -/
theorem licensedOn_iff_subset_correctSet [Nonempty V] (S : Set X) (q : X → Q) (P : X → V) :
    LicensedOn S q P ↔ ∃ d : Q → V, S ⊆ correctSet q P d := by
  constructor
  · intro h
    exact ⟨retainedDecoder S q P, fun x hx => retainedDecoder_of_mem h hx⟩
  · rintro ⟨d, hd⟩
    exact (licensedOn_correctSet q P d).mono hd

/-- **Maximal refusals.** The maximal licensed retained sets are exactly the correctness sets of
decoders whose value on every fiber is attained in that fiber. -/
theorem maximalLicensedOn_iff [Nonempty V] (S : Set X) (q : X → Q) (P : X → V) :
    MaximalLicensedOn S q P ↔ ∃ d : Q → V, FiberAttained q P d ∧ S = correctSet q P d := by
  constructor
  · rintro ⟨hS, hmax⟩
    refine ⟨retainedDecoder S q P, retainedDecoder_fiberAttained S q P, ?_⟩
    have hsub : S ⊆ correctSet q P (retainedDecoder S q P) :=
      fun x hx => retainedDecoder_of_mem hS hx
    exact (hmax _ hsub (licensedOn_correctSet q P _)).symm
  · rintro ⟨d, hatt, rfl⟩
    refine ⟨licensedOn_correctSet q P d, ?_⟩
    intro T hST hT
    refine Set.Subset.antisymm ?_ hST
    intro x hxT
    obtain ⟨y, hyq, hyP⟩ := hatt x
    have hyS : y ∈ correctSet q P d := by
      show P y = d (q y)
      rw [hyq]
      exact hyP
    have hxy : P x = P y := hT x hxT y (hST hyS) hyq.symm
    show P x = d (q x)
    rw [hxy, hyP]

/-- **Refusal is not determined by the observer.** A collision between `x` and `y` gives a maximal
refusal that keeps `x` and drops `y`, and a maximal refusal that keeps `y` and drops `x`. -/
theorem maximal_refusals_of_collision {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) :
    (∃ S : Set X, MaximalLicensedOn S q P ∧ x ∈ S ∧ y ∉ S) ∧
      ∃ T : Set X, MaximalLicensedOn T q P ∧ y ∈ T ∧ x ∉ T := by
  haveI : Nonempty V := ⟨P x⟩
  have keep : ∀ {a b : X}, q a = q b → P a ≠ P b →
      ∃ S : Set X, MaximalLicensedOn S q P ∧ a ∈ S ∧ b ∉ S := by
    intro a b hab hne
    have hlic : LicensedOn ({a} : Set X) q P := by
      intro z hz w hw _
      rw [Set.mem_singleton_iff.1 hz, Set.mem_singleton_iff.1 hw]
    have ha : P a = retainedDecoder {a} q P (q a) :=
      retainedDecoder_of_mem hlic (Set.mem_singleton a)
    refine ⟨correctSet q P (retainedDecoder {a} q P),
      (maximalLicensedOn_iff _ q P).2 ⟨_, retainedDecoder_fiberAttained {a} q P, rfl⟩, ha, ?_⟩
    intro hb
    have hb' : P b = retainedDecoder {a} q P (q b) := hb
    apply hne
    rw [ha, hb', hab]
  exact ⟨keep hxy.1 hxy.2, keep hxy.1.symm (Ne.symm hxy.2)⟩

/-- **Lift is not determined by the observer.** If `x` and `y` collide and the side channel `s`
licenses the target, then `s` followed by the swap of its symbols at `x` and `y` also licenses the
target and differs from `s` at `x`. -/
theorem lift_relabel_of_collision {C : Type z} [DecidableEq C] {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) {s : X → C}
    (hs : Licensed (augmentObserver q s) P) :
    Licensed (augmentObserver q (fun z => Equiv.swap (s x) (s y) (s z))) P ∧
      Equiv.swap (s x) (s y) (s x) ≠ s x := by
  constructor
  · intro a b hab
    apply hs a b
    have hq : q a = q b := congrArg Prod.fst hab
    have hsw : Equiv.swap (s x) (s y) (s a) = Equiv.swap (s x) (s y) (s b) :=
      congrArg Prod.snd hab
    simp only [augmentObserver, hq, (Equiv.swap (s x) (s y)).injective hsw]
  · rw [Equiv.swap_apply_left]
    exact (collision_separated_by_lift hxy s hs).symm

/-- A finite set of at most `k ≥ 1` values embeds into `Fin k`. -/
theorem exists_injOn_fin {k : ℕ} (hk : 0 < k) (A : Finset V) (hA : A.card ≤ k) :
    ∃ f : V → Fin k, Set.InjOn f (↑A : Set V) := by
  classical
  obtain ⟨e⟩ : Nonempty ({v // v ∈ A} ↪ Fin k) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hA)
  refine ⟨fun v => if hv : v ∈ A then e ⟨v, hv⟩ else ⟨0, hk⟩, ?_⟩
  intro a ha b hb hab
  have ha' : a ∈ A := Finset.mem_coe.1 ha
  have hb' : b ∈ A := Finset.mem_coe.1 hb
  simp only [dif_pos ha', dif_pos hb'] at hab
  exact congrArg Subtype.val (e.injective hab)

/-- **Mixed repair.** A side channel with `k ≥ 1` symbols licenses the target on the retained set
`S` exactly when a menu of at most `k` target values per observation contains the target of every
state of `S` at its observation. -/
theorem mixed_repair_iff {k : ℕ} (hk : 0 < k) (q : X → Q) (P : X → V) (S : Finset X) :
    (∃ s : X → Fin k, LicensedOn (↑S : Set X) (augmentObserver q s) P) ↔
      ∃ T : Q → Finset V, (∀ o, (T o).card ≤ k) ∧ ∀ x ∈ S, P x ∈ T (q x) := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun o => (S.filter (fun x => q x = o)).image P, ?_, ?_⟩
    · intro o
      have hcard : ((S.filter (fun x => q x = o)).image P).card ≤
          (Finset.univ : Finset (Fin k)).card := by
        apply Finset.card_le_card_of_injOn
          (fun v => if hv : ∃ x, x ∈ S ∧ q x = o ∧ P x = v then s (Classical.choose hv)
            else ⟨0, hk⟩)
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro v1 hv1 v2 hv2 heq
          obtain ⟨x1, hx1, hx1v⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv1)
          obtain ⟨x2, hx2, hx2v⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv2)
          have hv1' : ∃ x, x ∈ S ∧ q x = o ∧ P x = v1 :=
            ⟨x1, (Finset.mem_filter.1 hx1).1, (Finset.mem_filter.1 hx1).2, hx1v⟩
          have hv2' : ∃ x, x ∈ S ∧ q x = o ∧ P x = v2 :=
            ⟨x2, (Finset.mem_filter.1 hx2).1, (Finset.mem_filter.1 hx2).2, hx2v⟩
          simp only [dif_pos hv1', dif_pos hv2'] at heq
          obtain ⟨hc1S, hc1q, hc1P⟩ := Classical.choose_spec hv1'
          obtain ⟨hc2S, hc2q, hc2P⟩ := Classical.choose_spec hv2'
          have hpair : augmentObserver q s (Classical.choose hv1') =
              augmentObserver q s (Classical.choose hv2') := by
            simp only [augmentObserver, hc1q, hc2q, heq]
          have hP := hs _ (Finset.mem_coe.2 hc1S) _ (Finset.mem_coe.2 hc2S) hpair
          exact hc1P.symm.trans (hP.trans hc2P)
      simpa using hcard
    · intro x hx
      exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨T, hT, hST⟩
    choose f hf using fun o => exists_injOn_fin hk (T o) (hT o)
    refine ⟨fun x => f (q x) (P x), ?_⟩
    intro x hx y hy hxy
    have hq : q x = q y := congrArg Prod.fst hxy
    have hs : f (q x) (P x) = f (q y) (P y) := congrArg Prod.snd hxy
    have hPx : P x ∈ T (q x) := hST x (Finset.mem_coe.1 hx)
    have hPy : P y ∈ T (q x) := by
      rw [hq]
      exact hST y (Finset.mem_coe.1 hy)
    rw [← hq] at hs
    exact hf (q x) (Finset.mem_coe.2 hPx) (Finset.mem_coe.2 hPy) hs

/-- **Exchange.** Given a menu entry `A` with at most `k` values and a menu entry `B` with at most
`k + 2` values, two entries with at most `k + 1` values each keep, together, every value exactly as
often as `A` and `B` do. The proof moves one value of `B \ A` into `A`. -/
theorem exists_exchange [DecidableEq V] (A B : Finset V) (k : ℕ) (hA : A.card ≤ k)
    (hB : B.card ≤ k + 2) :
    ∃ A' B' : Finset V, A'.card ≤ k + 1 ∧ B'.card ≤ k + 1 ∧
      ∀ (v : V) (m : ℚ), ((if v ∈ A' then 0 else m) + if v ∈ B' then 0 else m) =
        (if v ∈ A then 0 else m) + if v ∈ B then 0 else m := by
  by_cases h : (B \ A).Nonempty
  · obtain ⟨b, hb⟩ := h
    obtain ⟨hbB, hbA⟩ := Finset.mem_sdiff.1 hb
    -- `insert b A` has at most `A.card + 1 ≤ k + 1` values; `B.erase b` has `B.card - 1 ≤ k + 1`.
    refine ⟨insert b A, B.erase b, (Finset.card_insert_le b A).trans (by omega), ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hbB]
      omega
    · intro v m
      by_cases hv : v = b
      · subst hv
        simp [hbB, hbA]
      · simp [hv]
  · have hsub : B ⊆ A :=
      Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 h)
    exact ⟨A, B, hA.trans (Nat.le_succ k),
      (Finset.card_le_card hsub).trans (hA.trans (Nat.le_succ k)), fun _ _ => rfl⟩

end General

/-! ## Costs on finite carriers -/

section Finite

variable {X : Type u} {Q : Type v} {V : Type w}

/-- The weight of the states that the retained set `S` refuses. -/
def refusedMass [Fintype X] [DecidableEq X] (μ : X → ℚ) (S : Finset X) : ℚ :=
  ∑ x, if x ∈ S then 0 else μ x

/-- The correctness set of a decoder, as a finite set. -/
def correctFinset [Fintype X] [DecidableEq V] (q : X → Q) (P : X → V) (d : Q → V) : Finset X :=
  Finset.univ.filter (fun x => P x = d (q x))

theorem coe_correctFinset [Fintype X] [DecidableEq V] (q : X → Q) (P : X → V) (d : Q → V) :
    (↑(correctFinset q P d) : Set X) = correctSet q P d := by
  ext x
  simp [correctFinset, correctSet]

theorem refusedMass_nonneg [Fintype X] [DecidableEq X] (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (S : Finset X) : 0 ≤ refusedMass μ S := by
  unfold refusedMass
  apply Finset.sum_nonneg
  intro x _
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx, hμ x]

/-- Keeping more states refuses less weight. -/
theorem refusedMass_antitone [Fintype X] [DecidableEq X] (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    {S T : Finset X} (hST : S ⊆ T) : refusedMass μ T ≤ refusedMass μ S := by
  unfold refusedMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hT : x ∈ T
  · by_cases hS : x ∈ S
    · simp [hT, hS]
    · simp [hT, hS, hμ x]
  · have hS : x ∉ S := fun h => hT (hST h)
    simp [hT, hS]

/-- A refusal without a side channel refuses, at every collision, at least the lighter of the two
colliding states. -/
theorem refusedMass_ge_min_of_collision [Fintype X] [DecidableEq X] (μ : X → ℚ)
    (hμ : ∀ x, 0 ≤ μ x) {q : X → Q} {P : X → V} {x y : X}
    (hxy : OperationallyInexpressibleAt q P x y) {S : Finset X}
    (hS : LicensedOn (↑S : Set X) q P) : min (μ x) (μ y) ≤ refusedMass μ S := by
  have hnonneg : ∀ z ∈ (Finset.univ : Finset X), 0 ≤ (if z ∈ S then 0 else μ z) := by
    intro z _
    by_cases hz : z ∈ S
    · simp [hz]
    · simp [hz, hμ z]
  have single : ∀ z, z ∉ S → μ z ≤ refusedMass μ S := by
    intro z hz
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ z)
    rw [if_neg hz] at hle
    exact hle
  rcases collision_refused hxy hS with hx | hy
  · exact (min_le_left _ _).trans (single x fun h => hx (Finset.mem_coe.2 h))
  · exact (min_le_right _ _).trans (single y fun h => hy (Finset.mem_coe.2 h))

/-- The weight refused by a decoder's correctness set is the decoder's 0-1 risk under the
deterministic observation model. -/
theorem refusedMass_correctFinset_eq_risk [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [DecidableEq V] (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x) (h1 : ∑ x, prior x = 1)
    (q : X → Q) (P : X → V) (d : Q → V) :
    refusedMass prior (correctFinset q P d) = risk (deterministicModel prior h0 h1 q) P d := by
  unfold risk
  rw [correctMass_deterministicModel prior h0 h1 q P d]
  unfold refusedMass correctFinset
  rw [← h1, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = d (q x)
  · simp [hx]
  · simp [hx]

/-- **Least refusal is the Bayes risk.** Some licensed retained set refuses exactly the Bayes risk
of guessing the target from the observer, and every licensed retained set refuses at least that
much. -/
theorem least_refusal_eq_bayesRisk [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [DecidableEq V] (EV : Enumeration V) (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x)
    (h1 : ∑ x, prior x = 1) (q : X → Q) (P : X → V) :
    (∃ S : Finset X, LicensedOn (↑S : Set X) q P ∧
        refusedMass prior S = bayesRisk EV (deterministicModel prior h0 h1 q) P) ∧
      ∀ S : Finset X, LicensedOn (↑S : Set X) q P →
        bayesRisk EV (deterministicModel prior h0 h1 q) P ≤ refusedMass prior S := by
  constructor
  · refine ⟨correctFinset q P (bayesDecoder EV (deterministicModel prior h0 h1 q) P), ?_, ?_⟩
    · rw [coe_correctFinset]
      exact licensedOn_correctSet q P _
    · exact refusedMass_correctFinset_eq_risk prior h0 h1 q P _
  · intro S hS
    have hX : Nonempty X := by
      by_contra hne
      haveI : IsEmpty X := not_nonempty_iff.mp hne
      have hzero : (∑ x, prior x) = 0 := by simp
      rw [h1] at hzero
      norm_num at hzero
    obtain ⟨x0⟩ := hX
    haveI : Nonempty V := ⟨P x0⟩
    obtain ⟨d, hd⟩ := (licensedOn_iff_subset_correctSet (↑S : Set X) q P).1 hS
    have hsub : S ⊆ correctFinset q P d := by
      intro x hx
      have hx' : x ∈ correctSet q P d := hd (Finset.mem_coe.2 hx)
      rw [← coe_correctFinset] at hx'
      exact Finset.mem_coe.1 hx'
    calc bayesRisk EV (deterministicModel prior h0 h1 q) P
        ≤ risk (deterministicModel prior h0 h1 q) P d := bayesRisk_le_risk EV _ P d
      _ = refusedMass prior (correctFinset q P d) :=
          (refusedMass_correctFinset_eq_risk prior h0 h1 q P d).symm
      _ ≤ refusedMass prior S := refusedMass_antitone prior h0 hsub

/-- **Least lift is the fiber multiplicity.** A side channel with `fiberMultiplicity q P` symbols
licenses the target, and every licensing side channel with `k` symbols has
`fiberMultiplicity q P ≤ k`. -/
theorem least_lift_eq_fiberMultiplicity [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) :
    (∃ s : X → Fin (fiberMultiplicity q P), Licensed (augmentObserver q s) P) ∧
      ∀ (k : ℕ) (s : X → Fin k), Licensed (augmentObserver q s) P →
        fiberMultiplicity q P ≤ k := by
  obtain ⟨r, hr⟩ := exists_optimal_side_channel q P
  refine ⟨⟨r, (licensed_iff_factorsThrough _ P).2 hr⟩, ?_⟩
  intro k s hs
  simpa using additional_channel_card_lower_bound q P s ((licensed_iff_factorsThrough _ P).1 hs)

/-- Under a constant observer the fiber multiplicity is the number of target values. -/
theorem fiberMultiplicity_const [Fintype X] [Nonempty X] [DecidableEq Q] [DecidableEq V]
    (c : Q) (P : X → V) : fiberMultiplicity (fun _ : X => c) P = (Finset.univ.image P).card := by
  unfold fiberMultiplicity fiberVerdicts
  rw [Finset.image_const Finset.univ_nonempty, Finset.sup_singleton]
  simp

/-- Menus that keep at most `k` target values at each observation. -/
def boundedMenus [Fintype Q] [DecidableEq Q] [Fintype V] (k : ℕ) : Finset (Q → Finset V) :=
  Finset.univ.filter (fun T => ∀ o, (T o).card ≤ k)

theorem empty_menu_mem_boundedMenus [Fintype Q] [DecidableEq Q] [Fintype V] (k : ℕ) :
    (fun _ => ∅ : Q → Finset V) ∈ boundedMenus k := by
  simp [boundedMenus]

/-- The weight refused by the menu `T`: every state whose target is not kept at its observation. -/
def menuRefusedMass [Fintype X] [DecidableEq V] (μ : X → ℚ) (q : X → Q) (P : X → V)
    (T : Q → Finset V) : ℚ :=
  ∑ x, if P x ∈ T (q x) then 0 else μ x

/-- The least weight refused by a menu of at most `k` target values per observation. For `k ≥ 1`
it is the least weight refused by a repair whose side channel has `k` symbols
(`repairFrontier_attained`, `repairFrontier_le_refusedMass`). -/
def repairFrontier [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]
    (μ : X → ℚ) (q : X → Q) (P : X → V) (k : ℕ) : ℚ :=
  (boundedMenus (Q := Q) (V := V) k).inf' ⟨_, empty_menu_mem_boundedMenus k⟩
    (menuRefusedMass μ q P)

theorem menuRefusedMass_eq_refusedMass [Fintype X] [DecidableEq X] [DecidableEq V] (μ : X → ℚ)
    (q : X → Q) (P : X → V) (T : Q → Finset V) :
    menuRefusedMass μ q P T = refusedMass μ (Finset.univ.filter (fun x => P x ∈ T (q x))) := by
  unfold menuRefusedMass refusedMass
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem menuRefusedMass_nonneg [Fintype X] [DecidableEq V] (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (q : X → Q) (P : X → V) (T : Q → Finset V) : 0 ≤ menuRefusedMass μ q P T := by
  unfold menuRefusedMass
  apply Finset.sum_nonneg
  intro x _
  by_cases hx : P x ∈ T (q x)
  · simp [hx]
  · simp [hx, hμ x]

/-- **The frontier is attained.** For `k ≥ 1`, some side channel with `k` symbols and some
retained set licensed by the joint observer refuse exactly the frontier weight. -/
theorem repairFrontier_attained [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q] [Fintype V]
    [DecidableEq V] (μ : X → ℚ) {k : ℕ} (hk : 0 < k) (q : X → Q) (P : X → V) :
    ∃ (s : X → Fin k) (S : Finset X), LicensedOn (↑S : Set X) (augmentObserver q s) P ∧
      refusedMass μ S = repairFrontier μ q P k := by
  obtain ⟨T, hTmem, hTeq⟩ := Finset.exists_mem_eq_inf'
    ⟨_, empty_menu_mem_boundedMenus (Q := Q) (V := V) k⟩ (menuRefusedMass μ q P)
  obtain ⟨s, hs⟩ := (mixed_repair_iff hk q P (Finset.univ.filter (fun x => P x ∈ T (q x)))).2
    ⟨T, (Finset.mem_filter.1 hTmem).2, fun x hx => (Finset.mem_filter.1 hx).2⟩
  refine ⟨s, Finset.univ.filter (fun x => P x ∈ T (q x)), hs, ?_⟩
  unfold repairFrontier
  rw [hTeq, menuRefusedMass_eq_refusedMass]

/-- **The frontier is a lower bound.** Every repair whose side channel has `k ≥ 1` symbols refuses
at least the frontier weight. -/
theorem repairFrontier_le_refusedMass [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype V] [DecidableEq V] (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) {k : ℕ} (hk : 0 < k)
    (q : X → Q) (P : X → V) (s : X → Fin k) (S : Finset X)
    (hS : LicensedOn (↑S : Set X) (augmentObserver q s) P) :
    repairFrontier μ q P k ≤ refusedMass μ S := by
  obtain ⟨T, hT, hST⟩ := (mixed_repair_iff hk q P S).1 ⟨s, hS⟩
  have hmem : T ∈ boundedMenus (Q := Q) (V := V) k :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩
  calc repairFrontier μ q P k ≤ menuRefusedMass μ q P T := by
        unfold repairFrontier
        exact Finset.inf'_le _ hmem
    _ = refusedMass μ (Finset.univ.filter (fun x => P x ∈ T (q x))) :=
        menuRefusedMass_eq_refusedMass μ q P T
    _ ≤ refusedMass μ S :=
        refusedMass_antitone μ hμ (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ x, hST x hx⟩)

/-- More side symbols never raise the frontier. -/
theorem repairFrontier_antitone [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V]
    [DecidableEq V] (μ : X → ℚ) (q : X → Q) (P : X → V) {k k' : ℕ} (hkk : k ≤ k') :
    repairFrontier μ q P k' ≤ repairFrontier μ q P k := by
  unfold repairFrontier
  apply Finset.le_inf'
  intro T hT
  have hT' : T ∈ boundedMenus (Q := Q) (V := V) k' := by
    have hcard := (Finset.mem_filter.1 hT).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun o => (hcard o).trans hkk⟩
  exact Finset.inf'_le _ hT'

theorem repairFrontier_nonneg [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]
    (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (q : X → Q) (P : X → V) (k : ℕ) :
    0 ≤ repairFrontier μ q P k := by
  unfold repairFrontier
  apply Finset.le_inf'
  intro T _
  exact menuRefusedMass_nonneg μ hμ q P T

/-- With no kept value, every state is refused. -/
theorem repairFrontier_zero [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]
    (μ : X → ℚ) (q : X → Q) (P : X → V) : repairFrontier μ q P 0 = ∑ x, μ x := by
  apply le_antisymm
  · calc repairFrontier μ q P 0 ≤ menuRefusedMass μ q P (fun _ => ∅) := by
          unfold repairFrontier
          exact Finset.inf'_le _ (empty_menu_mem_boundedMenus 0)
      _ = ∑ x, μ x := by simp [menuRefusedMass]
  · unfold repairFrontier
    apply Finset.le_inf'
    intro T hT
    have hempty : ∀ o, T o = ∅ := fun o =>
      Finset.card_eq_zero.1 (Nat.le_zero.1 ((Finset.mem_filter.1 hT).2 o))
    simp [menuRefusedMass, hempty]

/-- **Pure refusal.** With one side symbol the frontier is the Bayes risk. -/
theorem repairFrontier_one_eq_bayesRisk [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype V] [DecidableEq V] (EV : Enumeration V) (prior : X → ℚ) (h0 : ∀ x, 0 ≤ prior x)
    (h1 : ∑ x, prior x = 1) (q : X → Q) (P : X → V) :
    repairFrontier prior q P 1 = bayesRisk EV (deterministicModel prior h0 h1 q) P := by
  apply le_antisymm
  · have hmem : (fun o => ({bayesDecoder EV (deterministicModel prior h0 h1 q) P o} : Finset V)) ∈
        boundedMenus (Q := Q) (V := V) 1 := by
      simp [boundedMenus]
    calc repairFrontier prior q P 1
        ≤ menuRefusedMass prior q P
            (fun o => {bayesDecoder EV (deterministicModel prior h0 h1 q) P o}) := by
          unfold repairFrontier
          exact Finset.inf'_le _ hmem
      _ = refusedMass prior
            (correctFinset q P (bayesDecoder EV (deterministicModel prior h0 h1 q) P)) := by
          rw [menuRefusedMass_eq_refusedMass]
          congr 1
          ext x
          simp [correctFinset]
      _ = bayesRisk EV (deterministicModel prior h0 h1 q) P :=
          refusedMass_correctFinset_eq_risk prior h0 h1 q P _
  · unfold repairFrontier
    apply Finset.le_inf'
    intro T hT
    have hcard : ∀ o, (T o).card ≤ 1 := (Finset.mem_filter.1 hT).2
    rw [menuRefusedMass_eq_refusedMass]
    apply (least_refusal_eq_bayesRisk EV prior h0 h1 q P).2
    intro x hx y hy hxy
    have hx' : P x ∈ T (q x) := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' : P y ∈ T (q x) := by
      rw [hxy]
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    exact Finset.card_le_one.1 (hcard (q x)) _ hx' _ hy'

/-- **Pure lift.** From the fiber multiplicity on, the frontier is zero. -/
theorem repairFrontier_eq_zero_of_fiberMultiplicity_le [Fintype X] [Fintype Q] [DecidableEq Q]
    [Fintype V] [DecidableEq V] (μ : X → ℚ) (hμ : ∀ x, 0 ≤ μ x) (q : X → Q) (P : X → V)
    {k : ℕ} (hk : fiberMultiplicity q P ≤ k) : repairFrontier μ q P k = 0 := by
  refine le_antisymm ?_ (repairFrontier_nonneg μ hμ q P k)
  have hmem : (fun o => fiberVerdicts q P o) ∈ boundedMenus (Q := Q) (V := V) k :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, fun o => (fiberVerdicts_card_le q P o).trans hk⟩
  calc repairFrontier μ q P k ≤ menuRefusedMass μ q P (fun o => fiberVerdicts q P o) := by
        unfold repairFrontier
        exact Finset.inf'_le _ hmem
    _ = 0 := by
        unfold menuRefusedMass
        apply Finset.sum_eq_zero
        intro x _
        have hmemx : P x ∈ fiberVerdicts q P (q x) := mem_fiberVerdicts.2 ⟨x, rfl, rfl⟩
        simp [hmemx]

/-- Under a prior of full support, a zero frontier at `k` forces `fiberMultiplicity q P ≤ k`. -/
theorem fiberMultiplicity_le_of_repairFrontier_eq_zero [Fintype X] [Fintype Q] [DecidableEq Q]
    [Fintype V] [DecidableEq V] (μ : X → ℚ) (hμ : ∀ x, 0 < μ x) (q : X → Q) (P : X → V)
    {k : ℕ} (hzero : repairFrontier μ q P k = 0) : fiberMultiplicity q P ≤ k := by
  obtain ⟨T, hTmem, hTeq⟩ := Finset.exists_mem_eq_inf'
    ⟨_, empty_menu_mem_boundedMenus (Q := Q) (V := V) k⟩ (menuRefusedMass μ q P)
  have hcard : ∀ o, (T o).card ≤ k := (Finset.mem_filter.1 hTmem).2
  have hsum : menuRefusedMass μ q P T = 0 := by
    rw [← hTeq]
    exact hzero
  unfold menuRefusedMass at hsum
  have hnonneg : ∀ y ∈ (Finset.univ : Finset X), 0 ≤ (if P y ∈ T (q y) then 0 else μ y) := by
    intro y _
    by_cases hy : P y ∈ T (q y)
    · simp [hy]
    · simp [hy, (hμ y).le]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum
  have hkept : ∀ x, P x ∈ T (q x) := by
    intro x
    by_contra hx
    have hx0 := hterms x (Finset.mem_univ x)
    rw [if_neg hx] at hx0
    exact (hμ x).ne' hx0
  unfold fiberMultiplicity
  apply Finset.sup_le
  intro o _
  calc (fiberVerdicts q P o).card ≤ (T o).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨x, hxo, hxv⟩ := mem_fiberVerdicts.1 hv
        rw [← hxv, ← hxo]
        exact hkept x
    _ ≤ k := hcard o

/-- **Diminishing returns.** Each extra side symbol lowers the frontier by no more than the
previous symbol did. -/
theorem repairFrontier_convex [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype V] [DecidableEq V]
    (μ : X → ℚ) (q : X → Q) (P : X → V) (k : ℕ) :
    repairFrontier μ q P (k + 1) + repairFrontier μ q P (k + 1) ≤
      repairFrontier μ q P k + repairFrontier μ q P (k + 2) := by
  obtain ⟨A, hAmem, hAeq⟩ := Finset.exists_mem_eq_inf'
    ⟨_, empty_menu_mem_boundedMenus (Q := Q) (V := V) k⟩ (menuRefusedMass μ q P)
  obtain ⟨B, hBmem, hBeq⟩ := Finset.exists_mem_eq_inf'
    ⟨_, empty_menu_mem_boundedMenus (Q := Q) (V := V) (k + 2)⟩ (menuRefusedMass μ q P)
  choose A' B' hA' hB' hAB using fun o =>
    exists_exchange (A o) (B o) k ((Finset.mem_filter.1 hAmem).2 o) ((Finset.mem_filter.1 hBmem).2 o)
  have hA'mem : A' ∈ boundedMenus (Q := Q) (V := V) (k + 1) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hA'⟩
  have hB'mem : B' ∈ boundedMenus (Q := Q) (V := V) (k + 1) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hB'⟩
  have hsum : menuRefusedMass μ q P A' + menuRefusedMass μ q P B' =
      menuRefusedMass μ q P A + menuRefusedMass μ q P B := by
    unfold menuRefusedMass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hAB (q x) (P x) (μ x)
  have hle1 : repairFrontier μ q P (k + 1) ≤ menuRefusedMass μ q P A' := by
    unfold repairFrontier
    exact Finset.inf'_le _ hA'mem
  have hle2 : repairFrontier μ q P (k + 1) ≤ menuRefusedMass μ q P B' := by
    unfold repairFrontier
    exact Finset.inf'_le _ hB'mem
  calc repairFrontier μ q P (k + 1) + repairFrontier μ q P (k + 1)
      ≤ menuRefusedMass μ q P A' + menuRefusedMass μ q P B' := add_le_add hle1 hle2
    _ = menuRefusedMass μ q P A + menuRefusedMass μ q P B := hsum
    _ = repairFrontier μ q P k + repairFrontier μ q P (k + 2) := by
        unfold repairFrontier
        rw [hAeq, hBeq]

/-- **Lift or refuse.** For finite carrier, observation, and target types and a prior of full
support:
* the observer licenses the target exactly when the fiber multiplicity is at most one, and exactly
  when the Bayes risk is zero;
* the frontier is the total weight with no kept value and the Bayes risk with one side symbol;
* the frontier is zero exactly from the fiber multiplicity on;
* the frontier never rises with one more side symbol, and its decrements never grow. -/
theorem lift_or_refuse [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q] [Fintype V]
    [DecidableEq V] (EV : Enumeration V) (prior : X → ℚ) (hpos : ∀ x, 0 < prior x)
    (h1 : ∑ x, prior x = 1) (q : X → Q) (P : X → V) :
    (Licensed q P ↔ fiberMultiplicity q P ≤ 1) ∧
    (Licensed q P ↔
      bayesRisk EV (deterministicModel prior (fun x => (hpos x).le) h1 q) P = 0) ∧
    repairFrontier prior q P 0 = 1 ∧
    repairFrontier prior q P 1 =
      bayesRisk EV (deterministicModel prior (fun x => (hpos x).le) h1 q) P ∧
    (∀ k, repairFrontier prior q P k = 0 ↔ fiberMultiplicity q P ≤ k) ∧
    (∀ k, repairFrontier prior q P (k + 1) ≤ repairFrontier prior q P k) ∧
    (∀ k, repairFrontier prior q P (k + 1) + repairFrontier prior q P (k + 1) ≤
      repairFrontier prior q P k + repairFrontier prior q P (k + 2)) := by
  refine ⟨?_, ?_, ?_, repairFrontier_one_eq_bayesRisk EV prior _ h1 q P, ?_,
    fun k => repairFrontier_antitone prior q P (Nat.le_succ k),
    fun k => repairFrontier_convex prior q P k⟩
  · rw [licensed_iff_factorsThrough, fiberMultiplicity_le_one_iff]
  · rw [bayesRisk_eq_zero_iff_licensedOnJointSupport,
      deterministic_fullSupport_licensed_iff_fullCarrier prior _ h1 hpos q P]
    exact Iff.rfl
  · rw [repairFrontier_zero, h1]
  · intro k
    exact ⟨fiberMultiplicity_le_of_repairFrontier_eq_zero prior hpos q P,
      repairFrontier_eq_zero_of_fiberMultiplicity_le prior (fun x => (hpos x).le) q P⟩

end Finite

/-! ## The smallest collision -/

/-- **Two voids.** Two states that no observation separates and that the target tells apart: the
lift needs two symbols, the maximal refusals keep one state each, and under the uniform prior the
frontier is one half with one side symbol and zero with two. -/
theorem twoVoids_lift_or_refuse :
    OperationallyInexpressibleAt (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) 0 1 ∧
    fiberMultiplicity (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) = 2 ∧
    (∀ S : Set (Fin 2), MaximalLicensedOn S (fun _ => ()) (fun x : Fin 2 => x) ↔
      S = {0} ∨ S = {1}) ∧
    repairFrontier (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ => ()) (fun x : Fin 2 => x) 1 = 1 / 2 ∧
    repairFrontier (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ => ()) (fun x : Fin 2 => x) 2 = 0 := by
  have hmult : fiberMultiplicity (fun _ : Fin 2 => ()) (fun x : Fin 2 => x) = 2 := by decide
  refine ⟨⟨rfl, by decide⟩, hmult, ?_, ?_, ?_⟩
  · intro S
    rw [maximalLicensedOn_iff]
    constructor
    · rintro ⟨d, -, rfl⟩
      have hcases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hcases (d ()) with hd | hd
      · left
        ext x
        simp [correctSet, hd]
      · right
        ext x
        simp [correctSet, hd]
    · rintro (rfl | rfl)
      · refine ⟨fun _ => 0, fun _ => ⟨0, rfl, rfl⟩, ?_⟩
        ext x
        simp [correctSet]
      · refine ⟨fun _ => 1, fun _ => ⟨1, rfl, rfl⟩, ?_⟩
        ext x
        simp [correctSet]
  · apply le_antisymm
    · have hmem : (fun _ => ({0} : Finset (Fin 2))) ∈ boundedMenus (Q := Unit) (V := Fin 2) 1 := by
        simp [boundedMenus]
      calc repairFrontier (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ => ()) (fun x : Fin 2 => x) 1
          ≤ menuRefusedMass (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ => ()) (fun x : Fin 2 => x)
              (fun _ => {0}) := by
            unfold repairFrontier
            exact Finset.inf'_le _ hmem
        _ = 1 / 2 := by
            simp [menuRefusedMass, Fin.sum_univ_two]
    · unfold repairFrontier
      apply Finset.le_inf'
      intro T hT
      have hcard : (T ()).card ≤ 1 := (Finset.mem_filter.1 hT).2 ()
      unfold menuRefusedMass
      rw [Fin.sum_univ_two]
      by_cases h0 : (0 : Fin 2) ∈ T ()
      · by_cases h1 : (1 : Fin 2) ∈ T ()
        · exact absurd (Finset.card_le_one.1 hcard _ h0 _ h1) (by decide)
        · norm_num [h0, h1]
      · by_cases h1 : (1 : Fin 2) ∈ T ()
        · norm_num [h0, h1]
        · norm_num [h0, h1]
  · exact repairFrontier_eq_zero_of_fiberMultiplicity_le _ (fun _ => by norm_num) _ _ hmult.le

end OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
