import OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel
import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery

/-!
# Exact capacity of side channels for set-valued tasks

A set-valued certificate task assigns to each source state the set of certificates admissible
there. A side channel with `k` symbols, read together with the observer, recovers an admissible
certificate at every state exactly when, in every observer fiber, the states can be colored with
`k` colors so that each nonempty color class has one certificate admissible at all of its states.
Colorings of different fibers are chosen independently, so the least number of symbols is the
maximum over realized fibers of the fiber chromatic number, the least number of colors of such a
coloring of that fiber. This is the chromatic number of the hypergraph whose hyperedges are the
fiber subsets without a common certificate. When some state has no admissible certificate, no
side channel of any size exists.

For function-valued targets (singleton admissibility) the capacity is the fiber multiplicity, the
function-valued case given by the chromatic number of Witsenhausen's confusability graph. An
exhaustive search over explicit enumerations computes the capacity: it returns the least alphabet
size with a successful coloring, and `none` exactly when some state has no certificate. On the
three-state task in which every pair of states shares a certificate and the three states together
do not, the capacity is two.

Relation: equality on observer fibers.
Property: exact minimum side-channel size; executable optimum.
Trust: kernel only; the fiber chromatic numbers use classical choice.
Scope: finite source for existence and optimality; explicit enumerations of source states and
certificates with decidable equality and decidable admissibility for the search.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RelationalSideCapacity

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery
open OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery

universe u v w

variable {X : Type u} {Q : Type v} {W : Type w}

/-! ## Fiber colorings -/

/-- The fiber over `u` admits a `k`-coloring in which every nonempty color class has a common
admissible certificate. -/
def FiberColorable (q : X → Q) (admissible : X → W → Prop) (u : Q) (k : ℕ) : Prop :=
  ∃ c : X → Fin k, ∀ j : Fin k, (∃ x, q x = u ∧ c x = j) →
    ∃ witness, ∀ x, q x = u → c x = j → admissible x witness

/-- **Gluing.** A side channel with `k` symbols exists exactly when every fiber is
`k`-colorable. -/
theorem exists_sideChannel_iff_forall_fiberColorable (q : X → Q) (admissible : X → W → Prop)
    (k : ℕ) :
    (∃ c : X → Fin k, PartialRelationalSideChannel q admissible c) ↔
      ∀ u, FiberColorable q admissible u k := by
  constructor
  · rintro ⟨c, hc⟩ u
    have hcells := (partialRelationalSideChannel_iff_cellwiseCompatible q admissible c).1 hc
    refine ⟨c, fun j ⟨x, hxu, hxj⟩ => ?_⟩
    obtain ⟨w, hw⟩ := hcells u j ⟨x, hxu, hxj⟩
    exact ⟨w, fun y hyu hyj => hw y ⟨hyu, hyj⟩⟩
  · intro h
    have h' : ∀ u, ∃ c : X → Fin k, ∀ j : Fin k, (∃ x, q x = u ∧ c x = j) →
        ∃ witness, ∀ x, q x = u → c x = j → admissible x witness := h
    choose c hc using h'
    refine ⟨fun x => c (q x) x, ?_⟩
    rw [partialRelationalSideChannel_iff_cellwiseCompatible]
    rintro u j ⟨x, hxu, hxj⟩
    have hxj' : c u x = j := by
      rw [← hxu]
      exact hxj
    obtain ⟨w, hw⟩ := hc u j ⟨x, hxu, hxj'⟩
    refine ⟨w, fun y hy => hw y hy.1 ?_⟩
    have hyj : c (q y) y = j := hy.2
    rw [hy.1] at hyj
    exact hyj

/-- More colors never hurt. -/
theorem FiberColorable.mono {q : X → Q} {admissible : X → W → Prop} {u : Q} {k k' : ℕ}
    (hk : k ≤ k') (h : FiberColorable q admissible u k) : FiberColorable q admissible u k' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun x => Fin.castLE hk (c x), fun j ⟨x, hxu, hxj⟩ => ?_⟩
  obtain ⟨w, hw⟩ := hc (c x) ⟨x, hxu, rfl⟩
  exact ⟨w, fun y hyu hyj => hw y hyu (Fin.castLE_injective hk (hyj.trans hxj.symm))⟩

/-- A state with no admissible certificate blocks every coloring of its fiber. -/
theorem not_fiberColorable_of_no_certificate {q : X → Q} {admissible : X → W → Prop} {x : X}
    (hx : ∀ w, ¬ admissible x w) (k : ℕ) : ¬ FiberColorable q admissible (q x) k := by
  rintro ⟨c, hc⟩
  obtain ⟨w, hw⟩ := hc (c x) ⟨x, rfl, rfl⟩
  exact hx w (hw x rfl rfl)

/-- A state with no admissible certificate blocks every side channel. -/
theorem no_sideChannel_of_no_certificate {q : X → Q} {admissible : X → W → Prop} {x : X}
    (hx : ∀ w, ¬ admissible x w) (k : ℕ) :
    ¬ ∃ c : X → Fin k, PartialRelationalSideChannel q admissible c := by
  rw [exists_sideChannel_iff_forall_fiberColorable]
  exact fun h => not_fiberColorable_of_no_certificate hx k (h (q x))

/-- For singleton admissibility, a side channel recovers the certificate exactly when the joint
observation determines the target. -/
theorem singleton_sideChannel_iff_factorsThrough (q : X → Q) (P : X → W) {k : ℕ}
    (c : X → Fin k) :
    PartialRelationalSideChannel q (SingletonAdmissible P) c ↔
      FactorsThrough (fun x => (q x, c x)) P := by
  constructor
  · rintro ⟨decode, hdecode⟩ x y hxy
    obtain ⟨wx, hx, hwx⟩ := hdecode x
    obtain ⟨wy, hy, hwy⟩ := hdecode y
    have hq : q x = q y := congrArg Prod.fst hxy
    have hc : c x = c y := congrArg Prod.snd hxy
    rw [hq, hc, hy] at hx
    have hw : wy = wx := Option.some.inj hx
    unfold SingletonAdmissible at hwx hwy
    rw [← hwx, ← hwy, hw]
  · intro h
    rw [partialRelationalSideChannel_iff_cellwiseCompatible]
    rintro u j ⟨x, hxu, hxj⟩
    refine ⟨P x, fun y hy => ?_⟩
    unfold SingletonAdmissible
    exact (h (Prod.ext (hy.1.trans hxu.symm) (hy.2.trans hxj.symm))).symm

/-! ## The capacity -/

section Finite

variable [Fintype X]

/-- When every state has an admissible certificate, one color per state suffices. -/
theorem fiberColorable_card {q : X → Q} {admissible : X → W → Prop}
    (hadm : ∀ x, ∃ w, admissible x w) (u : Q) :
    FiberColorable q admissible u (Fintype.card X) := by
  classical
  refine ⟨Fintype.equivFin X, fun j ⟨x, _, hxj⟩ => ?_⟩
  obtain ⟨w, hw⟩ := hadm x
  refine ⟨w, fun y _ hyj => ?_⟩
  have hyx : y = x := (Fintype.equivFin X).injective (hyj.trans hxj.symm)
  rw [hyx]
  exact hw

open Classical in
/-- The fiber chromatic number: the least number of colors of an admissible coloring of the fiber
over `u`. -/
noncomputable def fiberChromatic (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) (u : Q) : ℕ :=
  Nat.find (⟨Fintype.card X, fiberColorable_card hadm u⟩ : ∃ k, FiberColorable q admissible u k)

theorem fiberChromatic_spec (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) (u : Q) :
    FiberColorable q admissible u (fiberChromatic q admissible hadm u) := by
  classical
  unfold fiberChromatic
  exact Nat.find_spec _

theorem fiberChromatic_le (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) {u : Q} {k : ℕ} (h : FiberColorable q admissible u k) :
    fiberChromatic q admissible hadm u ≤ k := by
  classical
  unfold fiberChromatic
  exact Nat.find_min' _ h

variable [DecidableEq Q]

/-- The exact side-channel capacity: the maximum fiber chromatic number over realized fibers. -/
noncomputable def relationalSideCapacity (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) : ℕ :=
  (Finset.univ.image q).sup fun u => fiberChromatic q admissible hadm u

/-- **Exact capacity for set-valued tasks.** A side channel with `k` symbols exists exactly when
`k` is at least the maximum fiber chromatic number. -/
theorem exists_sideChannel_iff_capacity_le (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) (k : ℕ) :
    (∃ c : X → Fin k, PartialRelationalSideChannel q admissible c) ↔
      relationalSideCapacity q admissible hadm ≤ k := by
  rw [exists_sideChannel_iff_forall_fiberColorable]
  constructor
  · intro h
    apply Finset.sup_le
    intro u _
    exact fiberChromatic_le q admissible hadm (h u)
  · intro hk u
    by_cases hu : u ∈ Finset.univ.image q
    · have hle : fiberChromatic q admissible hadm u ≤ k :=
        le_trans (Finset.le_sup (f := fun u => fiberChromatic q admissible hadm u) hu) hk
      exact (fiberChromatic_spec q admissible hadm u).mono hle
    · rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
      · exact ⟨fun x => isEmptyElim x, fun _ ⟨x, _⟩ => isEmptyElim x⟩
      · have hmem : q x₀ ∈ Finset.univ.image q :=
          Finset.mem_image.2 ⟨x₀, Finset.mem_univ _, rfl⟩
        have hpos : 0 < fiberChromatic q admissible hadm (q x₀) := by
          rw [Nat.pos_iff_ne_zero]
          intro h0
          obtain ⟨c, _⟩ := fiberChromatic_spec q admissible hadm (q x₀)
          have hlt := (c x₀).isLt
          omega
        have hk1 : 0 < k := lt_of_lt_of_le hpos
          (le_trans (Finset.le_sup (f := fun u => fiberChromatic q admissible hadm u) hmem) hk)
        refine ⟨fun _ => ⟨0, hk1⟩, fun _ ⟨x, hxu, _⟩ => ?_⟩
        exact absurd (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hxu⟩) hu

/-- The capacity is attained, and no smaller alphabet suffices. -/
theorem relationalSideCapacity_exact (q : X → Q) (admissible : X → W → Prop)
    (hadm : ∀ x, ∃ w, admissible x w) :
    (∃ c : X → Fin (relationalSideCapacity q admissible hadm),
        PartialRelationalSideChannel q admissible c) ∧
      ∀ k < relationalSideCapacity q admissible hadm,
        ¬ ∃ c : X → Fin k, PartialRelationalSideChannel q admissible c := by
  refine ⟨(exists_sideChannel_iff_capacity_le q admissible hadm _).2 le_rfl, fun k hk h => ?_⟩
  exact absurd ((exists_sideChannel_iff_capacity_le q admissible hadm k).1 h) (not_le.2 hk)

/-- **Singleton specialization.** For a function-valued target, the exact side-channel capacity is
the fiber multiplicity. -/
theorem relationalSideCapacity_singleton [DecidableEq W] (q : X → Q) (P : X → W) :
    relationalSideCapacity q (SingletonAdmissible P) (fun x => ⟨P x, rfl⟩) =
      fiberMultiplicity q P := by
  have key : ∀ k, relationalSideCapacity q (SingletonAdmissible P) (fun x => ⟨P x, rfl⟩) ≤ k ↔
      fiberMultiplicity q P ≤ k := by
    intro k
    rw [← exists_sideChannel_iff_capacity_le]
    constructor
    · rintro ⟨c, hc⟩
      have hf : FactorsThrough (fun x => (q x, c x)) P := fun {x y} hxy =>
        (singleton_sideChannel_iff_factorsThrough q P c).1 hc hxy
      simpa using additional_channel_card_lower_bound q P c hf
    · intro hk
      obtain ⟨r, hr⟩ := exists_optimal_side_channel q P
      refine ⟨fun x => Fin.castLE hk (r x), ?_⟩
      rw [singleton_sideChannel_iff_factorsThrough]
      intro x y hxy
      have hq : q x = q y := congrArg Prod.fst hxy
      have hr' : r x = r y := Fin.castLE_injective hk (congrArg Prod.snd hxy)
      exact hr (Prod.ext hq hr')
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

end Finite

/-! ## Executable exhaustive search -/

/-- The explicit enumeration of `Fin k`. -/
def finEnumeration (k : ℕ) : Enumeration (Fin k) :=
  ⟨List.finRange k, List.nodup_finRange k, List.mem_finRange⟩

/-- Executable test that every color cell of `c` has a common certificate listed in `EW`. -/
def cellwiseCompatibleB [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] {k : ℕ} (c : X → Fin k) : Bool :=
  decide (∀ x ∈ EX.items, ∃ w ∈ EW.items, ∀ y ∈ EX.items,
    q y = q x → c y = c x → admissible y w)

/-- The executable cell test decides cellwise compatibility. -/
theorem cellwiseCompatibleB_eq_true_iff [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] {k : ℕ} (c : X → Fin k) :
    cellwiseCompatibleB EX EW q admissible c = true ↔ CellwiseCompatible q admissible c := by
  unfold cellwiseCompatibleB
  rw [decide_eq_true_iff]
  constructor
  · rintro h u j ⟨x, hxu, hxj⟩
    obtain ⟨w, _, hw⟩ := h x (EX.complete x)
    exact ⟨w, fun y hy => hw y (EX.complete y) (hy.1.trans hxu.symm) (hy.2.trans hxj.symm)⟩
  · intro h x _
    obtain ⟨w, hw⟩ := h (q x) (c x) ⟨x, rfl, rfl⟩
    exact ⟨w, EW.complete w, fun y _ hq hc => hw y ⟨hq, hc⟩⟩

/-- Executable test: some `k`-coloring has common certificates on all of its cells. The
candidate colorings are the exhaustive table enumeration `sideEncoderCandidates`. -/
def colorableB [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] (k : ℕ) : Bool :=
  (sideEncoderCandidates EX (finEnumeration k)).any fun c =>
    cellwiseCompatibleB EX EW q admissible c

/-- The executable coloring test decides existence of a `k`-symbol side channel. -/
theorem colorableB_eq_true_iff [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] (k : ℕ) :
    colorableB EX EW q admissible k = true ↔
      ∃ c : X → Fin k, PartialRelationalSideChannel q admissible c := by
  unfold colorableB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, (partialRelationalSideChannel_iff_cellwiseCompatible q admissible c).2
      ((cellwiseCompatibleB_eq_true_iff EX EW q admissible c).1 hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, sideEncoderCandidates_complete EX (finEnumeration k) c,
      (cellwiseCompatibleB_eq_true_iff EX EW q admissible c).2
        ((partialRelationalSideChannel_iff_cellwiseCompatible q admissible c).1 hc)⟩

/-- When every state has a certificate, one color per enumerated state suffices. -/
theorem exists_sideChannel_of_certificates [DecidableEq X] (EX : Enumeration X) {q : X → Q}
    {admissible : X → W → Prop} (hadm : ∀ x, ∃ w, admissible x w) :
    ∃ c : X → Fin EX.items.length, PartialRelationalSideChannel q admissible c := by
  refine ⟨fun x => ⟨EX.items.idxOf x, List.idxOf_lt_length_iff.2 (EX.complete x)⟩, ?_⟩
  rw [partialRelationalSideChannel_iff_cellwiseCompatible]
  rintro u j ⟨x, _, hxj⟩
  obtain ⟨w, hw⟩ := hadm x
  refine ⟨w, fun y hy => ?_⟩
  have hidx : EX.items.idxOf y = EX.items.idxOf x := congrArg Fin.val (hy.2.trans hxj.symm)
  rw [(List.idxOf_inj (EX.complete y) (EX.complete x)).1 hidx]
  exact hw

/-- **Executable exhaustive search for the least side alphabet.** The search tests alphabet sizes
up to the number of enumerated states and returns the least size with a successful coloring. -/
def relationalSideCapacity? [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] : Option ℕ :=
  if h : colorableB EX EW q admissible EX.items.length = true then
    some (Nat.find (p := fun k => colorableB EX EW q admissible k = true) ⟨EX.items.length, h⟩)
  else none

/-- The search returns the exact capacity whenever every state has a certificate. -/
theorem relationalSideCapacity?_eq_some [Fintype X] [DecidableEq X] [DecidableEq Q]
    [DecidableEq W] (EX : Enumeration X) (EW : Enumeration W) (q : X → Q)
    (admissible : X → W → Prop) [∀ x w, Decidable (admissible x w)]
    (hadm : ∀ x, ∃ w, admissible x w) :
    relationalSideCapacity? EX EW q admissible =
      some (relationalSideCapacity q admissible hadm) := by
  have hlen : colorableB EX EW q admissible EX.items.length = true :=
    (colorableB_eq_true_iff EX EW q admissible _).2 (exists_sideChannel_of_certificates EX hadm)
  unfold relationalSideCapacity?
  rw [dif_pos hlen, Option.some.injEq, Nat.find_eq_iff]
  constructor
  · exact (colorableB_eq_true_iff EX EW q admissible _).2
      ((exists_sideChannel_iff_capacity_le q admissible hadm _).2 le_rfl)
  · intro n hn hcol
    have hle := (exists_sideChannel_iff_capacity_le q admissible hadm n).1
      ((colorableB_eq_true_iff EX EW q admissible n).1 hcol)
    omega

/-- The search returns `none` exactly when some state has no admissible certificate. -/
theorem relationalSideCapacity?_eq_none_iff [DecidableEq X] [DecidableEq Q] [DecidableEq W]
    (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (admissible : X → W → Prop)
    [∀ x w, Decidable (admissible x w)] :
    relationalSideCapacity? EX EW q admissible = none ↔ ∃ x, ∀ w, ¬ admissible x w := by
  unfold relationalSideCapacity?
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    have hlen := (colorableB_eq_true_iff EX EW q admissible _).2
      (exists_sideChannel_of_certificates EX hall)
    rw [dif_pos hlen] at h
    cases h
  · rintro ⟨x, hx⟩
    have hlen : ¬ colorableB EX EW q admissible EX.items.length = true := fun h =>
      no_sideChannel_of_no_certificate hx _ ((colorableB_eq_true_iff EX EW q admissible _).1 h)
    rw [dif_neg hlen]

/-- Singleton admissibility is decidable from decidable equality of certificates. -/
instance singletonAdmissible_decidable [DecidableEq W] (P : X → W) (x : X) (w : W) :
    Decidable (SingletonAdmissible P x w) :=
  inferInstanceAs (Decidable (w = P x))

/-- For a function-valued target the search returns the fiber multiplicity. -/
theorem relationalSideCapacity?_singleton [Fintype X] [DecidableEq X] [DecidableEq Q]
    [DecidableEq W] (EX : Enumeration X) (EW : Enumeration W) (q : X → Q) (P : X → W) :
    relationalSideCapacity? EX EW q (SingletonAdmissible P) = some (fiberMultiplicity q P) := by
  rw [relationalSideCapacity?_eq_some EX EW q (SingletonAdmissible P) (fun x => ⟨P x, rfl⟩),
    relationalSideCapacity_singleton]

/-! ## The three-state fixture -/

/-- Every three-state position has an admissible certificate. -/
theorem threeWay_certificates : ∀ x : Fin 3, ∃ w, threeWayAdmissible x w :=
  fun x => ⟨thirdWitness x x, thirdWitness_ne_left x x⟩

/-- The two-color encoder of the fixture with values in `Fin 2`. -/
def threeWayFinTwoColor (x : Fin 3) : Fin 2 :=
  if threeWayTwoColor x then 1 else 0

/-- Two colors succeed on the fixture. -/
theorem threeWay_finTwo_succeeds :
    PartialRelationalSideChannel threeWayObserver threeWayAdmissible threeWayFinTwoColor := by
  refine ⟨fun _ c => if c = 0 then some 2 else some 0, ?_⟩
  intro x
  fin_cases x
  · exact ⟨2, rfl, by simp [threeWayAdmissible]⟩
  · exact ⟨2, rfl, by simp [threeWayAdmissible]⟩
  · exact ⟨0, rfl, by simp [threeWayAdmissible]⟩

/-- One color fails on the fixture. -/
theorem threeWay_one_color_fails :
    ¬ ∃ c : Fin 3 → Fin 1, PartialRelationalSideChannel threeWayObserver threeWayAdmissible c := by
  rintro ⟨c, hc⟩
  have hcells := (partialRelationalSideChannel_iff_cellwiseCompatible _ _ c).1 hc
  obtain ⟨w, hw⟩ := hcells () 0 ⟨0, rfl, Subsingleton.elim _ _⟩
  exact hw w ⟨rfl, Subsingleton.elim _ _⟩ rfl

/-- **The three-state task has capacity two.** Every pair of states shares a certificate, and the
three states together do not. -/
theorem threeWay_capacity_eq_two :
    relationalSideCapacity threeWayObserver threeWayAdmissible threeWay_certificates = 2 := by
  apply le_antisymm
  · exact (exists_sideChannel_iff_capacity_le _ _ threeWay_certificates 2).1
      ⟨threeWayFinTwoColor, threeWay_finTwo_succeeds⟩
  · by_contra hlt
    have h1 : relationalSideCapacity threeWayObserver threeWayAdmissible
        threeWay_certificates ≤ 1 := by
      omega
    exact threeWay_one_color_fails
      ((exists_sideChannel_iff_capacity_le _ _ threeWay_certificates 1).2 h1)

/-- Admissibility on the fixture is decidable. -/
instance threeWayAdmissible_decidable (x w : Fin 3) : Decidable (threeWayAdmissible x w) :=
  inferInstanceAs (Decidable (w ≠ x))

/-- The executable search returns two on the fixture. -/
theorem threeWay_relationalSideCapacity? :
    relationalSideCapacity? threeValueEnumeration threeValueEnumeration threeWayObserver
      threeWayAdmissible = some 2 := by
  rw [relationalSideCapacity?_eq_some threeValueEnumeration threeValueEnumeration threeWayObserver
    threeWayAdmissible threeWay_certificates, threeWay_capacity_eq_two]

/-- **Pairwise compatibility with a bad triple.** Every pair of states in the single fiber shares a
certificate, the capacity is two, and the search returns two. -/
theorem threeWay_pairwise_compatible_capacity_two :
    PairwiseFiberCompatible threeWayObserver threeWayAdmissible ∧
      relationalSideCapacity threeWayObserver threeWayAdmissible threeWay_certificates = 2 ∧
      relationalSideCapacity? threeValueEnumeration threeValueEnumeration threeWayObserver
        threeWayAdmissible = some 2 :=
  ⟨threeWay_pairwiseFiberCompatible, threeWay_capacity_eq_two, threeWay_relationalSideCapacity?⟩

end OperatorKO7.Meta.OperationalInexpressibility.RelationalSideCapacity
