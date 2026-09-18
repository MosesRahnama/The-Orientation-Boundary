import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Compactness.Compact
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

/-!
# Observer-target confusability graph

For an observer `q : X → Q` and target `P : X → V`, two source states are
confusable when the observer identifies them but the target separates them. The
resulting simple graph is the zero-error obstruction carried by the observer.

A side channel `s : X → C` licenses the augmented observer `x ↦ (q x, s x)` for
`P` if and only if `s` is a proper coloring of this graph. Consequently, an
`n`-symbol resolving side channel exists if and only if the graph is `n`-colorable,
and the graph's chromatic number is exactly the minimum finite resolving alphabet.
For arbitrary inputs, a finite resolving alphabet exists exactly when every
observer fiber has finitely many target values, with one common size bound.
For finite inputs, the maximum fiber size gives the alphabet size and its ceiling
binary logarithm gives the minimum fixed-length code length.

Relation: observer-fiber collision combined with target disequality.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel checked; no external artifact or stochastic assumption.
Scope: arbitrary source, observer, target, and side-channel types. Only the
finite-source maximum and computable code-deficit formulas require finite inputs.
Non-vacuity: finite and infinite input examples test attainable and impossible capacities.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.Confusability

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

universe u v w z

/-- Two states are confusable for `(q, P)` when `q` merges them while `P`
requires them to remain distinct. -/
def Confusable {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (x y : X) : Prop :=
  q x = q y ∧ P x ≠ P y

/-- The simple graph whose edges are exactly the observer collisions that destroy
licensing of the target. -/
def confusabilityGraph {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) : SimpleGraph X where
  Adj := Confusable q P
  symm := by
    intro x y h
    exact ⟨h.1.symm, fun hyx => h.2 hyx.symm⟩
  loopless := by
    intro x h
    exact h.2 rfl

@[simp] theorem confusabilityGraph_adj_iff
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (x y : X) :
    (confusabilityGraph q P).Adj x y ↔ q x = q y ∧ P x ≠ P y :=
  Iff.rfl

/-- A side channel is resolving exactly when adjacent/confusable source states
receive distinct side-channel symbols. -/
def ResolvingSideChannel {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C) : Prop :=
  ∀ ⦃x y⦄, Confusable q P x y → s x ≠ s y

/-- The augmented observer formed by retaining the original observation and adding
one side-channel coordinate. -/
def augmentObserver {X : Type u} {Q : Type v} {C : Type z}
    (q : X → Q) (s : X → C) : X → Q × C :=
  fun x => (q x, s x)

/-- Zero-error side-channel theorem: licensing the augmented observer is equivalent
to proper coloring of the confusability relation. -/
theorem licensed_augment_iff_resolving
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C) :
    Licensed (augmentObserver q s) P ↔ ResolvingSideChannel q P s := by
  constructor
  · intro hlic x y hconf hs
    apply hconf.2
    apply hlic x y
    exact Prod.ext hconf.1 hs
  · intro hresolve x y haug
    by_contra hP
    have hconf : Confusable q P x y := ⟨congrArg Prod.fst haug, hP⟩
    exact (hresolve hconf) (congrArg Prod.snd haug)

/-- Relabeling a side-channel alphabet by an equivalence preserves and reflects
licensing. -/
theorem licensed_augment_equiv
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z} {D : Type*}
    (q : X → Q) (P : X → V) (s : X → C) (e : C ≃ D) :
    Licensed (augmentObserver q s) P ↔
      Licensed (augmentObserver q (fun x => e (s x))) P := by
  constructor
  · intro h x y hxy
    have hq : q x = q y := congrArg (fun p : Q × D => p.1) hxy
    have hs : e (s x) = e (s y) := congrArg (fun p : Q × D => p.2) hxy
    apply h x y
    exact Prod.ext hq (e.injective hs)
  · intro h x y hxy
    have hq : q x = q y := congrArg (fun p : Q × C => p.1) hxy
    have hs : s x = s y := congrArg (fun p : Q × C => p.2) hxy
    apply h x y
    exact Prod.ext hq (congrArg e hs)

/-- Equivalent alphabets support exactly the same resolving channels. -/
theorem exists_resolving_channel_congr
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z} {D : Type*}
    (q : X → Q) (P : X → V) (e : C ≃ D) :
    (∃ s : X → C, Licensed (augmentObserver q s) P) ↔
      ∃ s : X → D, Licensed (augmentObserver q s) P := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun x => e (s x), (licensed_augment_equiv q P s e).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨fun x => e.symm (s x),
      (licensed_augment_equiv q P s e.symm).mp hs⟩

/-- Every resolving side channel is literally a Mathlib proper coloring of the
confusability graph. -/
def coloringOfResolving
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C)
    (hs : ResolvingSideChannel q P s) :
    (confusabilityGraph q P).Coloring C :=
  SimpleGraph.Coloring.mk s (fun h => hs h)

@[simp] theorem coloringOfResolving_apply
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C)
    (hs : ResolvingSideChannel q P s) (x : X) :
    coloringOfResolving q P s hs x = s x :=
  rfl

/-- Conversely, every proper graph coloring is a resolving side channel. -/
theorem resolving_of_coloring
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V)
    (c : (confusabilityGraph q P).Coloring C) :
    ResolvingSideChannel q P c := by
  intro x y hconf
  exact c.valid hconf

/-- A proper coloring licenses the target through the augmented observer. -/
theorem licensed_augment_of_coloring
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V)
    (c : (confusabilityGraph q P).Coloring C) :
    Licensed (augmentObserver q c) P :=
  (licensed_augment_iff_resolving q P c).2 (resolving_of_coloring q P c)

/-- Finite alphabet equivalence: an `n`-coloring is exactly an `n`-symbol side
channel that repairs the observer for the target. -/
theorem colorable_iff_exists_fin_resolving_channel
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (n : Nat) :
    (confusabilityGraph q P).Colorable n ↔
      ∃ s : X → Fin n, Licensed (augmentObserver q s) P := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c, licensed_augment_of_coloring q P c⟩
  · rintro ⟨s, hlic⟩
    exact ⟨coloringOfResolving q P s ((licensed_augment_iff_resolving q P s).1 hlic)⟩

/-- The minimum finite resolving alphabet is the graph chromatic number. This is
stated in the exact order-theoretic form supplied by Mathlib: `χ(G) ≤ n` iff an
`n`-symbol licensed side channel exists. -/
theorem chromaticNumber_le_iff_exists_fin_resolving_channel
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (n : Nat) :
    (confusabilityGraph q P).chromaticNumber ≤ n ↔
      ∃ s : X → Fin n, Licensed (augmentObserver q s) P := by
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  exact colorable_iff_exists_fin_resolving_channel q P n

/-- On a single observer fiber, target-separated states must receive different side
symbols. This is the complete-multipartite fiber law without any finite assumptions. -/
theorem sameFiber_target_ne_forces_side_ne
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C)
    (hlic : Licensed (augmentObserver q s) P)
    {x y : X} (hq : q x = q y) (hP : P x ≠ P y) :
    s x ≠ s y := by
  exact ((licensed_augment_iff_resolving q P s).1 hlic) ⟨hq, hP⟩

/-- If the original observer is constant, the confusability graph is exactly the
complete multipartite graph induced by target fibers: adjacency is target
disequality. -/
theorem constantObserver_adj_iff_target_ne
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V)
    (hq : ∀ x y, q x = q y) (x y : X) :
    (confusabilityGraph q P).Adj x y ↔ P x ≠ P y := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hq x y, h⟩

/-! ## Capacity on arbitrary input spaces -/

/-- The target values attained by inputs with observation o. -/
def FiberTargetValues {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (o : Q) :=
  {value : V // ∃ x, q x = o ∧ P x = value}

/-- Each attained fiber value has an actual input representative. -/
noncomputable def fiberTargetRepresentative
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (o : Q) (a : FiberTargetValues q P o) : X :=
  Classical.choose a.property

theorem fiberTargetRepresentative_spec
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (o : Q) (a : FiberTargetValues q P o) :
    q (fiberTargetRepresentative q P o a) = o ∧
      P (fiberTargetRepresentative q P o a) = a.val :=
  Classical.choose_spec a.property

/-- A licensed channel embeds each fiber's attained target values into its alphabet. -/
noncomputable def fiberTargetEmbeddingOfLicense
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) (s : X → C)
    (hlic : Licensed (augmentObserver q s) P) (o : Q) :
    FiberTargetValues q P o ↪ C where
  toFun a := s (fiberTargetRepresentative q P o a)
  inj' := by
    intro a b hab
    apply Subtype.ext
    have ha := fiberTargetRepresentative_spec q P o a
    have hb := fiberTargetRepresentative_spec q P o b
    have hP := hlic (fiberTargetRepresentative q P o a)
      (fiberTargetRepresentative q P o b) (Prod.ext (ha.1.trans hb.1.symm) hab)
    exact ha.2.symm.trans (hP.trans hb.2)

/-- Fiber embeddings define one channel on all inputs. -/
def sideChannelOfFiberEmbeddings
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V)
    (e : ∀ o, FiberTargetValues q P o ↪ C) : X → C :=
  fun x => e (q x) ⟨P x, x, rfl, rfl⟩

theorem sideChannelOfFiberEmbeddings_licensed
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V)
    (e : ∀ o, FiberTargetValues q P o ↪ C) :
    Licensed (augmentObserver q (sideChannelOfFiberEmbeddings q P e)) P := by
  intro x y hxy
  have hq : q x = q y := congrArg Prod.fst hxy
  have hs := congrArg Prod.snd hxy
  have sameValue : ∀ (o₁ o₂ : Q) (a : FiberTargetValues q P o₁)
      (b : FiberTargetValues q P o₂), o₁ = o₂ → e o₁ a = e o₂ b → a.val = b.val := by
    intro o₁ o₂ a b ho he
    cases ho
    exact congrArg Subtype.val ((e o₁).injective he)
  exact sameValue (q x) (q y) ⟨P x, x, rfl, rfl⟩ ⟨P y, y, rfl, rfl⟩ hq hs

/-- Exact capacity law for arbitrary input, observation, target, and alphabet types. -/
theorem exists_resolving_channel_iff_fiber_embeddings
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (q : X → Q) (P : X → V) :
    (∃ s : X → C, Licensed (augmentObserver q s) P) ↔
      ∀ o, Nonempty (FiberTargetValues q P o ↪ C) := by
  classical
  constructor
  · rintro ⟨s, hs⟩ o
    exact ⟨fiberTargetEmbeddingOfLicense q P s hs o⟩
  · intro h
    let e : ∀ o, FiberTargetValues q P o ↪ C := fun o => Classical.choice (h o)
    exact ⟨sideChannelOfFiberEmbeddings q P e,
      sideChannelOfFiberEmbeddings_licensed q P e⟩

/-- Finite capacity requires only bounded finite target sets within observation fibers. -/
theorem exists_fin_resolving_channel_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (n : Nat) :
    (∃ s : X → Fin n, Licensed (augmentObserver q s) P) ↔
      ∀ o, Finite (FiberTargetValues q P o) ∧ Nat.card (FiberTargetValues q P o) ≤ n := by
  classical
  rw [exists_resolving_channel_iff_fiber_embeddings]
  constructor
  · intro h o
    rcases h o with ⟨e⟩
    refine ⟨Finite.of_injective e e.injective, ?_⟩
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Finite.card_le_of_embedding e
  · intro h o
    letI : Finite (FiberTargetValues q P o) := (h o).1
    letI := Fintype.ofFinite (FiberTargetValues q P o)
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using (h o).2

/-- Exact capacity law for every finite alphabet type, including empty and
singleton alphabets. The bound is its intrinsic cardinality, with no chosen
enumeration in the statement. -/
theorem exists_finite_resolving_channel_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z} [Finite C]
    (q : X → Q) (P : X → V) :
    (∃ s : X → C, Licensed (augmentObserver q s) P) ↔
      ∀ o, Finite (FiberTargetValues q P o) ∧
        Nat.card (FiberTargetValues q P o) ≤ Nat.card C := by
  classical
  exact (exists_resolving_channel_congr q P (Finite.equivFin C)).trans
    (exists_fin_resolving_channel_iff_fiber_capacity q P (Nat.card C))

theorem colorable_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (n : Nat) :
    (confusabilityGraph q P).Colorable n ↔
      ∀ o, Finite (FiberTargetValues q P o) ∧ Nat.card (FiberTargetValues q P o) ≤ n := by
  rw [colorable_iff_exists_fin_resolving_channel,
    exists_fin_resolving_channel_iff_fiber_capacity]

theorem chromaticNumber_le_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (n : Nat) :
    (confusabilityGraph q P).chromaticNumber ≤ n ↔
      ∀ o, Finite (FiberTargetValues q P o) ∧ Nat.card (FiberTargetValues q P o) ≤ n := by
  rw [chromaticNumber_le_iff_exists_fin_resolving_channel,
    exists_fin_resolving_channel_iff_fiber_capacity]

/-- This counts fixed-length binary codes; it has no probability or entropy premise. -/
theorem exists_binary_resolving_channel_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (k : Nat) :
    (∃ s : X → Fin (2 ^ k), Licensed (augmentObserver q s) P) ↔
      ∀ o, Finite (FiberTargetValues q P o) ∧
        Nat.card (FiberTargetValues q P o) ≤ 2 ^ k :=
  exists_fin_resolving_channel_iff_fiber_capacity q P (2 ^ k)

theorem one_symbol_channel_iff_licensed
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) :
    (∃ s : X → Fin 1, Licensed (augmentObserver q s) P) ↔ Licensed q P := by
  constructor
  · rintro ⟨s, hs⟩ x y hq
    exact hs x y (Prod.ext hq (Subsingleton.elim (s x) (s y)))
  · intro h
    exact ⟨fun _ => 0, fun x y hxy => h x y (congrArg Prod.fst hxy)⟩

theorem zero_symbol_channel_iff_isEmpty
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) :
    (∃ s : X → Fin 0, Licensed (augmentObserver q s) P) ↔ IsEmpty X := by
  constructor
  · rintro ⟨s, _⟩
    exact ⟨fun x => Fin.elim0 (s x)⟩
  · intro h
    letI := h
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

theorem no_fin_channel_of_infinite_fiber
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (o : Q)
    [Infinite (FiberTargetValues q P o)] (n : Nat) :
    ¬ ∃ s : X → Fin n, Licensed (augmentObserver q s) P := by
  rintro ⟨s, hs⟩
  let e := fiberTargetEmbeddingOfLicense q P s hs o
  exact not_injective_infinite_finite e e.injective

/-- Finite fibers without a common bound still require an infinite alphabet. -/
theorem no_fin_channel_of_unbounded_fibers
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V)
    (h : ∀ n : Nat, ∃ o, Finite (FiberTargetValues q P o) ∧
      n < Nat.card (FiberTargetValues q P o)) (n : Nat) :
    ¬ ∃ s : X → Fin n, Licensed (augmentObserver q s) P := by
  intro hs
  have hb := (exists_fin_resolving_channel_iff_fiber_capacity q P n).mp hs
  obtain ⟨o, _, ho⟩ := h n
  exact Nat.not_lt_of_ge (hb o).2 ho

/-! ## Infinite-source controls -/

def natParitySide (x : Nat) : Fin 2 :=
  ⟨x % 2, Nat.mod_lt _ (by decide)⟩

theorem natParitySide_licenses :
    Licensed (augmentObserver (fun _ : Nat => ()) natParitySide)
      (fun x : Nat => x % 2) := by
  intro x y h
  exact congrArg Fin.val (congrArg Prod.snd h)

theorem natParity_no_one_symbol :
    ¬ ∃ s : Nat → Fin 1,
      Licensed (augmentObserver (fun _ : Nat => ()) s) (fun x : Nat => x % 2) := by
  intro hs
  have h := (one_symbol_channel_iff_licensed (fun _ : Nat => ())
    (fun x : Nat => x % 2)).mp hs 0 1 rfl
  exact (by decide : (0 : Nat) % 2 ≠ 1 % 2) h

theorem nat_identity_no_finite_channel (n : Nat) :
    ¬ ∃ s : Nat → Fin n,
      Licensed (augmentObserver (fun _ : Nat => ()) s) id := by
  rintro ⟨s, hs⟩
  apply not_injective_infinite_finite s
  intro x y h
  exact hs x y (Prod.ext rfl h)

/-! ## Exact finite multiplicity and binary capacity -/

/-- A finite-source graph has an `n`-coloring exactly when every observer fiber
has at most `n` target values. The statement includes empty sources and `n = 0`. -/
theorem colorable_iff_fiberMultiplicity_le
    {X : Type u} {Q : Type v} {V : Type w}
    [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) (n : Nat) :
    (confusabilityGraph q P).Colorable n ↔ fiberMultiplicity q P ≤ n := by
  rw [colorable_iff_exists_fin_resolving_channel]
  constructor
  · rintro ⟨s, hs⟩
    have h := additional_channel_card_lower_bound q P s
      ((licensed_iff_factorsThrough (augmentObserver q s) P).1 hs)
    simpa using h
  · intro hmn
    obtain ⟨s, hs⟩ := exists_optimal_side_channel q P
    refine ⟨fun x => Fin.castLE hmn (s x), ?_⟩
    intro x y hxy
    have hq : q x = q y := congrArg Prod.fst hxy
    have hc : s x = s y :=
      Fin.castLE_injective hmn (congrArg Prod.snd hxy)
    exact hs (Prod.ext hq hc)

/-- The chromatic number is the maximum target multiplicity within an observer
fiber, including the empty-source case where both values are zero. -/
theorem chromaticNumber_eq_fiberMultiplicity
    {X : Type u} {Q : Type v} {V : Type w}
    [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) :
    (confusabilityGraph q P).chromaticNumber = (fiberMultiplicity q P : ℕ∞) := by
  have hupper : (confusabilityGraph q P).chromaticNumber ≤
      (fiberMultiplicity q P : ℕ∞) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.2
      ((colorable_iff_fiberMultiplicity_le q P _).2 le_rfl)
  have hfinite : (confusabilityGraph q P).chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hupper
  have hlower := (colorable_iff_fiberMultiplicity_le q P _).1
    ((confusabilityGraph q P).colorable_of_chromaticNumber_ne_top hfinite)
  apply le_antisymm hupper
  have hcast : (fiberMultiplicity q P : ℕ∞) ≤
      ((confusabilityGraph q P).chromaticNumber.toNat : ℕ∞) := by
    exact_mod_cast hlower
  simpa only [ENat.coe_toNat hfinite] using hcast

/-- The count-valued code deficit is the ceiling binary logarithm of the graph's
chromatic number, not a Shannon entropy. -/
theorem fiberCodeDeficit_eq_clog_chromaticNumber
    {X : Type u} {Q : Type v} {V : Type w}
    [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) :
    fiberCodeDeficit q P =
      Nat.clog 2 (confusabilityGraph q P).chromaticNumber.toNat := by
  rw [chromaticNumber_eq_fiberMultiplicity]
  rfl

/-- A fixed-length `k`-bit side channel resolves the target exactly when the code
deficit is at most `k`. -/
theorem exists_binary_resolving_channel_iff
    {X : Type u} {Q : Type v} {V : Type w}
    [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) (k : Nat) :
    (∃ s : X → Fin (2 ^ k), Licensed (augmentObserver q s) P) ↔
      fiberCodeDeficit q P ≤ k := by
  rw [← colorable_iff_exists_fin_resolving_channel,
    colorable_iff_fiberMultiplicity_le]
  exact Nat.le_pow_iff_clog_le (by decide : 1 < 2)

/-- The code deficit is attained and is no larger than every resolving binary
code length. -/
theorem fiberCodeDeficit_isLeast_binary_resolving_length
    {X : Type u} {Q : Type v} {V : Type w}
    [Fintype X] [DecidableEq Q] [DecidableEq V]
    (q : X → Q) (P : X → V) :
    IsLeast {k : Nat | ∃ s : X → Fin (2 ^ k), Licensed (augmentObserver q s) P}
      (fiberCodeDeficit q P) := by
  exact ⟨(exists_binary_resolving_channel_iff q P _).2 le_rfl,
    fun k hk => (exists_binary_resolving_channel_iff q P k).1 hk⟩

/-! ## Non-vacuous finite fixture -/

/-- Four source states, a constant observer, and a binary target. -/
def binaryFixtureObserver (_ : Fin 4) : Unit := ()

def binaryFixtureTarget (i : Fin 4) : Bool := decide (i.val % 2 = 0)

/-- The fixture has a genuine confusability edge. -/
theorem binaryFixture_has_edge :
    (confusabilityGraph binaryFixtureObserver binaryFixtureTarget).Adj
      (0 : Fin 4) (1 : Fin 4) := by
  constructor
  · rfl
  · decide

/-- Equal-target states are not adjacent, so the graph is not complete. -/
theorem binaryFixture_has_nonedge :
    ¬ (confusabilityGraph binaryFixtureObserver binaryFixtureTarget).Adj
      (0 : Fin 4) (2 : Fin 4) := by
  intro h
  exact h.2 (by decide)

/-- Parity itself is a two-symbol resolving side channel for the fixture. -/
def binaryFixtureSide (i : Fin 4) : Fin 2 :=
  if binaryFixtureTarget i then 0 else 1

/-- The fixture's side symbol identifies exactly the same binary partition as
the target. -/
theorem binaryFixtureSide_eq_iff_target_eq (x y : Fin 4) :
    binaryFixtureSide x = binaryFixtureSide y ↔
      binaryFixtureTarget x = binaryFixtureTarget y := by
  unfold binaryFixtureSide
  cases hx : binaryFixtureTarget x <;>
    cases hy : binaryFixtureTarget y <;>
      simp_all

/-- The concrete side channel repairs the otherwise-confused observer. -/
theorem binaryFixtureSide_licenses :
    Licensed (augmentObserver binaryFixtureObserver binaryFixtureSide)
      binaryFixtureTarget := by
  apply (licensed_augment_iff_resolving _ _ _).2
  intro x y hconf hside
  exact hconf.2 ((binaryFixtureSide_eq_iff_target_eq x y).1 hside)

/-- The four-state fixture requires exactly two colors despite having non-edges. -/
theorem binaryFixture_chromaticNumber :
    (confusabilityGraph binaryFixtureObserver binaryFixtureTarget).chromaticNumber = 2 := by
  rw [chromaticNumber_eq_fiberMultiplicity]
  have h : fiberMultiplicity binaryFixtureObserver binaryFixtureTarget = 2 := by decide
  norm_num [h]

/-- Exactly one fixed-length bit is required by the four-state fixture. -/
theorem binaryFixture_binary_capacity (k : Nat) :
    (∃ s : Fin 4 → Fin (2 ^ k),
      Licensed (augmentObserver binaryFixtureObserver s) binaryFixtureTarget) ↔ 1 ≤ k := by
  rw [exists_binary_resolving_channel_iff]
  have h : fiberCodeDeficit binaryFixtureObserver binaryFixtureTarget = 1 := by
    change Nat.clog 2 (fiberMultiplicity binaryFixtureObserver binaryFixtureTarget) = 1
    have hm : fiberMultiplicity binaryFixtureObserver binaryFixtureTarget = 2 := by decide
    rw [hm]
    exact Nat.clog_eq_one (le_refl 2) (le_refl 2)
  rw [h]



/-! ## Infinite-capacity classification and necessity controls -/

/-- Infinite chromatic number means every finite capacity fails on an attained fiber. -/
theorem chromaticNumber_eq_top_iff_fiber_obstructions
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) :
    (confusabilityGraph q P).chromaticNumber = ⊤ ↔
      ∀ n : Nat, ∃ o, ¬ Finite (FiberTargetValues q P o) ∨
        n < Nat.card (FiberTargetValues q P o) := by
  classical
  constructor
  · intro htop n
    by_contra hnone
    have hc : ∀ o, Finite (FiberTargetValues q P o) ∧
        Nat.card (FiberTargetValues q P o) ≤ n := by
      intro o
      constructor
      · by_contra hf
        exact hnone ⟨o, Or.inl hf⟩
      · by_contra hb
        exact hnone ⟨o, Or.inr (by omega)⟩
    have hbound := (chromaticNumber_le_iff_fiber_capacity q P n).mpr hc
    rw [htop] at hbound
    exact (not_le_of_gt (WithTop.coe_lt_top n)) hbound
  · intro h
    by_contra hne
    obtain ⟨n, hn⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp hne
    have hb := (colorable_iff_fiber_capacity q P n).mp hn
    obtain ⟨o, ho⟩ := h n
    rcases ho with hfinite | hlarge
    · exact hfinite (hb o).1
    · exact Nat.not_lt_of_ge (hb o).2 hlarge

def growingFiberObserver (x : Σ n : Nat, Fin (n + 1)) : Nat := x.1

def growingFiberTarget (x : Σ n : Nat, Fin (n + 1)) : Nat := x.2.val

/-- Fiber n has exactly n+1 attained targets, although the input space is infinite. -/
def growingFiberEquiv (n : Nat) :
    FiberTargetValues growingFiberObserver growingFiberTarget n ≃ Fin (n + 1) where
  toFun a := ⟨a.val, by
    obtain ⟨x, ho, ht⟩ := a.property
    have hb := x.2.isLt
    change x.1 = n at ho
    change x.2.val = a.val at ht
    omega⟩
  invFun i := ⟨i.val, ⟨n, i⟩, rfl, rfl⟩
  left_inv a := Subtype.ext rfl
  right_inv i := Fin.ext rfl

theorem growingFiber_finite (n : Nat) :
    Finite (FiberTargetValues growingFiberObserver growingFiberTarget n) :=
  Finite.of_injective (growingFiberEquiv n) (growingFiberEquiv n).injective

theorem growingFiber_card (n : Nat) :
    Nat.card (FiberTargetValues growingFiberObserver growingFiberTarget n) = n + 1 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using Nat.card_congr (growingFiberEquiv n)

/-- Finite target sets in every fiber do not suffice without one common bound. -/
theorem growingFiber_no_finite_channel (n : Nat) :
    ¬ ∃ s : (Σ k : Nat, Fin (k + 1)) → Fin n,
      Licensed (augmentObserver growingFiberObserver s) growingFiberTarget := by
  apply no_fin_channel_of_unbounded_fibers growingFiberObserver growingFiberTarget
  intro k
  exact ⟨k, growingFiber_finite k, by rw [growingFiber_card]; omega⟩

theorem nat_identity_fiber_infinite :
    Infinite (FiberTargetValues (fun _ : Nat => ()) (id : Nat → Nat) ()) := by
  let f : Nat → FiberTargetValues (fun _ : Nat => ()) (id : Nat → Nat) () :=
    fun n => ⟨n, n, rfl, rfl⟩
  exact Infinite.of_injective f (fun _ _ h => congrArg Subtype.val h)

/-- Nat.card alone assigns zero to an infinite fiber and cannot certify capacity. -/
theorem nat_card_without_finite_is_insufficient (n : Nat) :
    (∀ o : Unit, Nat.card (FiberTargetValues (fun _ : Nat => ()) (id : Nat → Nat) o) ≤ n) ∧
      ¬ ∃ s : Nat → Fin n,
        Licensed (augmentObserver (fun _ : Nat => ()) s) id := by
  refine ⟨?_, nat_identity_no_finite_channel n⟩
  intro o
  cases o
  letI := nat_identity_fiber_infinite
  rw [Nat.card_eq_zero_of_infinite]
  exact Nat.zero_le n


/-! ## One retained channel across all stages -/

open OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

theorem orbit_refines_stabilized_observer
    {X : Type u} {Q : Type v} (F : X → X) (q : X → Q)
    [Finite (ObservedValue q)] (hc : ObservationCompatible F q) (n : Nat) :
    ObserverRefines (orbitObserver F q n)
      (orbitObserver F q (Nat.card (ObservedValue q) - 1)) := by
  have h := (compatible_license_at_image_card_pred_iff_persistent F q hc
    (orbitObserver F q (Nat.card (ObservedValue q) - 1))).mp (fun _ _ he => he)
  intro x y hxy
  exact h n x y hxy

/-- The channel reads the original input, not the evolved state. -/
theorem fixed_channel_licenses_all_iff_at_image_bound
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) (s : X → C) :
    (∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      Licensed (augmentObserver
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) s) P := by
  constructor
  · exact fun h => h _
  · intro h n x y he
    have hside : s x = s y := congrArg Prod.snd he
    have hobs : orbitObserver F q n x = orbitObserver F q n y := congrArg Prod.fst he
    exact h x y (Prod.ext (orbit_refines_stabilized_observer F q hc n hobs) hside)

theorem exists_fixed_channel_all_iff_at_image_bound
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) :
    (∃ s : X → C, ∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      ∃ s : X → C, Licensed (augmentObserver
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) s) P := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (fixed_channel_licenses_all_iff_at_image_bound F q hc P s).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (fixed_channel_licenses_all_iff_at_image_bound F q hc P s).mpr hs⟩

/-- For finite observation images, separate stage repairs have one common repair,
even when the channel alphabet is infinite. -/
theorem exists_fixed_channel_iff_stagewise_channels
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) :
    (∃ s : X → C, ∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      ∀ n, ∃ s : X → C, Licensed (augmentObserver (orbitObserver F q n) s) P := by
  constructor
  · rintro ⟨s, hs⟩ n
    exact ⟨s, hs n⟩
  · intro h
    exact (exists_fixed_channel_all_iff_at_image_bound F q hc P).mpr (h _)

/-- The stabilized target fibers determine the exact permanent finite alphabet. -/
theorem permanent_fin_channel_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w}
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) (m : Nat) :
    (∃ s : X → Fin m, ∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      ∀ o, Finite (FiberTargetValues
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ∧
        Nat.card (FiberTargetValues
          (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ≤ m := by
  rw [exists_fixed_channel_all_iff_at_image_bound F q hc P,
    exists_fin_resolving_channel_iff_fiber_capacity]

/-- The stabilized target fibers determine the exact permanent capacity of an
arbitrary finite alphabet, without replacing that alphabet in the statement by
`Fin m`. -/
theorem permanent_finite_alphabet_channel_iff_fiber_capacity
    {X : Type u} {Q : Type v} {V : Type w} {C : Type z} [Finite C]
    (F : X → X) (q : X → Q) [Finite (ObservedValue q)]
    (hc : ObservationCompatible F q) (P : X → V) :
    (∃ s : X → C, ∀ n, Licensed (augmentObserver (orbitObserver F q n) s) P) ↔
      ∀ o, Finite (FiberTargetValues
        (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ∧
        Nat.card (FiberTargetValues
          (orbitObserver F q (Nat.card (ObservedValue q) - 1)) P o) ≤ Nat.card C := by
  rw [exists_fixed_channel_all_iff_at_image_bound F q hc P,
    exists_finite_resolving_channel_iff_fiber_capacity]

/-! ## Finite-alphabet compactness without finite observations -/

/-- Zero-error requirements form a closed set in the product of finite alphabets. -/
theorem finite_channel_set_isClosed
    {X : Type u} {Q : Type v} {V : Type w}
    (q : X → Q) (P : X → V) (m : Nat) :
    IsClosed {s : X → Fin m | Licensed (augmentObserver q s) P} := by
  classical
  have hset : {s : X → Fin m | Licensed (augmentObserver q s) P} =
      ⋂ x, ⋂ y, ⋂ (_ : q x = q y), ⋂ (_ : P x ≠ P y),
        {s : X → Fin m | s x ≠ s y} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h x y hq hP hs
      exact hP (h x y (Prod.ext hq hs))
    · intro h x y hxy
      by_contra hP
      exact h x y (congrArg Prod.fst hxy) hP (congrArg Prod.snd hxy)
  rw [hset]
  refine isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  have hcont : Continuous (fun s : X → Fin m => (s x, s y)) :=
    (continuous_apply x).prodMk (continuous_apply y)
  exact IsClosed.preimage hcont
    (isClosed_discrete {p : Fin m × Fin m | p.1 ≠ p.2})

/-- A common finite channel exists iff every finite collection of requirements has one.
Observers and targets may have different codomain types at each index. -/
theorem finite_channel_compactness
    {X : Type u} {I : Type*} {Q : I → Type v} {V : I → Type w}
    (qs : (i : I) → X → Q i) (Ps : (i : I) → X → V i) (m : Nat) :
    (∃ s : X → Fin m, ∀ i, Licensed (augmentObserver (qs i) s) (Ps i)) ↔
      ∀ J : Finset I, ∃ s : X → Fin m,
        ∀ i ∈ J, Licensed (augmentObserver (qs i) s) (Ps i) := by
  classical
  constructor
  · rintro ⟨s, hs⟩ J
    exact ⟨s, fun i _ => hs i⟩
  · intro h
    let S : I → Set (X → Fin m) := fun i => {s | Licensed (augmentObserver (qs i) s) (Ps i)}
    have hclosed : ∀ i, IsClosed (S i) := fun i => finite_channel_set_isClosed (qs i) (Ps i) m
    have hfinite : ∀ J : Finset I,
        ((Set.univ : Set (X → Fin m)) ∩ ⋂ i ∈ J, S i).Nonempty := by
      intro J
      obtain ⟨s, hs⟩ := h J
      refine ⟨s, Set.mem_univ s, ?_⟩
      exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi => hs i hi
    obtain ⟨s, _, hs⟩ := isCompact_univ.inter_iInter_nonempty S hclosed hfinite
    exact ⟨s, fun i => Set.mem_iInter.mp hs i⟩

/-- Compactness for an arbitrary finite alphabet: one channel meets every
requirement exactly when each finite collection has a common channel. -/
theorem finite_alphabet_compactness
    {X : Type u} {I : Type*} {Q : I → Type v} {V : I → Type w}
    {C : Type z} [Finite C]
    (qs : (i : I) → X → Q i) (Ps : (i : I) → X → V i) :
    (∃ s : X → C, ∀ i, Licensed (augmentObserver (qs i) s) (Ps i)) ↔
      ∀ J : Finset I, ∃ s : X → C,
        ∀ i ∈ J, Licensed (augmentObserver (qs i) s) (Ps i) := by
  classical
  let e : C ≃ Fin (Nat.card C) := Finite.equivFin C
  constructor
  · rintro ⟨s, hs⟩ J
    exact ⟨s, fun i _ => hs i⟩
  · intro h
    have hfin : ∀ J : Finset I, ∃ s : X → Fin (Nat.card C),
        ∀ i ∈ J, Licensed (augmentObserver (qs i) s) (Ps i) := by
      intro J
      obtain ⟨s, hs⟩ := h J
      refine ⟨fun x => e (s x), ?_⟩
      intro i hi
      exact (licensed_augment_equiv (qs i) (Ps i) s e).mp (hs i hi)
    obtain ⟨s, hs⟩ :=
      (finite_channel_compactness qs Ps (Nat.card C)).mpr hfin
    refine ⟨fun x => e.symm (s x), ?_⟩
    intro i
    exact (licensed_augment_equiv (qs i) (Ps i) s e.symm).mp (hs i)

/-- For any coarsening sequence, stagewise finite-alphabet repairs have one fixed
repair. No finite observation image, finite input type, or stabilization is assumed. -/
theorem coarsening_fixed_finite_channel_iff_stagewise
    {X : Type u} {Q : Nat → Type v} {V : Type w}
    (qs : (n : Nat) → X → Q n)
    (hc : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V) (m : Nat) :
    (∃ s : X → Fin m, ∀ n, Licensed (augmentObserver (qs n) s) P) ↔
      ∀ n, ∃ s : X → Fin m, Licensed (augmentObserver (qs n) s) P := by
  constructor
  · rintro ⟨s, hs⟩ n
    exact ⟨s, hs n⟩
  · intro h
    apply (finite_channel_compactness qs (fun _ => P) m).mpr
    intro J
    obtain ⟨s, hs⟩ := h (J.sup id)
    refine ⟨s, ?_⟩
    intro n hn x y hxy
    have hside : s x = s y := congrArg Prod.snd hxy
    have hobs : qs n x = qs n y := congrArg Prod.fst hxy
    have hle : n ≤ J.sup id := Finset.le_sup (f := id) hn
    exact hs x y (Prod.ext (coarsening_refines_of_le qs hc n (J.sup id) hle hobs) hside)

/-- For every finite alphabet type, stagewise repairs of a coarsening sequence
have one fixed repair. No finite observation image, finite input type, or
stabilization assumption is needed. -/
theorem coarsening_fixed_finite_alphabet_iff_stagewise
    {X : Type u} {Q : Nat → Type v} {V : Type w} {C : Type z} [Finite C]
    (qs : (n : Nat) → X → Q n)
    (hc : ∀ n, ObserverRefines (qs n) (qs (n + 1))) (P : X → V) :
    (∃ s : X → C, ∀ n, Licensed (augmentObserver (qs n) s) P) ↔
      ∀ n, ∃ s : X → C, Licensed (augmentObserver (qs n) s) P := by
  constructor
  · rintro ⟨s, hs⟩ n
    exact ⟨s, hs n⟩
  · intro h
    apply (finite_alphabet_compactness qs (fun _ => P)).mpr
    intro J
    obtain ⟨s, hs⟩ := h (J.sup id)
    refine ⟨s, ?_⟩
    intro n hn x y hxy
    have hside : s x = s y := congrArg Prod.snd hxy
    have hobs : qs n x = qs n y := congrArg Prod.fst hxy
    have hle : n ≤ J.sup id := Finset.le_sup (f := id) hn
    exact hs x y
      (Prod.ext (coarsening_refines_of_le qs hc n (J.sup id) hle hobs) hside)


/-! ## Separate repairs need not be one repair without compatibility -/

def threePairObserver (i x : Fin 3) : Bool := decide (x = i)

theorem threePair_stagewise_two_symbols :
    ∀ i : Fin 3, ∃ s : Fin 3 → Fin 2,
      Licensed (augmentObserver (threePairObserver i) s) id := by
  unfold Licensed augmentObserver threePairObserver
  decide

theorem threePair_no_common_two_symbols :
    ¬ ∃ s : Fin 3 → Fin 2, ∀ i : Fin 3,
      Licensed (augmentObserver (threePairObserver i) s) id := by
  unfold Licensed augmentObserver threePairObserver
  decide

theorem threePair_not_coarsening :
    ¬ ObserverRefines (threePairObserver 0) (threePairObserver 1) := by
  intro h
  exact (by decide : threePairObserver 1 1 ≠ threePairObserver 1 2)
    (@h 1 2 (by decide))

end OperatorKO7.Meta.OperationalInexpressibility.Confusability
