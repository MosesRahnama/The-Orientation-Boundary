import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.PairInvariants
import OperatorKO7.Meta.BoundaryObserver.PlaceExistence
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

/-!
# Foundational sentences of the Boundary-Observation Principle

The statements of the first sections of the manuscript that no earlier declaration states in the
words of the paper: the least set with a separating test, the constancy of continuous discrete
coordinates on a preconnected space, the tables of comparisons that are kernels, the determined
tests of two observers and their values in an arbitrary set, the apartness of an observer, the
sets of tests determined by one observer, the bijection of the codomains of two surjective
observers with one kernel, the four invariant relations of a merged pair, the orbits and the
invariant tests of the self-test with the law of its indicator, the least size of a resolving
coordinate, the fiber condition of a fiberwise bijective coordinate without a finiteness
hypothesis, the resolving coordinates of the observer with unequal fibers, and the mutual
information and the largest entropy of the null-record proposition.

Relation: none; the statements concern functions on sets, permutations and finite sums.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObserverFoundations

universe u

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! ## Remark `cor:single`: the least set with a separating test -/

/-- Every set with a separating test has two distinct points, and the two-element set of Boolean
values has one, so the least set with a separating test has two elements. -/
theorem least_separating_set :
    (∀ (X : Type*) (f : X → Bool) (x y : X), f x ≠ f y → x ≠ y) ∧
      Nat.card Bool = 2 ∧ ∃ f : Bool → Bool, f false ≠ f true := by
  refine ⟨fun _ f x y h hxy => h (hxy ▸ rfl), by simp, ⟨id, by decide⟩⟩

/-! ## Remark `prop:continuous-place-obstruction`: continuous discrete maps are constant -/

/-- On a preconnected space every continuous map to a discrete space is constant, so it takes one
value at the two states of every merged pair. -/
theorem continuous_discrete_const {X S : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace S] [DiscreteTopology S] (s : X → S) (hs : Continuous s) (x y : X) :
    s x = s y :=
  PreconnectedSpace.constant ‹_› hs

/-! ## Proposition `prop:tables`: tables of comparisons -/

/-- A reflexive and symmetric table of comparisons is the kernel of an observer if and only if it
is transitive. -/
theorem table_is_kernel_iff {X : Type u} (T : X → X → Prop) (hrefl : ∀ x, T x x)
    (hsymm : ∀ x y, T x y → T y x) :
    (∃ (Q : Type u) (q : X → Q), ∀ x y, T x y ↔ q x = q y) ↔
      ∀ x y z, T x y → T y z → T x z := by
  constructor
  · rintro ⟨Q, q, hq⟩ x y z hxy hyz
    exact (hq x z).2 (((hq x y).1 hxy).trans ((hq y z).1 hyz))
  · intro htrans
    let s : Setoid X := ⟨T, ⟨hrefl, fun h => hsymm _ _ h, fun h h' => htrans _ _ _ h h'⟩⟩
    exact ⟨Quotient s, Quotient.mk s, fun x y => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩⟩

/-- A transitive reflexive and symmetric table is the kernel of its quotient map. -/
theorem table_kernel_of_quotient {X : Type*} (T : X → X → Prop) (hrefl : ∀ x, T x x)
    (hsymm : ∀ x y, T x y → T y x) (htrans : ∀ x y z, T x y → T y z → T x z) :
    ∀ x y, T x y ↔
      Quotient.mk (⟨T, ⟨hrefl, fun h => hsymm _ _ h, fun h h' => htrans _ _ _ h h'⟩⟩ : Setoid X) x =
        Quotient.mk (⟨T, ⟨hrefl, fun h => hsymm _ _ h, fun h h' => htrans _ _ _ h h'⟩⟩ : Setoid X)
          y :=
  fun _ _ => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- The observer `q` determines the target `P` when `P` has one value at any two states with one
record. -/
def DeterminesTarget {X Y V : Type*} (q : X → Y) (P : X → V) : Prop :=
  ∀ x y, q x = q y → P x = P y

/-- For a set `V`, `q` determines every target with values in `V` that `q'` determines if and
only if `V` has at most one element or the kernel of `q` is contained in the kernel of `q'`. -/
theorem determines_all_targets_iff {X Y Y' V : Type*} (q : X → Y) (q' : X → Y') :
    (∀ P : X → V, DeterminesTarget q' P → DeterminesTarget q P) ↔
      Subsingleton V ∨ ∀ x y, q x = q y → q' x = q' y := by
  classical
  constructor
  · intro h
    by_cases hV : Subsingleton V
    · exact Or.inl hV
    · right
      obtain ⟨v₀, v₁, hv⟩ := not_subsingleton_iff_nontrivial.1 hV |>.exists_pair_ne
      intro x y hxy
      let P : X → V := fun z => if q' z = q' x then v₀ else v₁
      have hP : DeterminesTarget q' P := fun a b hab => by simp only [P, hab]
      have hxy' := h P hP x y hxy
      simp only [P, if_pos rfl] at hxy'
      by_contra hne
      rw [if_neg (Ne.symm hne)] at hxy'
      exact hv hxy'
  · rintro (hV | hk) P hP x y hxy
    · exact Subsingleton.elim _ _
    · exact hP x y (hk x y hxy)

/-- The kernel of `q` is contained in the kernel of `q'` if and only if `q` determines every test
that `q'` determines. -/
theorem kernel_le_iff_tests {X Y Y' : Type*} (q : X → Y) (q' : X → Y') :
    (∀ x y, q x = q y → q' x = q' y) ↔
      ∀ f : X → Bool, DeterminesTarget q' f → DeterminesTarget q f := by
  rw [determines_all_targets_iff]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · exact absurd (Subsingleton.elim true false) (by decide)
    · exact h

/-- The containment of kernels is strict if and only if the inclusion of the sets of determined
tests is strict. -/
theorem kernel_lt_iff_tests {X Y Y' : Type*} (q : X → Y) (q' : X → Y') :
    ((∀ x y, q x = q y → q' x = q' y) ∧ ¬ ∀ x y, q' x = q' y → q x = q y) ↔
      ((∀ f : X → Bool, DeterminesTarget q' f → DeterminesTarget q f) ∧
        ¬ ∀ f : X → Bool, DeterminesTarget q f → DeterminesTarget q' f) := by
  rw [kernel_le_iff_tests q q', kernel_le_iff_tests q' q]

/-- Two observers determine the same tests if and only if they have the same kernel. -/
theorem same_tests_iff_same_kernel {X Y Y' : Type*} (q : X → Y) (q' : X → Y') :
    (∀ f : X → Bool, DeterminesTarget q f ↔ DeterminesTarget q' f) ↔
      ∀ x y, q x = q y ↔ q' x = q' y := by
  constructor
  · intro h x y
    exact ⟨(kernel_le_iff_tests q q').2 (fun f hf => (h f).2 hf) x y,
      (kernel_le_iff_tests q' q).2 (fun f hf => (h f).1 hf) x y⟩
  · intro h f
    exact ⟨fun hf a b hab => hf a b ((h a b).2 hab), fun hf a b hab => hf a b ((h a b).1 hab)⟩

/-- The kernel of `q` is the relation under which every test that `q` determines has one value at
the two states. -/
theorem kernel_eq_determined_tests_agreement {X Y : Type*} (q : X → Y) (x y : X) :
    q x = q y ↔ ∀ f : X → Bool, DeterminesTarget q f → f x = f y := by
  classical
  constructor
  · intro h f hf
    exact hf x y h
  · intro h
    have hf : DeterminesTarget q (fun z => decide (q z = q x)) := fun a b hab => by
      simp only [hab]
    have := h _ hf
    simp only [decide_true] at this
    exact (of_decide_eq_true this.symm).symm

/-- The apartness of an observer is irreflexive and symmetric, and two apart states have every
third state apart from one of them. -/
theorem apartness_properties {X Y : Type*} (q : X → Y) :
    (∀ x, ¬ q x ≠ q x) ∧ (∀ x y, q x ≠ q y → q y ≠ q x) ∧
      ∀ x y z, q x ≠ q y → q x ≠ q z ∨ q z ≠ q y := by
  refine ⟨fun x h => h rfl, fun x y h => Ne.symm h, fun x y z h => ?_⟩
  by_cases hxz : q x = q z
  · exact Or.inr (fun hzy => h (hxz.trans hzy))
  · exact Or.inl hxz

/-- A set `F` of tests is the set of tests determined by one observer if and only if it contains
every test that has one value at any two states at which every member of `F` has one value. -/
theorem determined_tests_iff_closed {X : Type u} (F : Set (X → Bool)) :
    (∃ (Q : Type u) (q : X → Q), F = {f | DeterminesTarget q f}) ↔
      ∀ f : X → Bool, (∀ x y, (∀ g ∈ F, g x = g y) → f x = f y) → f ∈ F := by
  constructor
  · rintro ⟨Q, q, rfl⟩ f hf x y hxy
    exact hf x y (fun g hg => hg x y hxy)
  · intro hcl
    refine ⟨F → Bool, fun x g => g.1 x, Set.ext fun f => ⟨fun hf x y hxy => ?_, fun hf => ?_⟩⟩
    · exact congrFun hxy ⟨f, hf⟩
    · apply hcl f
      intro x y hxy
      exact hf x y (funext fun g => hxy g.1 g.2)

/-! ## Theorem `thm:unique-attained-image`: surjective observers -/

/-- Two surjective observers have one kernel if and only if there is a unique bijection of their
codomains that commutes with the two projections. -/
theorem same_kernel_iff_unique_equiv_of_surjective {X Y₁ Y₂ : Type*} (q₁ : X → Y₁)
    (q₂ : X → Y₂) (h₁ : Function.Surjective q₁) (h₂ : Function.Surjective q₂) :
    (∀ x y, q₁ x = q₁ y ↔ q₂ x = q₂ y) ↔ ∃! e : Y₁ ≃ Y₂, ∀ x, e (q₁ x) = q₂ x := by
  constructor
  · intro hk
    let f : Y₁ → Y₂ := fun y => q₂ (Function.surjInv h₁ y)
    let g : Y₂ → Y₁ := fun y => q₁ (Function.surjInv h₂ y)
    have hf : ∀ x, f (q₁ x) = q₂ x := fun x =>
      (hk _ _).1 (Function.surjInv_eq h₁ (q₁ x))
    have hg : ∀ x, g (q₂ x) = q₁ x := fun x =>
      (hk _ _).2 (Function.surjInv_eq h₂ (q₂ x))
    refine ⟨⟨f, g, ?_, ?_⟩, hf, ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := h₁ y
      rw [hf, hg]
    · intro y
      obtain ⟨x, rfl⟩ := h₂ y
      rw [hg, hf]
    · intro e he
      ext y
      obtain ⟨x, rfl⟩ := h₁ y
      rw [he x]
      exact (hf x).symm
  · rintro ⟨e, he, -⟩ x y
    rw [← he x, ← he y]
    exact e.injective.eq_iff.symm

/-! ## Theorem `thm:pair`(3): the invariant relations of a merged pair -/

/-- The binary relations on a two-element set `{x₀, x₁}` invariant under the transposition are
exactly the empty relation, the diagonal, its complement and the full relation. -/
theorem swap_invariant_relations_four {X : Type*} [DecidableEq X] {x₀ x₁ : X} (hne : x₀ ≠ x₁)
    (R : X → X → Prop) :
    (∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        (R (Equiv.swap x₀ x₁ a) (Equiv.swap x₀ x₁ b) ↔ R a b)) ↔
      ((∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X), ¬ R a b) ∨
        (∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X), (R a b ↔ a = b)) ∨
        (∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X), (R a b ↔ a ≠ b)) ∨
        (∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X), R a b)) := by
  rw [MergedPair.swap_invariant_relation_iff]
  have hne' : x₁ ≠ x₀ := Ne.symm hne
  constructor
  · rintro ⟨hd, ho⟩
    by_cases h00 : R x₀ x₀ <;> by_cases h01 : R x₀ x₁
    · right; right; right
      intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact h00
      · exact h01
      · exact ho.1 h01
      · exact hd.1 h00
    · right; left
      intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ⟨fun _ => rfl, fun _ => h00⟩
      · exact ⟨fun h => absurd h h01, fun h => absurd h hne⟩
      · exact ⟨fun h => absurd (ho.2 h) h01, fun h => absurd h hne'⟩
      · exact ⟨fun _ => rfl, fun _ => hd.1 h00⟩
    · right; right; left
      intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ⟨fun h => absurd h h00, fun h => absurd rfl h⟩
      · exact ⟨fun _ => hne, fun _ => h01⟩
      · exact ⟨fun _ => hne', fun _ => ho.1 h01⟩
      · exact ⟨fun h => absurd (hd.2 h) h00, fun h => absurd rfl h⟩
    · left
      intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact h00
      · exact h01
      · exact fun h => h01 (ho.2 h)
      · exact fun h => h00 (hd.2 h)
  · have h0 : x₀ ∈ ({x₀, x₁} : Set X) := Or.inl rfl
    have h1 : x₁ ∈ ({x₀, x₁} : Set X) := Or.inr rfl
    rintro (h | h | h | h)
    · exact ⟨⟨fun r => absurd r (h _ h0 _ h0), fun r => absurd r (h _ h1 _ h1)⟩,
        ⟨fun r => absurd r (h _ h0 _ h1), fun r => absurd r (h _ h1 _ h0)⟩⟩
    · exact ⟨⟨fun _ => (h _ h1 _ h1).2 rfl, fun _ => (h _ h0 _ h0).2 rfl⟩,
        ⟨fun r => absurd ((h _ h0 _ h1).1 r) hne, fun r => absurd ((h _ h1 _ h0).1 r) hne'⟩⟩
    · exact ⟨⟨fun r => absurd rfl ((h _ h0 _ h0).1 r), fun r => absurd rfl ((h _ h1 _ h1).1 r)⟩,
        ⟨fun _ => (h _ h1 _ h0).2 hne', fun _ => (h _ h0 _ h1).2 hne⟩⟩
    · exact ⟨⟨fun _ => h _ h1 _ h1, fun _ => h _ h0 _ h0⟩, ⟨fun _ => h _ h1 _ h0, fun _ => h _ h0 _ h1⟩⟩

/-! ## Proposition `prop:self-test`: orbits, invariant tests and the law of the indicator -/

/-- A test is constant off `x` if and only if it factors through the indicator of `x`. -/
theorem const_off_iff_factors {C : Type*} [DecidableEq C] (x : C) (f : C → Bool) :
    (∀ a b, a ≠ x → b ≠ x → f a = f b) ↔
      ∃ g : Bool → Bool, ∀ c, f c = g (decide (c = x)) := by
  constructor
  · intro h
    by_cases hex : ∃ c, c ≠ x
    · obtain ⟨c₀, hc₀⟩ := hex
      refine ⟨fun b => if b then f x else f c₀, fun c => ?_⟩
      by_cases hc : c = x
      · simp [hc]
      · simp [hc, h c c₀ hc hc₀]
    · push_neg at hex
      exact ⟨fun _ => f x, fun c => by rw [hex c]⟩
  · rintro ⟨g, hg⟩ a b ha hb
    rw [hg a, hg b, decide_eq_false ha, decide_eq_false hb]

/-- The orbits of the permutations that fix `x`: two states lie in one orbit if and only if both
are `x` or neither is. -/
theorem point_stabilizer_orbits {C : Type*} [DecidableEq C] (x c d : C) :
    (∃ σ : Equiv.Perm C, σ x = x ∧ σ c = d) ↔ (c = x ↔ d = x) := by
  constructor
  · rintro ⟨σ, hσx, rfl⟩
    constructor
    · rintro rfl
      exact hσx
    · intro h
      exact σ.injective (h.trans hσx.symm)
  · intro h
    by_cases hc : c = x
    · subst hc
      exact ⟨1, rfl, (h.1 rfl).symm⟩
    · have hd : d ≠ x := fun hd => hc (h.2 hd)
      refine ⟨Equiv.swap c d, ?_, Equiv.swap_apply_left c d⟩
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hd)

/-- The tests invariant under the permutations that fix `x`. -/
def invariantTests {C : Type*} (x : C) : Set (C → Bool) :=
  {f | ∀ σ : Equiv.Perm C, σ x = x → ∀ c, f (σ c) = f c}

/-- The invariant tests are the tests that factor through the indicator of `x`. -/
theorem invariantTests_eq_range {C : Type*} [DecidableEq C] (x : C) :
    invariantTests x = Set.range (fun g : Bool → Bool => fun c => g (decide (c = x))) := by
  ext f
  change (∀ σ : Equiv.Perm C, σ x = x → ∀ c, f (σ c) = f c) ↔ _
  rw [PairInvariants.point_stabilizer_invariant_iff, const_off_iff_factors]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, funext fun c => (hg c).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun _ => rfl⟩

/-- There are four distinct invariant tests when some state differs from `x`. -/
theorem invariantTests_card_four {C : Type*} [DecidableEq C] (x : C) (h : ∃ c, c ≠ x) :
    Nat.card (invariantTests x) = 4 := by
  obtain ⟨c₀, hc₀⟩ := h
  rw [invariantTests_eq_range]
  have hinj : Function.Injective (fun g : Bool → Bool => fun c : C => g (decide (c = x))) := by
    intro g g' hgg
    funext b
    cases b
    · have := congrFun hgg c₀
      simpa [hc₀] using this
    · have := congrFun hgg x
      simpa using this
  rw [Nat.card_range_of_injective hinj, Nat.card_fun]
  simp

/-- There are two invariant tests when `x` is the only state. -/
theorem invariantTests_card_two {C : Type*} [DecidableEq C] (x : C) (h : ∀ c, c = x) :
    Nat.card (invariantTests x) = 2 := by
  rw [invariantTests_eq_range]
  have hrange : Set.range (fun g : Bool → Bool => fun c : C => g (decide (c = x))) =
      Set.range (fun b : Bool => fun _ : C => b) := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g true, funext fun c => by simp [h c]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨fun _ => b, rfl⟩
  have hinj : Function.Injective (fun b : Bool => fun _ : C => b) :=
    fun b b' hbb => congrFun hbb x
  rw [hrange, Nat.card_range_of_injective hinj]
  simp

/-- The law of the indicator of one state of a uniform `n`-element set: mass `1 / n` at the value
one and `1 - 1 / n` at the value zero. -/
noncomputable def selfTestLaw (n : ℕ) (b : Bool) : ℝ := if b then 1 / n else 1 - 1 / n

/-- The indicator of `x` pushes the uniform law of `C` forward to `selfTestLaw`. -/
theorem selfTest_pushforward {C : Type*} [Fintype C] [DecidableEq C] (x : C) (b : Bool) :
    ∑ c, (if decide (c = x) = b then (1 : ℝ) / Fintype.card C else 0) =
      selfTestLaw (Fintype.card C) b := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos_iff.2 ⟨x⟩
  cases b
  · have hcard : (Finset.univ.filter (fun c : C => decide (c = x) = false)).card =
        Fintype.card C - 1 := by
      have : (Finset.univ.filter (fun c : C => decide (c = x) = false)) =
          Finset.univ.erase x := by
        ext c
        simp
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    rw [hcard, selfTestLaw]
    have h1 : 1 ≤ Fintype.card C := Fintype.card_pos_iff.2 ⟨x⟩
    simp only [Bool.false_eq_true, if_false]
    rw [Nat.cast_sub h1]
    field_simp
  · have hcard : (Finset.univ.filter (fun c : C => decide (c = x) = true)).card = 1 := by
      have : (Finset.univ.filter (fun c : C => decide (c = x) = true)) = {x} := by
        ext c
        simp
      rw [this, Finset.card_singleton]
    rw [hcard, selfTestLaw]
    simp

/-- Under the uniform law the entropy of the indicator of one state is the binary entropy of
`1 / n`. -/
theorem selfTest_entropy (n : ℕ) :
    BitDivision.entropy (selfTestLaw n) = Real.binEntropy (1 / n) := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold BitDivision.entropy
  rw [Fintype.sum_bool]
  simp [selfTestLaw]

/-! ## Theorem `thm:place`: resolving coordinates -/

open OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates

/-- With finite fibers of size at most `m` and a fiber of size `m`, the least size of a resolving
coordinate is `m`, the largest fiber size. -/
theorem least_resolving_size {X Q : Type*} (q : X → Q) (m : ℕ)
    (hfin : ∀ y, (q ⁻¹' {y}).Finite) (hle : ∀ y, (q ⁻¹' {y}).ncard ≤ m)
    (hatt : ∃ y, (q ⁻¹' {y}).ncard = m) :
    IsLeast {n | ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))} m := by
  refine ⟨(exists_place_coordinate_iff q m).2 fun y => ⟨hfin y, hle y⟩, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hatt
  rw [← hy]
  exact ((exists_place_coordinate_iff q n).1 hn y).2

/-- On the empty state set the least size of a resolving coordinate is zero. -/
theorem least_resolving_size_empty {X Q : Type*} [IsEmpty X] (q : X → Q) :
    IsLeast {n | ∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))} 0 :=
  ⟨⟨isEmptyElim, fun a => isEmptyElim a⟩, fun n _ => Nat.zero_le n⟩

/-- A coordinate bijective on each fiber onto `Fin n` exists if and only if every fiber has `n`
states, with no finiteness hypothesis: an infinite fiber has infinite cardinality and admits no
such bijection. -/
theorem placeCoord_nonempty_iff_encard {X Q : Type*} (q : X → Q) (n : ℕ) :
    (PlaceCoord q n).Nonempty ↔ ∀ y ∈ Set.range q, (q ⁻¹' {y}).encard = n := by
  by_cases hfin : ∀ y ∈ Set.range q, (q ⁻¹' {y}).Finite
  · rw [PlaceExistence.placeExistenceGoal q n hfin]
    constructor
    · intro h y hy
      rw [← (hfin y hy).cast_ncard_eq, h y hy]
    · intro h y hy
      have := h y hy
      rw [← (hfin y hy).cast_ncard_eq] at this
      exact_mod_cast this
  · push_neg at hfin
    obtain ⟨y, hy, hinf⟩ := hfin
    constructor
    · rintro ⟨p, hp⟩
      exact absurd ((hp y hy).finite_iff_finite.2 Set.finite_univ) hinf
    · intro h
      have := h y hy
      rw [Set.encard_eq_top_iff.2 hinf] at this
      exact absurd this (ENat.top_ne_coe n)

/-- The observer with unequal fibers of Theorem `thm:place`(iii): `q a = q b = 0` and `q c = 1`. -/
def unequalFibers : Fin 3 → Bool := ![false, false, true]

/-- The observer with unequal fibers has exactly four resolving coordinates with two values. -/
theorem unequalFibers_resolving_card :
    (Finset.univ.filter (fun p : Fin 3 → Fin 2 =>
      Function.Injective (fun x => (unequalFibers x, p x)))).card = 4 := by
  decide

/-- Every record-preserving permutation of the observer with unequal fibers fixes `c`. -/
theorem unequalFibers_stabilizer_fixes (σ : Equiv.Perm (Fin 3))
    (hσ : σ ∈ licenseStabilizer unequalFibers) : σ 2 = 2 := by
  have h : unequalFibers (σ 2) = unequalFibers 2 := hσ 2
  revert h
  generalize σ 2 = k
  revert k
  decide

/-- The transposition of `a` and `b` preserves the record of the observer with unequal fibers. -/
theorem unequalFibers_swap_mem : Equiv.swap (0 : Fin 3) 1 ∈ licenseStabilizer unequalFibers := by
  intro x
  revert x
  decide

/-- Two resolving coordinates with two values of the observer with unequal fibers lie in one orbit
of the record-preserving permutations if and only if they agree at `c`; the coordinates with the
value zero at `c` and those with the value one at `c` form the two orbits. -/
theorem unequalFibers_orbits (p p' : Fin 3 → Fin 2)
    (hp : Function.Injective (fun x => (unequalFibers x, p x)))
    (hp' : Function.Injective (fun x => (unequalFibers x, p' x))) :
    (∃ σ ∈ licenseStabilizer unequalFibers, p' = p ∘ σ.symm) ↔ p 2 = p' 2 := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hfix : σ.symm 2 = 2 := by
      have := unequalFibers_stabilizer_fixes σ hσ
      rw [Equiv.symm_apply_eq]
      exact this.symm
    simp [hfix]
  · intro h2
    have h01 : p 0 ≠ p 1 := fun h => by
      have := hp (a₁ := 0) (a₂ := 1) (by simp [unequalFibers, h])
      exact absurd this (by decide)
    have h01' : p' 0 ≠ p' 1 := fun h => by
      have := hp' (a₁ := 0) (a₂ := 1) (by simp [unequalFibers, h])
      exact absurd this (by decide)
    have hvals : ∀ u v : Fin 2, u ≠ v → ∀ u' v' : Fin 2, u' ≠ v' →
        (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by decide
    rcases hvals _ _ h01 _ _ h01' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine ⟨1, Subgroup.one_mem _, funext fun x => ?_⟩
      fin_cases x
      · exact ha
      · exact hb
      · exact h2.symm
    · refine ⟨Equiv.swap 0 1, unequalFibers_swap_mem, funext fun x => ?_⟩
      fin_cases x
      · simpa [Equiv.swap_apply_left] using ha
      · simpa [Equiv.swap_apply_right] using hb
      · simp only [Function.comp_apply]
        exact h2.symm

/-- Resolving coordinates with both values at `c` exist, so the two orbits are nonempty. -/
theorem unequalFibers_two_orbits_nonempty :
    ∃ p p' : Fin 3 → Fin 2, Function.Injective (fun x => (unequalFibers x, p x)) ∧
      Function.Injective (fun x => (unequalFibers x, p' x)) ∧ p 2 = 0 ∧ p' 2 = 1 := by
  refine ⟨![0, 1, 0], ![0, 1, 1], ?_, ?_, rfl, rfl⟩ <;> decide

/-! ## Proposition `prop:null`: mutual information and the largest entropy -/

open OperatorKO7.Meta.BoundaryObserver.BitDivision

/-- Under the uniform law on a finite set, the mutual information of the state and its record,
`H(x) + H(q(x)) - H(x, q(x))`, is `log n - H(x | q(x))`, with `log n` the entropy of the uniform
law. -/
theorem uniform_mutualInfo_eq {X Q : Type*} [Fintype X] [Nonempty X] (q : X → Q) :
    entropy (fun _ : X => (1 : ℝ) / Fintype.card X) + attainedUniformRecordEntropy q -
        attainedUniformRecordEntropy (fun x : X => (x, q x)) =
      Real.log (Fintype.card X) - attainedUniformConditionalEntropy q := by
  rw [attainedUniformJointEntropy_eq_state, attainedUniformConditionalEntropy, entropy_uniform]
  ring

/-- On `X × {0, 1}` the largest entropy is `log n + log 2`: every probability law has at most this
entropy, and the uniform law attains it. -/
theorem pair_system_largest_entropy (X : Type) [Fintype X] [Nonempty X] :
    (∀ m : X × Bool → ℝ, (∀ z, 0 ≤ m z) → ∑ z, m z = 1 →
        entropy m ≤ Real.log (Fintype.card X) + Real.log 2) ∧
      entropy (fun _ : X × Bool => (1 : ℝ) / Fintype.card (X × Bool)) =
        Real.log (Fintype.card X) + Real.log 2 := by
  refine ⟨fun m hm0 hm1 => ?_, ?_⟩
  · rw [entropy_eq_H, ← pair_system_log_card X]
    exact OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.H_le_log_card m hm0 hm1
  · rw [entropy_uniform, pair_system_log_card]

end OperatorKO7.Meta.BoundaryObserver.ObserverFoundations
