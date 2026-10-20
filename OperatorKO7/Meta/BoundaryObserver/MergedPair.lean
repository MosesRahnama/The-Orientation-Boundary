import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

set_option autoImplicit false

/-!
# The structure of a merged pair

An observer is a map `q : X → Q`. A merged pair of `q` is a pair of distinct states with one
record. This module states, for every observer and every merged pair, the clauses of the
structure theorem of the observation-principle manuscript (Theorem 4.1(1) to (6)), together with
the results of its Section 2 on kernels and apartness and Propositions 4.7 and 4.8. Clause (7) of
Theorem 4.1 is in `BitDivision.lean`.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M1.

Relation: none; the statements are about maps, permutations and relations on arbitrary types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.

STATEMENT CHANGE against the plan file `OBSERVATION-PRINCIPLE-LEAN-ROADMAP.md`, both
strengthenings by removal of a hypothesis that the proof does not consume:
* `swap_invariant_relation_iff` holds without `x₀ ≠ x₁`;
* `mergedPair_comparison_decoder` holds for every observer once `s x₀ ≠ s x₁`, which already
  gives `x₀ ≠ x₁`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.MergedPair

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

/-! ## Observers, merged pairs, boundary -/

/-- The observer `q` determines the target `P`: states with one record have one target value.
This is `Licensed` of the observer paper under the manuscript's verb. -/
abbrev Determines {X Q V : Type*} (q : X → Q) (P : X → V) : Prop := Licensed q P

/-- A merged pair of `q`: two distinct states with one record (Definition 2.1). -/
def IsMergedPair {X Q : Type*} (q : X → Q) (x₀ x₁ : X) : Prop := x₀ ≠ x₁ ∧ q x₀ = q x₁

/-- The boundary of `q`: the set of its merged pairs (Definition 2.5). -/
def boundary {X Q : Type*} (q : X → Q) : Set (X × X) := {p | IsMergedPair q p.1 p.2}

/-- Non-vacuity: the two points of `Bool` are a merged pair of the constant observer. -/
theorem isMergedPair_bool_const : IsMergedPair (fun _ : Bool => ()) false true :=
  ⟨Bool.false_ne_true, rfl⟩

/-! ## Lemma 2.3: determination, collisions, invariance -/

/-- Lemma 2.3(i): `q` determines `P` if and only if `q` has no collision for `P`. -/
theorem determines_iff_no_collision {X Q V : Type*} (q : X → Q) (P : X → V) :
    Determines q P ↔ ¬ ∃ x x', q x = q x' ∧ P x ≠ P x' := by
  constructor
  · rintro h ⟨x, x', hq, hP⟩
    exact hP (h x x' hq)
  · intro h x x' hq
    by_contra hP
    exact h ⟨x, x', hq, hP⟩

/-- Lemma 2.3(ii): `q` determines `P` if and only if `P` is invariant under every permutation
that keeps every record. -/
theorem determines_iff_invariant {X Q V : Type*} (q : X → Q) (P : X → V) :
    Determines q P ↔ ∀ σ ∈ licenseStabilizer q, ∀ x, P (σ x) = P x := by
  classical
  constructor
  · intro h σ hσ x
    exact h (σ x) x (hσ x)
  · intro h x y hxy
    have hP := h (observerSwap x y) (swap_mem_licenseStabilizer_of_eq q hxy) x
    simp only [observerSwap, Equiv.swap_apply_left] at hP
    exact hP.symm

/-- Lemma 2.3(iii): two states have one record if and only if a permutation that keeps every
record maps one to the other. -/
theorem same_record_iff_orbit {X Q : Type*} (q : X → Q) (x y : X) :
    q x = q y ↔ ∃ σ ∈ licenseStabilizer q, σ x = y := by
  classical
  constructor
  · intro h
    exact ⟨observerSwap x y, swap_mem_licenseStabilizer_of_eq q h, by simp [observerSwap]⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (hσ x).symm

/-- Lemma 2.3(iv): `q` determines the identity if and only if `q` is injective. -/
theorem determines_id_iff_injective {X Q : Type*} (q : X → Q) :
    Determines q (id : X → X) ↔ Function.Injective q :=
  licensed_identity_iff_injective q

/-! ## Proposition 2.4: tables of comparisons -/

/-- Proposition 2.4(ii): for a reflexive symmetric table `T`, the transitive closure is an
equivalence relation, and every observer that agrees with each entry of `T` agrees with each
entry of the closure. The closure is therefore the least kernel that contains `T`. -/
theorem transGen_least_kernel {X : Type*} (T : X → X → Prop)
    (hrefl : ∀ x, T x x) (hsymm : ∀ x y, T x y → T y x) :
    Equivalence (Relation.TransGen T) ∧
      ∀ {Q : Type*} (q : X → Q), (∀ x y, T x y → q x = q y) →
        ∀ x y, Relation.TransGen T x y → q x = q y := by
  refine ⟨⟨fun x => Relation.TransGen.single (hrefl x), ?_, fun h₁ h₂ => h₁.trans h₂⟩, ?_⟩
  · intro x y h
    induction h with
    | single h => exact Relation.TransGen.single (hsymm _ _ h)
    | tail _ h ih => exact Relation.TransGen.head (hsymm _ _ h) ih
  · intro Q q hq x y h
    induction h with
    | single h => exact hq _ _ h
    | tail _ h ih => exact ih.trans (hq _ _ h)

/-- Proposition 2.4(iv), first half: difference of records is irreflexive, symmetric and
cotransitive. -/
theorem apart_irrefl_symm_cotrans {X Q : Type*} (q : X → Q) :
    (∀ x, ¬ q x ≠ q x) ∧ (∀ x y, q x ≠ q y → q y ≠ q x) ∧
      (∀ x y z, q x ≠ q y → q x ≠ q z ∨ q z ≠ q y) := by
  refine ⟨fun x h => h rfl, fun x y h => h.symm, ?_⟩
  intro x y z h
  by_contra hcon
  push_neg at hcon
  exact h (hcon.1.trans hcon.2)

/-- Proposition 2.4(iv), second half: every irreflexive, symmetric, cotransitive relation is the
complement of an equivalence relation, hence of the kernel of its quotient map. -/
theorem apartness_is_kernel_complement {X : Type*} (A : X → X → Prop)
    (hirr : ∀ x, ¬ A x x) (hsymm : ∀ x y, A x y → A y x)
    (hcot : ∀ x y z, A x y → A x z ∨ A z y) :
    ∃ s : Setoid X, ∀ x y, A x y ↔ ¬ s.r x y := by
  refine ⟨⟨fun x y => ¬ A x y, ⟨hirr, ?_, ?_⟩⟩, ?_⟩
  · intro x y h hyx
    exact h (hsymm _ _ hyx)
  · intro x y z hxy hyz hxz
    rcases hcot x z y hxz with h | h
    · exact hxy h
    · exact hyz h
  · intro x y
    exact not_not.symm

/-- Definition 2.5 with the remark after it: the boundary is empty if and only if the observer
is injective. -/
theorem boundary_eq_empty_iff_injective {X Q : Type*} (q : X → Q) :
    boundary q = ∅ ↔ Function.Injective q := by
  constructor
  · intro h x y hxy
    by_contra hne
    have hmem : (x, y) ∈ boundary q := ⟨hne, hxy⟩
    rw [h] at hmem
    exact (Set.mem_empty_iff_false _).1 hmem
  · intro h
    ext ⟨x, y⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hne, hxy⟩
    exact hne (h hxy)

/-! ## Theorem 4.1: the structure of a merged pair -/

/--
Theorem 4.1(1), tests through the record.

Proves: every Boolean test determined by `q` has one value on a merged pair of `q`.
Does not prove: anything about tests that `q` does not determine.
Relation: none. Trust: kernel-only.
-/
theorem mergedPair_tests_through_record {X Q : Type*} {q : X → Q} {x₀ x₁ : X}
    (h : IsMergedPair q x₀ x₁) (f : X → Bool) (hf : Determines q f) : f x₀ = f x₁ :=
  hf x₀ x₁ h.2

/--
Theorem 4.1(2), separating tests.

Proves: for two distinct points, a Boolean map that separates them agrees on the pair with the
indicator of one of the two points; the two indicators are negations of each other on the pair;
the transposition maps one indicator to the other; a Boolean map is unchanged by the
transposition if and only if it has one value on the pair.
Does not prove: any statement about maps outside the pair.
Relation: none. Trust: kernel-only.
-/
theorem mergedPair_separating_tests {X : Type*} [DecidableEq X] {x₀ x₁ : X} (hne : x₀ ≠ x₁) :
    (∀ f : X → Bool, f x₀ ≠ f x₁ →
        (f x₀ = decide (x₀ = x₀) ∧ f x₁ = decide (x₁ = x₀)) ∨
          (f x₀ = decide (x₀ = x₁) ∧ f x₁ = decide (x₁ = x₁))) ∧
      (∀ a ∈ ({x₀, x₁} : Set X), decide (a = x₁) = !decide (a = x₀)) ∧
      (∀ a : X, decide (Equiv.swap x₀ x₁ a = x₀) = decide (a = x₁)) ∧
      (∀ f : X → Bool, (∀ a, f (Equiv.swap x₀ x₁ a) = f a) ↔ f x₀ = f x₁) := by
  have h01 : decide (x₀ = x₁) = false := decide_eq_false hne
  have h10 : decide (x₁ = x₀) = false := decide_eq_false hne.symm
  have h00 : decide (x₀ = x₀) = true := decide_eq_true rfl
  have h11 : decide (x₁ = x₁) = true := decide_eq_true rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [h00, h10, h01, h11]
    cases hp : f x₀ <;> cases hq : f x₁ <;> simp_all
  · intro a ha
    have ha' : a = x₀ ∨ a = x₁ := ha
    rcases ha' with ha' | ha'
    · rw [ha', h01, h00]
      rfl
    · rw [ha', h11, h10]
      rfl
  · intro a
    by_cases ha : a = x₁
    · rw [ha, Equiv.swap_apply_right, h00, h11]
    · have hsw : Equiv.swap x₀ x₁ a ≠ x₀ := by
        intro h
        apply ha
        have h' := congrArg (Equiv.swap x₀ x₁) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
      rw [decide_eq_false hsw, decide_eq_false ha]
  · intro f
    constructor
    · intro h
      have hx := h x₀
      simpa only [Equiv.swap_apply_left] using hx.symm
    · intro hf a
      by_cases ha : a = x₀
      · subst a
        simpa only [Equiv.swap_apply_left] using hf.symm
      · by_cases hb : a = x₁
        · subst a
          simpa only [Equiv.swap_apply_right] using hf
        · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Theorem 4.1(3), invariant relations: a relation on the pair is invariant under the
transposition if and only if it has one value on the diagonal and one value off it. The invariant
relations are therefore the empty relation, the diagonal, its complement and the full
relation. -/
theorem swap_invariant_relation_iff {X : Type*} [DecidableEq X] {x₀ x₁ : X}
    (R : X → X → Prop) :
    (∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        (R (Equiv.swap x₀ x₁ a) (Equiv.swap x₀ x₁ b) ↔ R a b)) ↔
      ((R x₀ x₀ ↔ R x₁ x₁) ∧ (R x₀ x₁ ↔ R x₁ x₀)) := by
  have m0 : x₀ ∈ ({x₀, x₁} : Set X) := Set.mem_insert _ _
  have m1 : x₁ ∈ ({x₀, x₁} : Set X) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  constructor
  · intro h
    have h00 := h x₀ m0 x₀ m0
    have h01 := h x₀ m0 x₁ m1
    rw [Equiv.swap_apply_left] at h00
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at h01
    exact ⟨h00.symm, h01.symm⟩
  · rintro ⟨hd, ho⟩ a ha b hb
    have ha' : a = x₀ ∨ a = x₁ := ha
    have hb' : b = x₀ ∨ b = x₁ := hb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb']
    · rw [Equiv.swap_apply_left]
      exact hd.symm
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact ho.symm
    · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      exact ho
    · rw [Equiv.swap_apply_right]
      exact hd

/-- Theorem 4.1(3): the relation "distinct" is invariant under the transposition. -/
theorem distinct_swap_invariant {X : Type*} [DecidableEq X] (x₀ x₁ a b : X) :
    Equiv.swap x₀ x₁ a ≠ Equiv.swap x₀ x₁ b ↔ a ≠ b :=
  (Equiv.swap x₀ x₁).injective.ne_iff

/--
Theorem 4.1(3), last sentence.

Proves: on a pair of distinct points, no combination `g` of the values of tests that are
invariant under the transposition equals the relation "distinct".
Does not prove: any statement about tests that the transposition changes.
Relation: none. Trust: kernel-only.
-/
theorem distinct_not_from_invariant_tests {X : Type*} [DecidableEq X] {x₀ x₁ : X} (hne : x₀ ≠ x₁)
    {ι : Type*} (f : ι → X → Bool) (hf : ∀ i a, f i (Equiv.swap x₀ x₁ a) = f i a)
    (g : (ι → Bool) → (ι → Bool) → Prop) :
    ¬ ∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        (g (fun i => f i a) (fun i => f i b) ↔ a ≠ b) := by
  intro h
  have m0 : x₀ ∈ ({x₀, x₁} : Set X) := Set.mem_insert _ _
  have m1 : x₁ ∈ ({x₀, x₁} : Set X) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hconst : (fun i => f i x₁) = (fun i => f i x₀) := by
    funext i
    have hi := hf i x₀
    rw [Equiv.swap_apply_left] at hi
    exact hi
  have h00 := h x₀ m0 x₀ m0
  have h01 := h x₀ m0 x₁ m1
  rw [hconst] at h01
  exact h00.1 (h01.2 hne) rfl

/--
Theorem 4.1(4), one side symbol.

Proves: on a merged pair of `q`, the observer `(q, s)` is injective if and only if `s` takes two
values on the pair.
Does not prove: injectivity of `(q, s)` outside the pair.
Relation: none. Trust: kernel-only.
-/
theorem mergedPair_side_symbol {X Q S : Type*} {q : X → Q} {x₀ x₁ : X}
    (h : IsMergedPair q x₀ x₁) (s : X → S) :
    Set.InjOn (fun x => (q x, s x)) ({x₀, x₁} : Set X) ↔ s x₀ ≠ s x₁ := by
  have m0 : x₀ ∈ ({x₀, x₁} : Set X) := Set.mem_insert _ _
  have m1 : x₁ ∈ ({x₀, x₁} : Set X) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  constructor
  · intro hinj hs
    have hpair : (fun x => (q x, s x)) x₀ = (fun x => (q x, s x)) x₁ := by
      show (q x₀, s x₀) = (q x₁, s x₁)
      rw [h.2, hs]
    exact h.1 (hinj m0 m1 hpair)
  · intro hs a ha b hb hab
    have ha' : a = x₀ ∨ a = x₁ := ha
    have hb' : b = x₀ ∨ b = x₁ := hb
    have hsab : s a = s b := congrArg Prod.snd hab
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · rw [ha', hb']
    · rw [ha', hb'] at hsab
      exact absurd hsab hs
    · rw [ha', hb'] at hsab
      exact absurd hsab.symm hs
    · rw [ha', hb']

/--
Theorem 4.1(5), restriction.

Proves: a subset of a merged pair of `q` carries an injective restriction of `q` if and only if
it omits a member of the pair.
Does not prove: any statement about subsets that leave the pair.
Relation: none. Trust: kernel-only.
-/
theorem mergedPair_restriction {X Q : Type*} {q : X → Q} {x₀ x₁ : X}
    (h : IsMergedPair q x₀ x₁) (S : Set X) (hS : S ⊆ ({x₀, x₁} : Set X)) :
    Set.InjOn q S ↔ ¬ (x₀ ∈ S ∧ x₁ ∈ S) := by
  constructor
  · rintro hinj ⟨h0, h1⟩
    exact h.1 (hinj h0 h1 h.2)
  · intro hnot a ha b hb _
    have ha' : a = x₀ ∨ a = x₁ := hS ha
    have hb' : b = x₀ ∨ b = x₁ := hS hb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · rw [ha', hb']
    · exact absurd ⟨ha' ▸ ha, hb' ▸ hb⟩ hnot
    · exact absurd ⟨hb' ▸ hb, ha' ▸ ha⟩ hnot
    · rw [ha', hb']

/--
Theorem 4.1(6), first half.

Proves: on a merged pair of `q`, no map of two records returns the comparison of the two states.
Does not prove: the same for observers finer than `q`.
Relation: none. Trust: kernel-only.
-/
theorem mergedPair_no_comparison_decoder {X Q : Type*} [DecidableEq X] {q : X → Q} {x₀ x₁ : X}
    (h : IsMergedPair q x₀ x₁) :
    ¬ ∃ d : Q → Q → Bool, ∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
        d (q a) (q b) = decide (a = b) := by
  rintro ⟨d, hd⟩
  have m0 : x₀ ∈ ({x₀, x₁} : Set X) := Set.mem_insert _ _
  have m1 : x₁ ∈ ({x₀, x₁} : Set X) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h00 := hd x₀ m0 x₀ m0
  have h01 := hd x₀ m0 x₁ m1
  rw [← h.2, h00, decide_eq_true rfl, decide_eq_false h.1] at h01
  exact Bool.noConfusion h01

/-- Theorem 4.1(6), second half: when the side symbol `s` takes two values on the pair, equality
of the records of `(q, s)` returns the comparison of the two states. -/
theorem mergedPair_comparison_decoder {X Q S : Type*} [DecidableEq X] [DecidableEq Q]
    [DecidableEq S] (q : X → Q) {x₀ x₁ : X} (s : X → S) (hs : s x₀ ≠ s x₁) :
    ∀ a ∈ ({x₀, x₁} : Set X), ∀ b ∈ ({x₀, x₁} : Set X),
      decide (q a = q b ∧ s a = s b) = decide (a = b) := by
  have hne : x₀ ≠ x₁ := fun e => hs (congrArg s e)
  intro a ha b hb
  have ha' : a = x₀ ∨ a = x₁ := ha
  have hb' : b = x₀ ∨ b = x₁ := hb
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb']
  · rw [decide_eq_true rfl, decide_eq_true ⟨rfl, rfl⟩]
  · rw [decide_eq_false hne, decide_eq_false (fun hand => hs hand.2)]
  · rw [decide_eq_false hne.symm, decide_eq_false (fun hand => hs hand.2.symm)]
  · rw [decide_eq_true rfl, decide_eq_true ⟨rfl, rfl⟩]

/-! ## Corollary 4.2, Example 4.6, Propositions 4.7 and 4.8 -/

/-- Corollary 4.2: on a type with at most one element every test is constant. -/
theorem test_const_of_subsingleton {X : Type*} [Subsingleton X] (f : X → Bool) (x y : X) :
    f x = f y :=
  congrArg f (Subsingleton.elim x y)

/-- Corollary 4.2: a test that takes two values has two points. -/
theorem two_points_of_separating_test {X : Type*} (f : X → Bool) {x y : X} (h : f x ≠ f y) :
    x ≠ y :=
  fun e => h (congrArg f e)

/-- Proposition 4.7: for a nonempty family of types with two distinct elements each, every choice
function is moved by some family of permutations. -/
theorem no_invariant_choice {ι : Type*} [Nonempty ι] (C : ι → Type*)
    (hC : ∀ i, ∃ a b : C i, a ≠ b) (f : ∀ i, C i) :
    ∃ σ : ∀ i, Equiv.Perm (C i), ∃ i, σ i (f i) ≠ f i := by
  classical
  have hc : ∀ j, ∃ c : C j, c ≠ f j := by
    intro j
    obtain ⟨a, b, hab⟩ := hC j
    by_cases ha : a = f j
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  choose g hg using hc
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨fun j => Equiv.swap (f j) (g j), i, ?_⟩
  show Equiv.swap (f i) (g i) (f i) ≠ f i
  rw [Equiv.swap_apply_left]
  exact hg i

/-- Proposition 4.8: an asymmetric relation closed under a map `σ` relates no two terms that
`σ` exchanges, in either direction. -/
theorem no_orientation_of_exchange {T : Type*} (lt : T → T → Prop)
    (hasymm : ∀ a b, lt a b → ¬ lt b a) (σ : T → T) (hσ : ∀ a b, lt a b → lt (σ a) (σ b))
    {l r : T} (hl : σ l = r) (hr : σ r = l) : ¬ lt l r ∧ ¬ lt r l := by
  constructor
  · intro h
    have h' := hσ l r h
    rw [hl, hr] at h'
    exact hasymm l r h h'
  · intro h
    have h' := hσ r l h
    rw [hr, hl] at h'
    exact hasymm r l h h'

end OperatorKO7.Meta.BoundaryObserver.MergedPair
