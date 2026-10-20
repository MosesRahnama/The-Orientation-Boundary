import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

set_option autoImplicit false

/-!
# Invariants of pairs under the invisible permutations

For an observer `q : X → Q`, the permutations that keep every record form the group
`licenseStabilizer q`. This module states Corollaries 4.3 and 4.4 and Proposition 4.5(i) of the
observation-principle manuscript: the orbits of that group on pairs of states are indexed by the
two records and one equality bit; two finite sets of states lie in one orbit if and only if they
have the same number of states in every class; and the permutations of a set that fix one point
have two orbits.


Relation: none; the statements are about permutations of arbitrary types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.

Strengthened form:
`finset_orbit_iff` holds without the hypothesis that the classes of `q` are finite, because the
permutation it constructs moves only states of the two finite sets.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PairInvariants

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! ## Corollary 4.3: pairs -/

/--
Corollary 4.3, orbits on pairs.

Proves: a permutation that keeps every record maps the pair `(a, a')` to the pair `(b, b')` for
some such permutation if and only if `a` and `b` have one record, `a'` and `b'` have one record,
and `a = a'` holds exactly when `b = b'` holds.
Does not prove: uniqueness of the permutation.
Relation: none. Trust: kernel-only.
-/
theorem pair_orbit_iff {X Q : Type*} (q : X → Q) (a a' b b' : X) :
    (∃ σ ∈ licenseStabilizer q, σ a = b ∧ σ a' = b') ↔
      (q a = q b ∧ q a' = q b' ∧ (a = a' ↔ b = b')) := by
  classical
  constructor
  · rintro ⟨σ, hσ, hab, hab'⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hab]
      exact (hσ a).symm
    · rw [← hab']
      exact (hσ a').symm
    · rw [← hab, ← hab']
      exact σ.injective.eq_iff.symm
  · rintro ⟨hq, hq', hiff⟩
    by_cases haa : a = a'
    · have hbb : b = b' := hiff.1 haa
      refine ⟨Equiv.swap a b,
        (by simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hq)),
        Equiv.swap_apply_left a b, ?_⟩
      rw [← haa, ← hbb]
      exact Equiv.swap_apply_left a b
    · have hbb : b ≠ b' := fun h => haa (hiff.2 h)
      have hτ : Equiv.swap a b ∈ licenseStabilizer q := by
        simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hq)
      have hc : q (Equiv.swap a b a') = q b' := (hτ a').trans hq'
      have hbc : b ≠ Equiv.swap a b a' := by
        intro h
        apply haa
        have h' : Equiv.swap a b a = Equiv.swap a b a' := (Equiv.swap_apply_left a b).trans h
        exact (Equiv.swap a b).injective h'
      refine ⟨Equiv.swap (Equiv.swap a b a') b' * Equiv.swap a b,
        Subgroup.mul_mem _
          (by simpa only [observerSwap] using (swap_mem_licenseStabilizer_of_eq q hc)) hτ,
        ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        exact Equiv.swap_apply_of_ne_of_ne hbc hbb
      · rw [Equiv.Perm.mul_apply]
        exact Equiv.swap_apply_left _ _

/-- Corollary 4.3, functions: a function of two states is invariant under the permutations that
keep every record if and only if it depends only on the two records and on whether the two
states are equal. -/
theorem pair_invariant_iff {X Q V : Type*} (q : X → Q) (F : X → X → V) :
    (∀ σ ∈ licenseStabilizer q, ∀ a a', F (σ a) (σ a') = F a a') ↔
      (∀ a a' b b', q a = q b → q a' = q b' → (a = a' ↔ b = b') → F a a' = F b b') := by
  constructor
  · intro h a a' b b' hq hq' hiff
    obtain ⟨σ, hσ, hab, hab'⟩ := (pair_orbit_iff q a a' b b').2 ⟨hq, hq', hiff⟩
    rw [← hab, ← hab']
    exact (h σ hσ a a').symm
  · intro h σ hσ a a'
    exact (h a a' (σ a) (σ a') (hσ a).symm (hσ a').symm σ.injective.eq_iff.symm).symm

/-! ## Corollary 4.4: finite sets -/

/-- Two finite sets with the same number of states in every class are matched by a permutation
that keeps every record. The permutation is built one state at a time and moves only states of
the two sets. -/
theorem exists_stabilizer_matching_finsets {X Q : Type*} [DecidableEq X] [DecidableEq Q]
    (q : X → Q) (A : Finset X) :
    ∀ A' : Finset X,
      (∀ y : Q, (A.filter (fun x => q x = y)).card = (A'.filter (fun x => q x = y)).card) →
        ∃ σ ∈ licenseStabilizer q, ∀ z, z ∈ A' ↔ ∃ x ∈ A, σ x = z := by
  induction A using Finset.induction_on with
  | empty =>
    intro A' h
    refine ⟨1, Subgroup.one_mem _, fun z => ⟨fun hz => ?_, ?_⟩⟩
    · exfalso
      have hy := h (q z)
      rw [Finset.filter_empty, Finset.card_empty] at hy
      have hmem : z ∈ A'.filter (fun x => q x = q z) := Finset.mem_filter.mpr ⟨hz, rfl⟩
      rw [Finset.card_eq_zero.mp hy.symm] at hmem
      exact Finset.notMem_empty z hmem
    · rintro ⟨x, hx, _⟩
      exact absurd hx (Finset.notMem_empty x)
  | insert a A₀ ha ih =>
    intro A' h
    have hpos : 0 < (A'.filter (fun x => q x = q a)).card := by
      rw [← h (q a)]
      exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_insert_self a A₀, rfl⟩⟩
    obtain ⟨a', ha'⟩ := Finset.card_pos.mp hpos
    obtain ⟨ha'A, ha'q⟩ := Finset.mem_filter.mp ha'
    obtain ⟨B, hB, hA'⟩ : ∃ B : Finset X, a' ∉ B ∧ A' = insert a' B :=
      ⟨A'.erase a', Finset.notMem_erase a' A', (Finset.insert_erase ha'A).symm⟩
    subst hA'
    have hcount : ∀ y : Q,
        (A₀.filter (fun x => q x = y)).card = (B.filter (fun x => q x = y)).card := by
      intro y
      have hy := h y
      rw [Finset.filter_insert, Finset.filter_insert] at hy
      by_cases hya : q a = y
      · have hya' : q a' = y := ha'q.trans hya
        rw [if_pos hya, if_pos hya',
          Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1),
          Finset.card_insert_of_notMem (fun hm => hB (Finset.mem_filter.mp hm).1)] at hy
        exact Nat.succ_injective hy
      · have hya' : ¬ q a' = y := fun h' => hya (ha'q.symm.trans h')
        rw [if_neg hya, if_neg hya'] at hy
        exact hy
    obtain ⟨σ₀, hσ₀, hmatch⟩ := ih B hcount
    have hc : q (σ₀ a) = q a' := (hσ₀ a).trans ha'q.symm
    have hσ₀A : ∀ x ∈ A₀, σ₀ x ≠ σ₀ a := fun x hx hxa => ha (σ₀.injective hxa ▸ hx)
    have hσ₀B : ∀ x ∈ A₀, σ₀ x ≠ a' := fun x hx hxa' => hB ((hmatch a').2 ⟨x, hx, hxa'⟩)
    have hswap : Equiv.swap (σ₀ a) a' ∈ licenseStabilizer q := by
      intro z
      by_cases hz₁ : z = σ₀ a
      · subst z
        simpa using hc.symm
      by_cases hz₂ : z = a'
      · subst z
        simpa using hc
      rw [Equiv.swap_apply_of_ne_of_ne hz₁ hz₂]
    refine ⟨Equiv.swap (σ₀ a) a' * σ₀,
      Subgroup.mul_mem _ hswap hσ₀,
      fun z => ⟨fun hz => ?_, ?_⟩⟩
    · rcases Finset.mem_insert.mp hz with hza' | hzB
      · refine ⟨a, Finset.mem_insert_self a A₀, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hza']
      · obtain ⟨x, hx, hxz⟩ := (hmatch z).1 hzB
        refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hσ₀A x hx) (hσ₀B x hx)]
        exact hxz
    · rintro ⟨x, hx, hxz⟩
      rw [Equiv.Perm.mul_apply] at hxz
      rcases Finset.mem_insert.mp hx with hxa | hxA₀
      · rw [hxa, Equiv.swap_apply_left] at hxz
        rw [← hxz]
        exact Finset.mem_insert_self a' B
      · rw [Equiv.swap_apply_of_ne_of_ne (hσ₀A x hxA₀) (hσ₀B x hxA₀)] at hxz
        exact Finset.mem_insert_of_mem ((hmatch z).2 ⟨x, hxA₀, hxz⟩)

/--
Corollary 4.4, content and count.

Proves: two finite sets of states lie in one orbit of the permutations that keep every record if
and only if they have the same number of states in every class of `q`.
Does not prove: any statement about infinite sets of states.
Relation: none. Trust: kernel-only.
-/
theorem finset_orbit_iff {X Q : Type*} [DecidableEq X] [DecidableEq Q] (q : X → Q)
    (A A' : Finset X) :
    (∃ σ ∈ licenseStabilizer q, A.map σ.toEmbedding = A') ↔
      ∀ y : Q, (A.filter (fun x => q x = y)).card = (A'.filter (fun x => q x = y)).card := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩ y
    rw [Finset.filter_map, Finset.card_map]
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    show q x = y ↔ q (σ x) = y
    rw [hσ x]
  · intro h
    obtain ⟨σ, hσ, hmatch⟩ := exists_stabilizer_matching_finsets q A A' h
    refine ⟨σ, hσ, Finset.ext fun z => ?_⟩
    rw [Finset.mem_map]
    exact (hmatch z).symm

/-! ## Proposition 4.5(i): the permutations that fix one point -/

/-- Proposition 4.5(i): the permutations that fix `x` are transitive on the other points. -/
theorem point_stabilizer_transitive {C : Type*} (x a b : C) (ha : a ≠ x) (hb : b ≠ x) :
    ∃ σ : Equiv.Perm C, σ x = x ∧ σ a = b := by
  classical
  exact ⟨Equiv.swap a b, Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm, Equiv.swap_apply_left a b⟩

/-- Proposition 4.5(i): a test is invariant under the permutations that fix `x` if and only if it
has one value on the points other than `x`; such a test is a Boolean function of the indicator
of `x`. -/
theorem point_stabilizer_invariant_iff {C : Type*} (x : C) (f : C → Bool) :
    (∀ σ : Equiv.Perm C, σ x = x → ∀ c, f (σ c) = f c) ↔
      ∀ a b, a ≠ x → b ≠ x → f a = f b := by
  constructor
  · intro h a b ha hb
    obtain ⟨σ, hσx, hσa⟩ := point_stabilizer_transitive x a b ha hb
    rw [← hσa]
    exact (h σ hσx a).symm
  · intro h σ hσx c
    classical
    by_cases hc : c = x
    · rw [hc, hσx]
    · exact h (σ c) c (fun hσc => hc (σ.injective (hσc.trans hσx.symm))) hc

end OperatorKO7.Meta.BoundaryObserver.PairInvariants
