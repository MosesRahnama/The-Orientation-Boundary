import OperatorKO7.Meta.BoundaryObserver.MergedPair

set_option autoImplicit false

/-!
# Content, place, and the place coordinates of an observer

An occurrence is a content at a place, `Y × R`. The content observer and the place observer are
the two projections. For an arbitrary observer `q : X → Q`, a place coordinate with `n` values is
a map `p : X → Fin n` such that `(q, p)` is injective. This module states Proposition 3.2,
Theorem 3.3 and Proposition 3.4 of the observation-principle manuscript: complementarity of
content and place, the least size of a place coordinate, and the labellings of an observer with
classes of one size as one free orbit of the permutations that keep every record.


Relation: none; the statements are about maps and permutations on arbitrary types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer

/-! ## Proposition 3.2: content and place are complementary -/

/-- Proposition 3.2(i): content and place together are injective. -/
theorem content_place_injective (Y R : Type*) :
    Function.Injective (fun o : Y × R => (o.1, o.2)) := by
  rintro ⟨y, r⟩ ⟨y', r'⟩ h
  exact h

/-- Proposition 3.2(ii): two occurrences are joined by one step of each kernel, through an
occurrence with the place of the first and the content of the second. -/
theorem content_place_join {Y R : Type*} (o o' : Y × R) :
    ∃ o'' : Y × R, o''.2 = o.2 ∧ o''.1 = o'.1 :=
  ⟨(o'.1, o.2), rfl, rfl⟩

/-- Proposition 3.2(ii), full strength: the transitive closure of the union of the
content-observer kernel and place-observer kernel is the total relation.
No inhabitedness or finiteness assumption on either coordinate is needed.
The path uses the place kernel first, then the content kernel. -/
theorem content_place_kernel_union_transGen_eq_total {Y R : Type*} :
    Relation.TransGen (fun a b : Y × R => a.1 = b.1 ∨ a.2 = b.2) =
      (fun _ _ => True) := by
  funext a b
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    have hplace :
        Relation.TransGen (fun x y : Y × R => x.1 = y.1 ∨ x.2 = y.2)
          a (b.1, a.2) :=
      Relation.TransGen.single (Or.inr rfl)
    have hcontent :
        Relation.TransGen (fun x y : Y × R => x.1 = y.1 ∨ x.2 = y.2)
          (b.1, a.2) b :=
      Relation.TransGen.single (Or.inl rfl)
    exact hplace.trans hcontent

/-- Proposition 3.2(iii): a class of the content observer meets a class of the place observer in
one occurrence. -/
theorem content_class_meets_place_class {Y R : Type*} (y : Y) (r : R) :
    ∃! o : Y × R, o.1 = y ∧ o.2 = r := by
  refine ⟨(y, r), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨y', r'⟩ ⟨h1, h2⟩
  exact Prod.ext h1 h2

/-- Proposition 3.2(iv): two occurrences are equal, or copies with different places, or have
different contents. -/
theorem occurrence_trichotomy {Y R : Type*} (o o' : Y × R) :
    o = o' ∨ (o.1 = o'.1 ∧ o.2 ≠ o'.2) ∨ o.1 ≠ o'.1 := by
  classical
  by_cases h1 : o.1 = o'.1
  · by_cases h2 : o.2 = o'.2
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr h1)

/-! ## Theorem 3.3(i): existence and least size -/

/--
Theorem 3.3(i).

Proves: a map `p` into `n` values with `(q, p)` injective exists if and only if every class of
`q` is finite with at most `n` elements. Hence `n` values suffice when `n` bounds the class
sizes, and fewer values than the size of some class never suffice.
Does not prove: any choice of `p`; the set of such maps is the subject of part (ii).
Relation: none. Trust: kernel-only, with `Classical.choice` for the choice of one injection per
class.
-/
theorem exists_place_coordinate_iff {X Q : Type*} (q : X → Q) (n : ℕ) :
    (∃ p : X → Fin n, Function.Injective (fun x => (q x, p x))) ↔
      ∀ y : Q, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n := by
  classical
  constructor
  · rintro ⟨p, hp⟩ y
    have hinj : Set.InjOn p (q ⁻¹' {y}) := by
      intro a ha b hb hab
      have ha' : q a = y := ha
      have hb' : q b = y := hb
      apply hp
      show (q a, p a) = (q b, p b)
      rw [ha', hb', hab]
    have hfin : (q ⁻¹' {y}).Finite :=
      Set.Finite.of_injOn (Set.mapsTo_univ p _) hinj Set.finite_univ
    refine ⟨hfin, ?_⟩
    have hle := Set.ncard_le_ncard_of_injOn p (fun a _ => Set.mem_univ (p a)) hinj Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_fin] at hle
  · intro h
    have hemb : ∀ y : Q, Nonempty (↥(q ⁻¹' {y}) ↪ Fin n) := by
      intro y
      obtain ⟨hfin, hcard⟩ := h y
      haveI : Fintype ↥(q ⁻¹' {y}) := hfin.fintype
      apply Function.Embedding.nonempty_of_card_le
      rw [Fintype.card_fin, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
      exact hcard
    let e : ∀ y : Q, ↥(q ⁻¹' {y}) ↪ Fin n := fun y => Classical.choice (hemb y)
    refine ⟨fun x => e (q x) ⟨x, rfl⟩, ?_⟩
    intro a b hab
    have hq : q a = q b := congrArg Prod.fst hab
    have hpab : e (q a) ⟨a, rfl⟩ = e (q b) ⟨b, rfl⟩ := congrArg Prod.snd hab
    have aux : ∀ (y : Q) (hy : q b = y), e y ⟨b, hy⟩ = e (q b) ⟨b, rfl⟩ := by
      intro y hy
      subst hy
      rfl
    rw [← aux (q a) hq.symm] at hpab
    exact congrArg Subtype.val ((e (q a)).injective hpab)

/-! ## Theorem 3.3(ii): the labellings form one free orbit -/

/-- The labellings of `q` with `n` values: the maps into `Fin n` that are bijective on every
class of `q`. The set is nonempty only if every class has `n` elements. -/
def PlaceCoord {X Q : Type*} (q : X → Q) (n : ℕ) : Set (X → Fin n) :=
  {p | ∀ y ∈ Set.range q, Set.BijOn p (q ⁻¹' {y}) Set.univ}

/-- Non-vacuity: the identity is a labelling of the constant observer of `Fin n`. -/
theorem placeCoord_const_id (n : ℕ) : (id : Fin n → Fin n) ∈ PlaceCoord (fun _ : Fin n => ()) n := by
  intro y _
  have hall : (fun _ : Fin n => ()) ⁻¹' {y} = Set.univ := by
    ext x
    simp
  rw [hall]
  exact ⟨Set.mapsTo_univ _ _, Function.injective_id.injOn, fun k _ => ⟨k, Set.mem_univ k, rfl⟩⟩

/-- Theorem 3.3(ii), first claim: a labelling `p` makes `(q, p)` a bijection from the states onto
the pairs of a record and a place. -/
theorem placeCoord_pair_bijective {X Q : Type*} (q : X → Q) {n : ℕ} {p : X → Fin n}
    (hp : p ∈ PlaceCoord q n) :
    Function.Bijective (fun x => (Set.rangeFactorization q x, p x)) := by
  constructor
  · intro a b hab
    have hq : q a = q b := congrArg (fun z => (z.1 : Q)) hab
    have hpab : p a = p b := congrArg Prod.snd hab
    exact (hp (q a) ⟨a, rfl⟩).injOn (rfl : q a = q a) (hq.symm : q b = q a) hpab
  · rintro ⟨⟨y, hy⟩, k⟩
    obtain ⟨x, hx, hpk⟩ := (hp y hy).surjOn (Set.mem_univ k)
    have hx' : q x = y := hx
    exact ⟨x, Prod.ext (Subtype.ext hx') hpk⟩

/-- A permutation that keeps every record maps each class of `q` onto itself. -/
theorem stabilizer_symm_bijOn_class {X Q : Type*} (q : X → Q) {σ : Equiv.Perm X}
    (hσ : σ ∈ licenseStabilizer q) (y : Q) :
    Set.BijOn σ.symm (q ⁻¹' {y}) (q ⁻¹' {y}) := by
  have hsymm : ∀ x, q (σ.symm x) = q x := by
    intro x
    have h := hσ (σ.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨?_, σ.symm.injective.injOn, ?_⟩
  · intro x hx
    have hx' : q x = y := hx
    show q (σ.symm x) = y
    rw [hsymm, hx']
  · intro z hz
    have hz' : q z = y := hz
    refine ⟨σ z, ?_, Equiv.symm_apply_apply σ z⟩
    show q (σ z) = y
    rw [hσ z, hz']

/-- Theorem 3.3(ii): the permutations that keep every record act on the labellings by
`σ · p = p ∘ σ⁻¹`. -/
theorem placeCoord_smul_mem {X Q : Type*} (q : X → Q) {n : ℕ} {p : X → Fin n}
    (hp : p ∈ PlaceCoord q n) {σ : Equiv.Perm X} (hσ : σ ∈ licenseStabilizer q) :
    p ∘ σ.symm ∈ PlaceCoord q n := by
  intro y hy
  exact (hp y hy).comp (stabilizer_symm_bijOn_class q hσ y)

/--
Theorem 3.3(ii), the action is free.

Proves: a permutation that keeps every record and fixes one labelling is the identity.
Does not prove: freeness of the action on maps that are not labellings.
Relation: none. Trust: kernel-only.
-/
theorem placeCoord_free {X Q : Type*} (q : X → Q) {n : ℕ} {p : X → Fin n}
    (hp : p ∈ PlaceCoord q n) {σ : Equiv.Perm X} (hσ : σ ∈ licenseStabilizer q)
    (hfix : p ∘ σ.symm = p) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  have hq : q (σ.symm x) = q x := by
    have h := hσ (σ.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hpx : p (σ.symm x) = p x := congrFun hfix x
  have hx : σ.symm x = x :=
    (hp (q x) ⟨x, rfl⟩).injOn (hq : q (σ.symm x) = q x) (rfl : q x = q x) hpx
  exact ((Equiv.symm_apply_eq σ).1 hx).symm

/--
Theorem 3.3(ii), the action is transitive.

Proves: any two labellings of `q` differ by a permutation that keeps every record.
Does not prove: uniqueness of that permutation, which is `placeCoord_free`.
Relation: none. Trust: kernel-only, with `Classical.choice` for the two inverse maps.
-/
theorem placeCoord_transitive {X Q : Type*} (q : X → Q) {n : ℕ} {p p' : X → Fin n}
    (hp : p ∈ PlaceCoord q n) (hp' : p' ∈ PlaceCoord q n) :
    ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm := by
  classical
  have hf : ∀ x, ∃ z, q z = q x ∧ p' z = p x := by
    intro x
    obtain ⟨z, hz, hpz⟩ := (hp' (q x) ⟨x, rfl⟩).surjOn (Set.mem_univ (p x))
    exact ⟨z, hz, hpz⟩
  have hg : ∀ x, ∃ z, q z = q x ∧ p z = p' x := by
    intro x
    obtain ⟨z, hz, hpz⟩ := (hp (q x) ⟨x, rfl⟩).surjOn (Set.mem_univ (p' x))
    exact ⟨z, hz, hpz⟩
  choose f hfq hfp using hf
  choose g hgq hgp using hg
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h1 : q (g (f x)) = q x := by rw [hgq, hfq]
    have h2 : p (g (f x)) = p x := by rw [hgp, hfp]
    exact (hp (q x) ⟨x, rfl⟩).injOn h1 (rfl : q x = q x) h2
  have hfg : ∀ x, f (g x) = x := by
    intro x
    have h1 : q (f (g x)) = q x := by rw [hfq, hgq]
    have h2 : p' (f (g x)) = p' x := by rw [hfp, hgp]
    exact (hp' (q x) ⟨x, rfl⟩).injOn h1 (rfl : q x = q x) h2
  refine ⟨⟨f, g, hgf, hfg⟩, fun x => hfq x, ?_⟩
  funext x
  exact (hgp x).symm

/-! ## Proposition 3.4: the labellings of a pair are its members -/

/-- Proposition 3.4: on a type with two elements, a labelling is fixed by the element that it
sends to the first label. -/
theorem labelling_member_bijective (C : Type*) [Fintype C] (hC : Fintype.card C = 2) :
    Function.Bijective (fun e : C ≃ Fin 2 => e.symm 0) := by
  constructor
  · intro e e' h
    have h0 : e.symm 0 = e'.symm 0 := h
    have key : ∀ (e₁ e₂ : C ≃ Fin 2), e₁.symm 0 = e₂.symm 0 → ∀ c, e₁ c = 0 → e₂ c = 0 := by
      intro e₁ e₂ h12 c hc
      have hc' : c = e₁.symm 0 := by rw [← hc, Equiv.symm_apply_apply]
      rw [hc', h12, Equiv.apply_symm_apply]
    exact Equiv.ext fun c =>
      Fin.fin_two_eq_of_eq_zero_iff ⟨key e e' h0 c, key e' e h0.symm c⟩
  · intro c
    let e₀ : C ≃ Fin 2 := Fintype.equivFinOfCardEq hC
    by_cases h : e₀ c = 0
    · refine ⟨e₀, ?_⟩
      show e₀.symm 0 = c
      rw [← h, Equiv.symm_apply_apply]
    · have h1 : e₀ c = 1 := by
        apply Fin.ext
        have hlt := (e₀ c).isLt
        have hne : (e₀ c : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
        show (e₀ c : ℕ) = 1
        omega
      have hsymm : e₀.symm 1 = c := by rw [← h1, Equiv.symm_apply_apply]
      refine ⟨e₀.trans (Equiv.swap 0 1), ?_⟩
      show (e₀.trans (Equiv.swap 0 1)).symm 0 = c
      rw [Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_left]
      exact hsymm

/-- Proposition 3.4: the map from labellings to members commutes with every permutation. -/
theorem labelling_member_equivariant {C : Type*} (σ : Equiv.Perm C) (e : C ≃ Fin 2) :
    (σ.symm.trans e).symm 0 = σ (e.symm 0) :=
  rfl

end OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
