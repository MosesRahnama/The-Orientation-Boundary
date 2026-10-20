import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates

set_option autoImplicit false

/-!
# One free orbit of place families for every observer

Theorem `thm:place`(ii) of the Boundary Theorem manuscript proves one free orbit of the invisible
group on the place coordinates for fibers of one size `n` with the common alphabet `Fin n`
(`PlaceCoordinates.placeCoord_free`, `PlaceCoordinates.placeCoord_transitive`). Remark
`rem:landau` and the conclusion state one free orbit for every observer. This module proves that
statement with an alphabet `A y` of its own for each fiber and with no finiteness: the families of
bijections of each fiber onto its alphabet form one free orbit of the invisible group
`licenseStabilizer q`, and each family together with the record resolves every state. The common
alphabet `Fin n` is the case of fibers of one size `n`, and the control
`common_alphabet_two_orbits` shows that the common-alphabet orbit statement fails for fibers of
unequal size, and `common_alphabet_four_coordinates_two_orbits` counts the four resolving
coordinates of that control and their two orbits.

The invisible group acts through the restriction `fiberPerm` of each invisible permutation to each
fiber; `fiberPerm_eq_fiberMulEquiv` identifies this restriction with the isomorphism
`licenseStabilizerFiberMulEquiv` that `LandauDictionary.landau_symmetry_change` records.


Relation: none; the statements are about maps and permutations on arbitrary types.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PlaceOrbitGeneral

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates

universe u v w

section General

variable {X : Type u} {Q : Type v} (q : X → Q)

/-- An invisible permutation keeps the record of every inverse image. -/
theorem stabilizer_symm_apply (σ : licenseStabilizer q) (x : X) :
    q ((σ : Equiv.Perm X).symm x) = q x := by
  have h := (mem_licenseStabilizer_iff q (σ : Equiv.Perm X)).1 σ.2 ((σ : Equiv.Perm X).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The restriction of an invisible permutation `σ` to the fiber over `y`: `q (σ x) = q x` places
`σ x` in the fiber of `x`. -/
def fiberPerm (σ : licenseStabilizer q) (y : Set.range q) : Equiv.Perm (ObserverFiber q y) where
  toFun z := ⟨(σ : Equiv.Perm X) z.1,
    ((mem_licenseStabilizer_iff q (σ : Equiv.Perm X)).1 σ.2 z.1).trans z.2⟩
  invFun z := ⟨(σ : Equiv.Perm X).symm z.1, (stabilizer_symm_apply q σ z.1).trans z.2⟩
  left_inv z := Subtype.ext ((σ : Equiv.Perm X).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((σ : Equiv.Perm X).apply_symm_apply z.1)

/-- The restriction of `σ` moves the state of a fiber point by `σ`. -/
@[simp] theorem fiberPerm_apply_val (σ : licenseStabilizer q) (y : Set.range q)
    (z : ObserverFiber q y) : ((fiberPerm q σ y z : ObserverFiber q y) : X) = (σ : Equiv.Perm X) z.1 :=
  rfl

/-- The inverse of the restriction of `σ` moves the state of a fiber point by `σ⁻¹`. -/
@[simp] theorem fiberPerm_symm_apply_val (σ : licenseStabilizer q) (y : Set.range q)
    (z : ObserverFiber q y) :
    (((fiberPerm q σ y).symm z : ObserverFiber q y) : X) = (σ : Equiv.Perm X).symm z.1 :=
  rfl

/-- The restriction of `σ` to the fiber over `y` is the `y`-component of `σ` under the
isomorphism `licenseStabilizerFiberMulEquiv` of the invisible group with the product of the
permutation groups of the fibers, the isomorphism of `landau_symmetry_change`. -/
theorem fiberPerm_eq_fiberMulEquiv (σ : licenseStabilizer q) (y : Set.range q) :
    fiberPerm q σ y = licenseStabilizerFiberMulEquiv q σ y :=
  Equiv.ext fun _ => Subtype.ext rfl

/-- The place families of `q` with the alphabet family `A`: one bijection of each fiber onto its
own alphabet. -/
def PlaceFamily (A : Set.range q → Type w) : Type (max u v w) :=
  ∀ y : Set.range q, ObserverFiber q y ≃ A y

variable {q}

/-- Two place families are equal when they agree at every point of every fiber. -/
theorem PlaceFamily.ext {A : Set.range q → Type w} {f g : PlaceFamily q A}
    (h : ∀ (y : Set.range q) (z : ObserverFiber q y), f y z = g y z) : f = g :=
  funext fun y => Equiv.ext (h y)

/-- Equal place families agree at every point of every fiber. -/
theorem PlaceFamily.apply_eq {A : Set.range q → Type w} {f g : PlaceFamily q A} (h : f = g)
    (y : Set.range q) (z : ObserverFiber q y) : f y z = g y z := by
  rw [h]

variable (q)

/-- The invisible group acts on the place families by `σ • f := fun y => (fiberPerm σ y)⁻¹ ≫ f y`,
the form `p ∘ σ⁻¹` of Theorem `thm:place`(ii) on each fiber. -/
instance instMulAction (A : Set.range q → Type w) :
    MulAction (licenseStabilizer q) (PlaceFamily q A) where
  smul σ f := fun y => (fiberPerm q σ y).symm.trans (f y)
  one_smul _ := PlaceFamily.ext fun _ _ => rfl
  mul_smul _ _ _ := PlaceFamily.ext fun _ _ => rfl

/-- The action reads the family at the inverse image: `(σ • f) y ⟨x, _⟩ = f y ⟨σ⁻¹ x, _⟩`. -/
theorem smul_apply {A : Set.range q → Type w} (σ : licenseStabilizer q) (f : PlaceFamily q A)
    (y : Set.range q) (z : ObserverFiber q y) :
    (σ • f) y z = f y ⟨(σ : Equiv.Perm X)⁻¹ z.1, (stabilizer_symm_apply q σ z.1).trans z.2⟩ :=
  rfl

/--
The action on place families is free.

Proves: an invisible permutation that fixes one place family is the identity, for every observer
and every alphabet family.
Does not prove: freeness on families of maps that are not bijections.
Relation: none. Trust: kernel-only.
-/
theorem placeFamily_free {A : Set.range q → Type w} (σ : licenseStabilizer q)
    (f : PlaceFamily q A) (h : σ • f = f) : σ = 1 := by
  apply Subtype.ext
  refine Equiv.ext fun x => ?_
  have hx := PlaceFamily.apply_eq h (Set.rangeFactorization q x) ⟨x, rfl⟩
  rw [smul_apply] at hx
  have hsymm : (σ : Equiv.Perm X).symm x = x :=
    congrArg Subtype.val ((f (Set.rangeFactorization q x)).injective hx)
  show (σ : Equiv.Perm X) x = x
  exact ((Equiv.symm_apply_eq (σ : Equiv.Perm X)).1 hsymm).symm

/-- The invisible permutation that carries the place family `f` to the place family `g`: on the
fiber over `y`, the bijection `(g y)⁻¹ ∘ f y`, assembled through the isomorphism
`licenseStabilizerFiberMulEquiv`. -/
def placeFamilyTransport {A : Set.range q → Type w} (f g : PlaceFamily q A) :
    licenseStabilizer q :=
  (licenseStabilizerFiberMulEquiv q).symm fun y => (f y).trans (g y).symm

/-- The restriction of the transport from `f` to `g` to the fiber over `y` is
`(g y)⁻¹ ∘ f y`. -/
theorem fiberPerm_placeFamilyTransport {A : Set.range q → Type w} (f g : PlaceFamily q A)
    (y : Set.range q) :
    fiberPerm q (placeFamilyTransport q f g) y = (f y).trans (g y).symm := by
  rw [fiberPerm_eq_fiberMulEquiv, placeFamilyTransport, MulEquiv.apply_symm_apply]

/--
The action on place families is transitive.

Proves: any two place families of `q` with the same alphabet family differ by an invisible
permutation, for every observer and every alphabet family, with no finiteness.
Does not prove: uniqueness of that permutation, which is `placeFamily_exists_unique`.
Relation: none. Trust: kernel-only.
-/
theorem placeFamily_transitive {A : Set.range q → Type w} (f g : PlaceFamily q A) :
    ∃ σ : licenseStabilizer q, σ • f = g := by
  refine ⟨placeFamilyTransport q f g, PlaceFamily.ext fun y z => ?_⟩
  show f y ((fiberPerm q (placeFamilyTransport q f g) y).symm z) = g y z
  rw [fiberPerm_placeFamilyTransport, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

/-- The action of the invisible group on the place families with one alphabet family is
transitive, as a Mathlib instance. -/
instance instIsPretransitive (A : Set.range q → Type w) :
    MulAction.IsPretransitive (licenseStabilizer q) (PlaceFamily q A) :=
  ⟨placeFamily_transitive q⟩

/--
The place families form one free orbit.

Proves: for any two place families `f` and `g` of `q` with the same alphabet family, exactly one
invisible permutation carries `f` to `g`.
Does not prove: anything about families of maps that are not bijections.
Relation: none. Trust: kernel-only.
-/
theorem placeFamily_exists_unique {A : Set.range q → Type w} (f g : PlaceFamily q A) :
    ∃! σ : licenseStabilizer q, σ • f = g := by
  obtain ⟨σ, hσ⟩ := placeFamily_transitive q f g
  refine ⟨σ, hσ, fun τ hτ => ?_⟩
  have hfix : (σ⁻¹ * τ) • f = f := by
    rw [mul_smul, hτ, ← hσ, inv_smul_smul]
  exact (inv_mul_eq_one.mp (placeFamily_free q (σ⁻¹ * τ) f hfix)).symm

/-- The joint map of a place family: a state goes to its record together with its place in the
alphabet of its fiber. -/
def placeFamilyEquiv {A : Set.range q → Type w} (f : PlaceFamily q A) :
    X ≃ Σ y : Set.range q, A y :=
  (Equiv.sigmaFiberEquiv (Set.rangeFactorization q)).symm.trans
    (Equiv.sigmaCongrRight fun y => (rangeFiberEquiv q y).trans (f y))

/-- The joint map sends a state to its record and to its place in the alphabet of its fiber. -/
theorem placeFamilyEquiv_apply {A : Set.range q → Type w} (f : PlaceFamily q A) (x : X) :
    placeFamilyEquiv q f x =
      ⟨Set.rangeFactorization q x, f (Set.rangeFactorization q x) ⟨x, rfl⟩⟩ :=
  rfl

/--
Every place family resolves every state.

Proves: for every observer `q`, every alphabet family `A` and every place family `f`, the map
`x ↦ ⟨record of x, f (record of x) x⟩` into `Σ y, A y` is a bijection.
Does not prove: the existence of a place family for a given alphabet family, which is
`placeFamily_nonempty_iff`.
Relation: none. Trust: kernel-only.
-/
theorem placeFamily_joint_bijective {A : Set.range q → Type w} (f : PlaceFamily q A) :
    Function.Bijective (fun x : X =>
      (⟨Set.rangeFactorization q x, f (Set.rangeFactorization q x) ⟨x, rfl⟩⟩ :
        Σ y : Set.range q, A y)) :=
  (placeFamilyEquiv q f).bijective

/-- The identity place family: each fiber is its own alphabet. -/
def placeFamilyId : PlaceFamily q (ObserverFiber q) :=
  fun y => Equiv.refl (ObserverFiber q y)

/--
Every observer has a resolving place family.

Proves: with the fibers themselves as alphabets, the identity family is a place family of `q`, and
it resolves every state together with the record.
Does not prove: a place family with any prescribed alphabet family.
Relation: none. Trust: kernel-only.
-/
theorem placeFamily_self :
    ∃ f : PlaceFamily q (ObserverFiber q),
      Function.Bijective (fun x : X =>
        (⟨Set.rangeFactorization q x, f (Set.rangeFactorization q x) ⟨x, rfl⟩⟩ :
          Σ y : Set.range q, ObserverFiber q y)) :=
  ⟨placeFamilyId q, placeFamily_joint_bijective q (placeFamilyId q)⟩

/-- A place family with the alphabet family `A` exists iff every fiber is in bijection with its
alphabet. -/
theorem placeFamily_nonempty_iff {A : Set.range q → Type w} :
    Nonempty (PlaceFamily q A) ↔ ∀ y : Set.range q, Nonempty (ObserverFiber q y ≃ A y) :=
  ⟨fun ⟨f⟩ y => ⟨f y⟩, fun h => ⟨fun y => Classical.choice (h y)⟩⟩

/-! ## The common alphabet `Fin n` -/

/-- A map out of the fibers with one codomain, read at the record of a fiber point, is the map
read at that point. -/
theorem family_apply_rangeFactorization {B : Type w}
    (f : ∀ y : Set.range q, ObserverFiber q y → B) (y : Set.range q) (z : ObserverFiber q y) :
    f (Set.rangeFactorization q z.1) ⟨z.1, rfl⟩ = f y z := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, hx⟩ := z
  change q x = y at hx
  subst hx
  rfl

/-- The labelling of a common-alphabet place family: a state goes to its place in its fiber. -/
def toPlaceCoord {n : ℕ} (f : PlaceFamily q (fun _ => Fin n)) : X → Fin n :=
  fun x => f (Set.rangeFactorization q x) ⟨x, rfl⟩

/-- The labelling of a common-alphabet place family is a place coordinate of
`PlaceCoordinates.PlaceCoord`. -/
theorem toPlaceCoord_mem {n : ℕ} (f : PlaceFamily q (fun _ => Fin n)) :
    toPlaceCoord q f ∈ PlaceCoord q n := by
  intro y hy
  have key : ∀ (x : X) (hx : q x = y),
      toPlaceCoord q f x = f ⟨y, hy⟩ ⟨x, hx⟩ := fun x hx =>
    family_apply_rangeFactorization q (fun y z => f y z) ⟨y, hy⟩ ⟨x, hx⟩
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : q a = y := ha
    have hb' : q b = y := hb
    rw [key a ha', key b hb'] at hab
    exact congrArg Subtype.val ((f ⟨y, hy⟩).injective hab)
  · intro k _
    obtain ⟨⟨x, hx⟩, hxk⟩ := (f ⟨y, hy⟩).surjective k
    exact ⟨x, hx, (key x hx).trans hxk⟩

/-- The common-alphabet place family of a place coordinate: on each fiber, the restriction of the
coordinate. -/
noncomputable def ofPlaceCoord {n : ℕ} {p : X → Fin n} (hp : p ∈ PlaceCoord q n) :
    PlaceFamily q (fun _ => Fin n) :=
  fun y => Equiv.ofBijective (fun z : ObserverFiber q y => p z.1)
    ⟨fun a b hab => Subtype.ext ((hp y.1 y.2).injOn a.2 b.2 hab), fun k => by
      obtain ⟨x, hx, hxk⟩ := (hp y.1 y.2).surjOn (Set.mem_univ k)
      exact ⟨⟨x, hx⟩, hxk⟩⟩

/-- The common-alphabet place families are the place coordinates of `PlaceCoord q n`. -/
noncomputable def placeCoordEquiv (n : ℕ) : PlaceFamily q (fun _ => Fin n) ≃ PlaceCoord q n where
  toFun f := ⟨toPlaceCoord q f, toPlaceCoord_mem q f⟩
  invFun p := ofPlaceCoord q p.2
  left_inv f := PlaceFamily.ext fun y z =>
    family_apply_rangeFactorization q (fun y z => f y z) y z
  right_inv _ := Subtype.ext (funext fun _ => rfl)

/-- The labelling map is equivariant: the labelling of `σ • f` is the labelling of `f` composed
with `σ⁻¹`, the action of `PlaceCoordinates.placeCoord_smul_mem`. -/
theorem toPlaceCoord_smul {n : ℕ} (σ : licenseStabilizer q) (f : PlaceFamily q (fun _ => Fin n)) :
    toPlaceCoord q (σ • f) = toPlaceCoord q f ∘ (σ : Equiv.Perm X).symm := by
  funext x
  exact (family_apply_rangeFactorization q (fun y z => f y z) (Set.rangeFactorization q x)
    ⟨(σ : Equiv.Perm X).symm x, stabilizer_symm_apply q σ x⟩).symm

/--
The common alphabet is the case of fibers of one size.

Proves: when every fiber of `q` is in bijection with `Fin n`, a place coordinate of
`PlaceCoord q n` exists, and the common-alphabet place families correspond to the place
coordinates by an equivalence that carries the action `σ • f` to `p ∘ σ⁻¹`.
Does not prove: a common alphabet for fibers of unequal size; `common_alphabet_two_orbits` is the
failure.
Relation: none. Trust: kernel-only, with `Classical.choice` for one bijection per fiber.
-/
theorem placeFamily_common_alphabet (n : ℕ)
    (hn : ∀ y : Set.range q, Nonempty (ObserverFiber q y ≃ Fin n)) :
    (PlaceCoord q n).Nonempty ∧
      ∃ e : PlaceFamily q (fun _ => Fin n) ≃ PlaceCoord q n,
        ∀ (σ : licenseStabilizer q) (f : PlaceFamily q (fun _ => Fin n)),
          (e (σ • f) : X → Fin n) = (e f : X → Fin n) ∘ (σ : Equiv.Perm X).symm := by
  obtain ⟨f⟩ := (placeFamily_nonempty_iff q).2 hn
  exact ⟨⟨_, toPlaceCoord_mem q f⟩, placeCoordEquiv q n, fun σ g => toPlaceCoord_smul q σ g⟩

/-- `PlaceCoordinates.placeCoord_free` as a case of `placeFamily_free`. -/
theorem placeCoord_free_of_placeFamily {n : ℕ} {p : X → Fin n} (hp : p ∈ PlaceCoord q n)
    {σ : Equiv.Perm X} (hσ : σ ∈ licenseStabilizer q) (hfix : p ∘ σ.symm = p) : σ = 1 := by
  have h : (⟨σ, hσ⟩ : licenseStabilizer q) • ofPlaceCoord q hp = ofPlaceCoord q hp := by
    apply (placeCoordEquiv q n).injective
    apply Subtype.ext
    show toPlaceCoord q (_ • ofPlaceCoord q hp) = toPlaceCoord q (ofPlaceCoord q hp)
    rw [toPlaceCoord_smul]
    exact hfix
  exact congrArg Subtype.val (placeFamily_free q _ _ h)

/-- `PlaceCoordinates.placeCoord_transitive` as a case of `placeFamily_transitive`. -/
theorem placeCoord_transitive_of_placeFamily {n : ℕ} {p p' : X → Fin n}
    (hp : p ∈ PlaceCoord q n) (hp' : p' ∈ PlaceCoord q n) :
    ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm := by
  obtain ⟨σ, hσ⟩ := placeFamily_transitive q (ofPlaceCoord q hp) (ofPlaceCoord q hp')
  refine ⟨σ, σ.2, ?_⟩
  have h := congrArg (toPlaceCoord q) hσ
  rw [toPlaceCoord_smul] at h
  exact h.symm

end General

/-! ## The control: a common alphabet for fibers of unequal size -/

/--
The common-alphabet orbit statement fails for fibers of unequal size.

Proves: for `q : Fin 3 → Bool` with `q 0 = q 1 = false` and `q 2 = true` and the common alphabet
`Fin 2`, the maps `p = (0, 1, 0)` and `p' = (0, 1, 1)` both resolve `q` together with the record,
and no invisible permutation `σ` gives `p' = p ∘ σ⁻¹`: every invisible permutation fixes `2`, and
`p 2 ≠ p' 2`.
Does not prove: anything about families with an alphabet per fiber, which form one free orbit by
`placeFamily_exists_unique`.
Relation: none. Trust: kernel-only.
-/
theorem common_alphabet_two_orbits (q : Fin 3 → Bool) (h0 : q 0 = false) (h1 : q 1 = false)
    (h2 : q 2 = true) :
    ∃ p p' : Fin 3 → Fin 2,
      Function.Injective (fun x => (q x, p x)) ∧ Function.Injective (fun x => (q x, p' x)) ∧
        ¬ ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm := by
  have hq : q = ![false, false, true] := by
    funext x
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
  subst hq
  refine ⟨![0, 1, 0], ![0, 1, 1], by decide, by decide, ?_⟩
  rintro ⟨σ, hσ, heq⟩
  have hrec := (mem_licenseStabilizer_iff _ σ).1 hσ (σ.symm 2)
  rw [Equiv.apply_symm_apply] at hrec
  have honly : ∀ k : Fin 3,
      (![false, false, true] : Fin 3 → Bool) 2 = ![false, false, true] k → k = 2 := by
    decide
  have hfix : σ.symm 2 = 2 := honly _ hrec
  have h := congrFun heq 2
  rw [Function.comp_apply, hfix] at h
  revert h
  decide

/--
The common alphabet splits the resolving coordinates of the three-state control into two orbits.

Proves: for `q : Fin 3 → Bool` with `q 0 = q 1 = false` and `q 2 = true` and the common alphabet
`Fin 2`, exactly four maps `p : Fin 3 → Fin 2` resolve `q` together with the record; the maps
`(0, 1, 0)` and `(0, 1, 1)` lie in distinct orbits of the invisible group, and every resolving map
lies in the orbit of one of them. The two orbits are the maps with `p 2 = 0` and the maps with
`p 2 = 1`, since every invisible permutation fixes `2`.
Does not prove: anything about families with an alphabet per fiber, which form one free orbit by
`placeFamily_exists_unique`.
Relation: none. Trust: kernel-only.
-/
theorem common_alphabet_four_coordinates_two_orbits (q : Fin 3 → Bool) (h0 : q 0 = false)
    (h1 : q 1 = false) (h2 : q 2 = true) :
    Fintype.card {p : Fin 3 → Fin 2 // Function.Injective (fun x => (q x, p x))} = 4 ∧
      ∃ p p' : Fin 3 → Fin 2,
        Function.Injective (fun x => (q x, p x)) ∧ Function.Injective (fun x => (q x, p' x)) ∧
        (¬ ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm) ∧
        ∀ r : Fin 3 → Fin 2, Function.Injective (fun x => (q x, r x)) →
          (∃ σ ∈ licenseStabilizer q, r = p ∘ σ.symm) ∨
            ∃ σ ∈ licenseStabilizer q, r = p' ∘ σ.symm := by
  have hq : q = ![false, false, true] := by
    funext x
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
  subst hq
  have hone : (1 : Equiv.Perm (Fin 3)) ∈ licenseStabilizer ![false, false, true] :=
    (licenseStabilizer _).one_mem
  have hswap : Equiv.swap (0 : Fin 3) 1 ∈ licenseStabilizer ![false, false, true] :=
    (mem_licenseStabilizer_iff _ _).2 (by decide)
  refine ⟨by decide, ![0, 1, 0], ![0, 1, 1], by decide, by decide, ?_, ?_⟩
  · rintro ⟨σ, hσ, heq⟩
    have hrec := (mem_licenseStabilizer_iff _ σ).1 hσ (σ.symm 2)
    rw [Equiv.apply_symm_apply] at hrec
    have honly : ∀ k : Fin 3,
        (![false, false, true] : Fin 3 → Bool) 2 = ![false, false, true] k → k = 2 := by
      decide
    have hfix : σ.symm 2 = 2 := honly _ hrec
    have h := congrFun heq 2
    rw [Function.comp_apply, hfix] at h
    revert h
    decide
  · intro r hr
    have hcases : r = ![0, 1, 0] ∨ r = ![1, 0, 0] ∨ r = ![0, 1, 1] ∨ r = ![1, 0, 1] := by
      revert r
      decide
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨1, hone, by decide⟩
    · exact Or.inl ⟨Equiv.swap 0 1, hswap, by decide⟩
    · exact Or.inr ⟨1, hone, by decide⟩
    · exact Or.inr ⟨Equiv.swap 0 1, hswap, by decide⟩

end OperatorKO7.Meta.BoundaryObserver.PlaceOrbitGeneral
