import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice

/-!
# Functional dependencies as licenses

A family of tuples satisfies the functional dependency `Y → Z` when tuples that agree on `Y`
agree on `Z`. This is the license of the restriction to `Z` by the restriction to `Y`. The rules
of Armstrong derive exactly the dependencies that every instance satisfying a list of
dependencies satisfies, and instances with two Boolean tuples refute every other dependency. A
family of licenses is a list of single-attribute dependencies.

Relation: agreement of tuples on attribute sets.
Property: dependency equals license; Armstrong soundness and completeness; lists of dependencies.
Trust: kernel only; completeness uses classical decidability of derivability.
Scope: arbitrary index, attribute, and value types; attribute sets are `Finset`s.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DependencyLicense

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

universe u v w
universe u' v' uX

section Dependency

variable {X : Type u} {A : Type v} {D : Type w}

/-- The restriction of a tuple to the attribute set `Y`. -/
def restrictTo (Y : Finset A) (t : A → D) : Y → D := fun a => t a.1

theorem restrictTo_eq_iff (Y : Finset A) (s t : A → D) :
    restrictTo Y s = restrictTo Y t ↔ ∀ a ∈ Y, s a = t a := by
  constructor
  · intro h a ha
    exact congrFun h ⟨a, ha⟩
  · intro h
    funext a
    exact h a.1 a.2

/-- The functional dependency `Y → Z` holds on the tuples indexed by `S`. -/
def FDHoldsOn (S : Set X) (tup : X → A → D) (Y Z : Finset A) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, (∀ a ∈ Y, tup x a = tup y a) → ∀ b ∈ Z, tup x b = tup y b

/-- **A functional dependency is a license** of the right restriction by the left restriction. -/
theorem fdHoldsOn_iff_licensedOn (S : Set X) (tup : X → A → D) (Y Z : Finset A) :
    FDHoldsOn S tup Y Z ↔
      LicensedOn S (fun x => restrictTo Y (tup x)) (fun x => restrictTo Z (tup x)) := by
  simp only [FDHoldsOn, LicensedOn, restrictTo_eq_iff]

theorem fdHoldsOn_of_subset (S : Set X) (tup : X → A → D) {Y Z : Finset A} (h : Z ⊆ Y) :
    FDHoldsOn S tup Y Z := by
  intro x _ y _ hY b hb
  exact hY b (h hb)

theorem FDHoldsOn.augment [DecidableEq A] {S : Set X} {tup : X → A → D} {Y Z : Finset A}
    (W : Finset A) (h : FDHoldsOn S tup Y Z) : FDHoldsOn S tup (Y ∪ W) (Z ∪ W) := by
  intro x hx y hy hYW b hb
  rcases Finset.mem_union.1 hb with hbZ | hbW
  · exact h x hx y hy (fun a ha => hYW a (Finset.mem_union.2 (Or.inl ha))) b hbZ
  · exact hYW b (Finset.mem_union.2 (Or.inr hbW))

theorem FDHoldsOn.trans {S : Set X} {tup : X → A → D} {Y Z W : Finset A}
    (h₁ : FDHoldsOn S tup Y Z) (h₂ : FDHoldsOn S tup Z W) : FDHoldsOn S tup Y W := by
  intro x hx y hy hY
  exact h₂ x hx y hy (h₁ x hx y hy hY)

theorem fdHoldsOn_union_iff [DecidableEq A] (S : Set X) (tup : X → A → D) (Y Z₁ Z₂ : Finset A) :
    FDHoldsOn S tup Y (Z₁ ∪ Z₂) ↔ FDHoldsOn S tup Y Z₁ ∧ FDHoldsOn S tup Y Z₂ := by
  constructor
  · intro h
    exact ⟨fun x hx y hy hY b hb => h x hx y hy hY b (Finset.mem_union.2 (Or.inl hb)),
      fun x hx y hy hY b hb => h x hx y hy hY b (Finset.mem_union.2 (Or.inr hb))⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy hY b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact h₁ x hx y hy hY b hb
    · exact h₂ x hx y hy hY b hb

/-- License form of the union rule. -/
theorem licensedOn_jointPair_iff {Q V₁ V₂ : Type*} (S : Set X) (q : X → Q) (P₁ : X → V₁)
    (P₂ : X → V₂) :
    LicensedOn S q (jointPair P₁ P₂) ↔ LicensedOn S q P₁ ∧ LicensedOn S q P₂ := by
  constructor
  · intro h
    exact ⟨fun x hx y hy hq => congrArg Prod.fst (h x hx y hy hq),
      fun x hx y hy hq => congrArg Prod.snd (h x hx y hy hq)⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy hq
    exact Prod.ext (h₁ x hx y hy hq) (h₂ x hx y hy hq)

/-- License form for an indexed family of targets. -/
theorem licensedOn_pi_iff {ι Q : Type*} {V : ι → Type*} (S : Set X) (q : X → Q)
    (P : (i : ι) → X → V i) :
    LicensedOn S q (fun x i => P i x) ↔ ∀ i, LicensedOn S q (P i) := by
  constructor
  · intro h i x hx y hy hq
    exact congrFun (h x hx y hy hq) i
  · intro h x hx y hy hq
    funext i
    exact h i x hx y hy hq

end Dependency

section Armstrong

variable {A : Type v} [DecidableEq A]

/-- A dependency `Y → Z` as its pair of attribute sets. -/
abbrev FD (A : Type v) := Finset A × Finset A

/-- Derivability from the list `Δ` by the rules of Armstrong. -/
inductive ArmstrongDerivable (Δ : List (FD A)) : Finset A → Finset A → Prop
  | member {Y Z : Finset A} : (Y, Z) ∈ Δ → ArmstrongDerivable Δ Y Z
  | refl {Y Z : Finset A} : Z ⊆ Y → ArmstrongDerivable Δ Y Z
  | augment {Y Z : Finset A} (W : Finset A) :
      ArmstrongDerivable Δ Y Z → ArmstrongDerivable Δ (Y ∪ W) (Z ∪ W)
  | trans {Y Z W : Finset A} :
      ArmstrongDerivable Δ Y Z → ArmstrongDerivable Δ Z W → ArmstrongDerivable Δ Y W

/-- Every instance whose tuples satisfy all dependencies of `Δ` satisfies `Y → Z`. -/
def SemanticallyImplies (Δ : List (FD A)) (Y Z : Finset A) : Prop :=
  ∀ (X D : Type) (tup : X → A → D),
    (∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2) → FDHoldsOn Set.univ tup Y Z

/-- The same statement over two tuples with Boolean values. -/
def TwoTupleImplies (Δ : List (FD A)) (Y Z : Finset A) : Prop :=
  ∀ tup : Bool → A → Bool,
    (∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2) → FDHoldsOn Set.univ tup Y Z

theorem armstrongDerivable_sound {Δ : List (FD A)} {Y Z : Finset A}
    (h : ArmstrongDerivable Δ Y Z) : SemanticallyImplies Δ Y Z := by
  intro X D tup hΔ
  induction h with
  | member hmem => exact hΔ _ hmem
  | refl hsub => exact fdHoldsOn_of_subset Set.univ tup hsub
  | augment W _ ih => exact FDHoldsOn.augment W ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ArmstrongDerivable.union {Δ : List (FD A)} {Y Z₁ Z₂ : Finset A}
    (h₁ : ArmstrongDerivable Δ Y Z₁) (h₂ : ArmstrongDerivable Δ Y Z₂) :
    ArmstrongDerivable Δ Y (Z₁ ∪ Z₂) := by
  have a : ArmstrongDerivable Δ Y (Z₁ ∪ Y) := by
    have := h₁.augment Y
    rwa [Finset.union_self] at this
  have b : ArmstrongDerivable Δ (Z₁ ∪ Y) (Z₂ ∪ Z₁) := by
    have := h₂.augment Z₁
    rwa [Finset.union_comm Y Z₁] at this
  have ab := a.trans b
  rwa [Finset.union_comm Z₂ Z₁] at ab

theorem ArmstrongDerivable.mono_right {Δ : List (FD A)} {Y Z W : Finset A}
    (h : ArmstrongDerivable Δ Y Z) (hW : W ⊆ Z) : ArmstrongDerivable Δ Y W :=
  h.trans (.refl hW)

theorem armstrongDerivable_iff_forall_singleton {Δ : List (FD A)} {Y Z : Finset A} :
    ArmstrongDerivable Δ Y Z ↔ ∀ a ∈ Z, ArmstrongDerivable Δ Y {a} := by
  constructor
  · intro h a ha
    exact h.mono_right (Finset.singleton_subset_iff.2 ha)
  · intro h
    induction Z using Finset.induction_on with
    | empty => exact .refl (Finset.empty_subset Y)
    | insert a s ha ih =>
        rw [Finset.insert_eq]
        exact (h a (Finset.mem_insert_self a s)).union
          (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- **Completeness of Armstrong's rules**, with two Boolean tuples. -/
theorem armstrongDerivable_of_twoTupleImplies {Δ : List (FD A)} {Y Z : Finset A}
    (h : TwoTupleImplies Δ Y Z) : ArmstrongDerivable Δ Y Z := by
  classical
  let tup : Bool → A → Bool := fun b a => b || decide (ArmstrongDerivable Δ Y {a})
  have F : ∀ a : A, tup true a = tup false a ↔ ArmstrongDerivable Δ Y {a} := by
    intro a
    show (true || decide (ArmstrongDerivable Δ Y {a})) =
        (false || decide (ArmstrongDerivable Δ Y {a})) ↔ _
    rw [Bool.true_or, Bool.false_or, eq_comm, decide_eq_true_iff]
  have hΔ : ∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2 := by
    intro p hp x _ y _ hagree b hb
    have hYp2_of : (∀ a ∈ p.1, ArmstrongDerivable Δ Y {a}) → ArmstrongDerivable Δ Y p.2 :=
      fun h1 => ((armstrongDerivable_iff_forall_singleton).2 h1).trans (.member hp)
    cases x <;> cases y
    · rfl
    · have h1 : ArmstrongDerivable Δ Y p.2 := hYp2_of fun a ha => (F a).1 (hagree a ha).symm
      exact ((F b).2 (h1.mono_right (Finset.singleton_subset_iff.2 hb))).symm
    · have h1 : ArmstrongDerivable Δ Y p.2 := hYp2_of fun a ha => (F a).1 (hagree a ha)
      exact (F b).2 (h1.mono_right (Finset.singleton_subset_iff.2 hb))
    · rfl
  have hY : ∀ a ∈ Y, tup true a = tup false a :=
    fun a ha => (F a).2 (.refl (Finset.singleton_subset_iff.2 ha))
  have hZ := h tup hΔ true trivial false trivial hY
  exact (armstrongDerivable_iff_forall_singleton).2 fun b hb => (F b).1 (hZ b hb)

/-- **Armstrong's theorem.** Derivability, implication over all instances, and implication over
two-tuple Boolean instances coincide. -/
theorem armstrongDerivable_iff_semanticallyImplies (Δ : List (FD A)) (Y Z : Finset A) :
    (ArmstrongDerivable Δ Y Z ↔ SemanticallyImplies Δ Y Z) ∧
      (SemanticallyImplies Δ Y Z ↔ TwoTupleImplies Δ Y Z) := by
  constructor
  · exact ⟨armstrongDerivable_sound,
      fun h => armstrongDerivable_of_twoTupleImplies fun tup hΔ => h Bool Bool tup hΔ⟩
  · exact ⟨fun h tup hΔ => h Bool Bool tup hΔ,
      fun h => armstrongDerivable_sound (armstrongDerivable_of_twoTupleImplies h)⟩

/-- Every instance whose tuples satisfy all dependencies of `Δ` satisfies `Y → Z`, with the
instance and value types in arbitrary universes. -/
def SemanticallyImpliesU (Δ : List (FD A)) (Y Z : Finset A) : Prop :=
  ∀ (X : Type u') (D : Type v') (tup : X → A → D),
    (∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2) → FDHoldsOn Set.univ tup Y Z

/-- **Soundness of Armstrong's rules over arbitrary universes.** -/
theorem armstrongDerivable_soundU {Δ : List (FD A)} {Y Z : Finset A}
    (h : ArmstrongDerivable Δ Y Z) : SemanticallyImpliesU Δ Y Z := by
  intro X D tup hΔ
  induction h with
  | member hmem => exact hΔ _ hmem
  | refl hsub => exact fdHoldsOn_of_subset Set.univ tup hsub
  | augment W _ ih => exact FDHoldsOn.augment W ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [DecidableEq A] in
/-- Transport of a dependency along the lift of a two-valued tuple family. -/
private theorem fdh_ulift_iff {X : Type u'} {t : X → A → Bool} (P Q : Finset A) :
    FDHoldsOn (Set.univ : Set X) (fun x a => (ULift.up (t x a) : ULift.{v', 0} Bool)) P Q ↔
      FDHoldsOn (Set.univ : Set X) t P Q := by
  constructor
  · intro h x _ y _ hagree b hb
    exact congrArg ULift.down
      (h x (Set.mem_univ x) y (Set.mem_univ y)
        (fun a ha => congrArg ULift.up (hagree a ha)) b hb)
  · intro h x _ y _ hagree b hb
    exact congrArg ULift.up
      (h x (Set.mem_univ x) y (Set.mem_univ y)
        (fun a ha => congrArg ULift.down (hagree a ha)) b hb)

omit [DecidableEq A] in
/-- Transport of a dependency along an equivalence of the index families. -/
private theorem fdh_equiv_iff {X : Type uX} {X' : Type u'} {D : Type w} (e : X' ≃ X)
    {t : X → A → D} (P Q : Finset A) :
    FDHoldsOn (Set.univ : Set X') (fun x' a => t (e x') a) P Q ↔
      FDHoldsOn (Set.univ : Set X) t P Q := by
  constructor
  · intro h x _ y _ hagree b hb
    have h' := h (e.symm x) (Set.mem_univ _) (e.symm y) (Set.mem_univ _)
      (fun a ha => by
        show t (e (e.symm x)) a = t (e (e.symm y)) a
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hagree a ha) b hb
    simpa [Equiv.apply_symm_apply] using h'
  · intro h x' _ y' _ hagree b hb
    exact h (e x') (Set.mem_univ _) (e y') (Set.mem_univ _)
      (fun a ha => hagree a ha) b hb

/-- **Completeness over arbitrary universes**, through the lifted two-valued instance. -/
theorem armstrongDerivable_of_semanticallyImpliesU {Δ : List (FD A)} {Y Z : Finset A}
    (h : ∀ (X : Type u') (D : Type v') (tup : X → A → D),
      (∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2) → FDHoldsOn Set.univ tup Y Z) :
    ArmstrongDerivable Δ Y Z := by
  classical
  apply armstrongDerivable_of_twoTupleImplies
  intro t hΔ
  let T : ULift.{u', 0} Bool → A → ULift.{v', 0} Bool := fun x a => ULift.up (t x.down a)
  let U : Bool → A → ULift.{v', 0} Bool := fun y a => ULift.up (t y a)
  have hUT : ∀ (P Q : Finset A), FDHoldsOn (Set.univ : Set (ULift.{u', 0} Bool)) T P Q ↔
      FDHoldsOn (Set.univ : Set Bool) U P Q :=
    fun P Q => fdh_equiv_iff (X := Bool) (X' := ULift.{u', 0} Bool) Equiv.ulift (t := U) P Q
  have hU := h (ULift.{u', 0} Bool) (ULift.{v', 0} Bool) T
    (fun p hp => (hUT p.1 p.2).2 ((fdh_ulift_iff p.1 p.2).2 (hΔ p hp)))
  exact (fdh_ulift_iff Y Z).1 ((hUT Y Z).1 hU)

/-- **The two-tuple instance and universal semantic implication agree.** -/
theorem semanticallyImpliesU_iff_twoTupleImplies (Δ : List (FD A)) (Y Z : Finset A) :
    (∀ (X : Type u') (D : Type v') (tup : X → A → D),
        (∀ p ∈ Δ, FDHoldsOn Set.univ tup p.1 p.2) → FDHoldsOn Set.univ tup Y Z) ↔
      TwoTupleImplies Δ Y Z := by
  constructor
  · intro h
    exact (armstrongDerivable_iff_semanticallyImplies Δ Y Z).2.1
      (armstrongDerivable_sound (armstrongDerivable_of_semanticallyImpliesU h))
  · intro h
    exact armstrongDerivable_soundU (armstrongDerivable_of_twoTupleImplies h)

/-- **Armstrong's theorem, universe-polymorphic.** -/
theorem armstrongDerivable_iff_semanticallyImplies_universal (Δ : List (FD A)) (Y Z : Finset A) :
    (ArmstrongDerivable Δ Y Z ↔ SemanticallyImpliesU Δ Y Z) ∧
      (SemanticallyImpliesU Δ Y Z ↔ TwoTupleImplies Δ Y Z) :=
  ⟨⟨armstrongDerivable_soundU, armstrongDerivable_of_semanticallyImpliesU⟩,
    semanticallyImpliesU_iff_twoTupleImplies Δ Y Z⟩

omit [DecidableEq A] in
/-- One tuple satisfies every dependency. -/
theorem oneTuple_satisfies_every_dependency (Y Z : Finset A) (tup : Unit → A → Bool) :
    FDHoldsOn Set.univ tup Y Z := by
  intro x _ y _ _ b _
  cases x
  cases y
  rfl

/-- **Two tuples are required**: the empty list does not derive `∅ → {true}`. -/
theorem twoTuple_family_is_required :
    ¬ ArmstrongDerivable ([] : List (FD Bool)) ∅ {true} := by
  intro h
  have hsem := armstrongDerivable_sound h
  have hholds := hsem Bool Bool (fun b _ => b) (by intro p hp; simp at hp)
  have heq := hholds true trivial false trivial (fun a ha => by simp at ha)
    true (Finset.mem_singleton_self true)
  exact Bool.noConfusion heq

end Armstrong

section Lists

variable {X : Type u} {A : Type v} {D : Type w}

/-- All dependencies of the list `Δ` hold on `S`. -/
def FDListHoldsOn (S : Set X) (tup : X → A → D) (Δ : List (FD A)) : Prop :=
  ∀ p ∈ Δ, FDHoldsOn S tup p.1 p.2

/-- **A list of dependencies is a family of licenses.** -/
theorem fdListHoldsOn_iff_licensedOn_each (S : Set X) (tup : X → A → D) (Δ : List (FD A)) :
    FDListHoldsOn S tup Δ ↔
      ∀ p ∈ Δ, LicensedOn S (fun x => restrictTo p.1 (tup x)) (fun x => restrictTo p.2 (tup x)) := by
  constructor
  · intro h p hp
    exact (fdHoldsOn_iff_licensedOn S tup p.1 p.2).1 (h p hp)
  · intro h p hp
    exact (fdHoldsOn_iff_licensedOn S tup p.1 p.2).2 (h p hp)

/-- The tuples that encode a family of observers and targets: attribute `inl i` holds the
`i`-th observation and attribute `inr i` the `i`-th target value. -/
def familyTuples {ι Q V : Type*} (q : ι → X → Q) (P : ι → X → V) : X → ι ⊕ ι → Q ⊕ V :=
  fun x a => Sum.elim (fun i => Sum.inl (q i x)) (fun i => Sum.inr (P i x)) a

/-- The single-attribute dependencies `inl i → inr i`. -/
def familyDependencies {ι : Type*} [DecidableEq ι] (is : List ι) : List (FD (ι ⊕ ι)) :=
  is.map fun i => ({Sum.inl i}, {Sum.inr i})

/-- **A family of licenses is a list of dependencies.** -/
theorem fdListHoldsOn_familyDependencies_iff {ι Q V : Type*} [DecidableEq ι] (S : Set X)
    (q : ι → X → Q) (P : ι → X → V) (is : List ι) :
    FDListHoldsOn S (familyTuples q P) (familyDependencies is) ↔
      ∀ i ∈ is, LicensedOn S (q i) (P i) := by
  constructor
  · intro h i hi
    have hf := h ({Sum.inl i}, {Sum.inr i}) (by
      simp only [familyDependencies, List.mem_map]
      exact ⟨i, hi, rfl⟩)
    intro x hx y hy hq
    have heq : ∀ a ∈ ({Sum.inl i} : Finset (ι ⊕ ι)),
        familyTuples q P x a = familyTuples q P y a := by
      intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      simp only [familyTuples, Sum.elim_inl]
      rw [hq]
    have hres := hf x hx y hy heq (Sum.inr i) (Finset.mem_singleton_self _)
    simpa only [familyTuples, Sum.elim_inr, Sum.inr.injEq] using hres
  · intro h p hp
    simp only [familyDependencies, List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    intro x hx y hy hagree
    have hq : q i x = q i y := by
      have := hagree (Sum.inl i) (Finset.mem_singleton_self _)
      simpa only [familyTuples, Sum.elim_inl, Sum.inl.injEq] using this
    have hP := h i hi x hx y hy hq
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    simpa only [familyTuples, Sum.elim_inr, Sum.inr.injEq] using hP

end Lists

end OperatorKO7.Meta.OperationalInexpressibility.DependencyLicense
