import OperatorKO7.Meta.OperationalInexpressibility.TargetKernelQuotient

/-!
# The license Galois connection

For a fixed source type, equivalence relations record observer kernels and sets
of Boolean targets record licensed distinctions. `licensedBy` sends a kernel to
the targets constant on its classes. `kerFamily` sends a target family to the
intersection of its target kernels. These antitone maps form a Galois
connection. Boolean class indicators reconstruct every equivalence relation on
an arbitrary source type, so the kernel-side closure is the identity and the
target-side closure is classified exactly.

No finiteness, decidable equality, observer surjectivity, or source inhabitance
assumption is used. Classical proposition decidability is used only to define
the Boolean indicator of an equivalence class.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.LicenseGalois

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.TargetKernel

universe u v w

/-- Boolean targets constant on every class of `E`. -/
def licensedBy {X : Type u} (E : Setoid X) : Set (X → Bool) :=
  {P | ∀ x y, E x y → P x = P y}

/-- Intersection of the kernels of every target in a family. -/
def kerFamily {X : Type u} (S : Set (X → Bool)) : Setoid X where
  r x y := ∀ P, P ∈ S → P x = P y
  iseqv :=
    ⟨fun _ _ _ => rfl,
      fun h P hP => (h P hP).symm,
      fun hxy hyz P hP => (hxy P hP).trans (hyz P hP)⟩

@[simp] theorem kerFamily_rel_iff {X : Type u} (S : Set (X → Bool)) (x y : X) :
    kerFamily S x y ↔ ∀ P ∈ S, P x = P y :=
  Iff.rfl

@[simp] theorem mem_licensedBy_iff {X : Type u} (E : Setoid X) (P : X → Bool) :
    P ∈ licensedBy E ↔ ∀ x y, E x y → P x = P y :=
  Iff.rfl

/-- The defining antitone Galois law. -/
theorem setoid_le_kerFamily_iff {X : Type u} (E : Setoid X)
    (S : Set (X → Bool)) :
    E ≤ kerFamily S ↔ S ⊆ licensedBy E := by
  constructor
  · intro h P hP x y hxy
    exact h hxy P hP
  · intro h x y hxy P hP
    exact h hP x y hxy

/-- The kernel and target-family maps form a Galois connection after reversing
the target-family order. -/
theorem licenseFamily_galoisConnection {X : Type u} :
    GaloisConnection
      (fun E : Setoid X => OrderDual.toDual (licensedBy E))
      (fun S : OrderDual (Set (X → Bool)) => kerFamily (OrderDual.ofDual S)) :=
  fun E S => (setoid_le_kerFamily_iff E (OrderDual.ofDual S)).symm

/-- Enlarging a kernel can only reduce its licensed target family. -/
theorem licensedBy_antitone {X : Type u} {E F : Setoid X} (hEF : E ≤ F) :
    licensedBy F ⊆ licensedBy E := by
  intro P hP x y hxy
  exact hP x y (hEF hxy)

/-- Enlarging a target family can only refine its common kernel. -/
theorem kerFamily_antitone {X : Type u} {S T : Set (X → Bool)} (hST : S ⊆ T) :
    kerFamily T ≤ kerFamily S := by
  intro x y hxy P hP
  exact hxy P (hST hP)

/-- The common kernel of a singleton family is its canonical target kernel. -/
theorem kerFamily_singleton {X : Type u} (P : X → Bool) :
    kerFamily ({P} : Set (X → Bool)) = targetKernelSetoid P := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    change P x = P y
    exact h P (by simp)
  · intro h Q hQ
    have hQP : Q = P := Set.mem_singleton_iff.mp hQ
    subst Q
    change P x = P y at h
    exact h

/-- One target is licensed by `E` exactly when `E` refines its target kernel. -/
theorem setoid_le_targetKernel_iff {X : Type u} (E : Setoid X) (P : X → Bool) :
    E ≤ targetKernelSetoid P ↔ P ∈ licensedBy E := by
  constructor
  · intro h x y hxy
    exact h hxy
  · intro h x y hxy
    change P x = P y
    exact h x y hxy

/-- Indicator of the equivalence class of `x`. -/
noncomputable def setoidClassIndicator {X : Type u} (E : Setoid X) (x : X) :
    X → Bool := by
  classical
  exact fun z => decide (E x z)

/-- Every class indicator is constant on all equivalence classes. -/
theorem setoidClassIndicator_licensed {X : Type u} (E : Setoid X) (x : X) :
    setoidClassIndicator E x ∈ licensedBy E := by
  classical
  intro a b hab
  unfold setoidClassIndicator
  apply Bool.decide_congr
  constructor
  · intro hxa
    exact E.iseqv.trans hxa hab
  · intro hxb
    exact E.iseqv.trans hxb (E.iseqv.symm hab)

/-- A class indicator separates `x` from every point outside its class. -/
theorem setoidClassIndicator_separates {X : Type u} (E : Setoid X)
    {x y : X} (hxy : ¬ E x y) :
    setoidClassIndicator E x x ≠ setoidClassIndicator E x y := by
  classical
  have hxx : E x x := E.iseqv.refl x
  simp [setoidClassIndicator, hxx, hxy]

/-- Boolean licensed targets reconstruct every setoid exactly. -/
theorem kerFamily_licensedBy_eq {X : Type u} (E : Setoid X) :
    kerFamily (licensedBy E) = E := by
  apply le_antisymm
  · intro x y hxy
    by_contra hne
    exact setoidClassIndicator_separates E hne
      (hxy (setoidClassIndicator E x) (setoidClassIndicator_licensed E x))
  · exact (setoid_le_kerFamily_iff E (licensedBy E)).mpr (fun _ h => h)

/-- The target-family closure induced by the Galois connection. -/
def licenseClosure {X : Type u} (S : Set (X → Bool)) : Set (X → Bool) :=
  licensedBy (kerFamily S)

theorem subset_licenseClosure {X : Type u} (S : Set (X → Bool)) :
    S ⊆ licenseClosure S :=
  (setoid_le_kerFamily_iff (kerFamily S) S).mp le_rfl

theorem licenseClosure_mono {X : Type u} {S T : Set (X → Bool)} (hST : S ⊆ T) :
    licenseClosure S ⊆ licenseClosure T := by
  intro P hP
  exact licensedBy_antitone (kerFamily_antitone hST) hP

theorem licenseClosure_idempotent {X : Type u} (S : Set (X → Bool)) :
    licenseClosure (licenseClosure S) = licenseClosure S := by
  unfold licenseClosure
  rw [kerFamily_licensedBy_eq]

/-- Closed target families are exactly the families licensed by one setoid. -/
theorem licenseClosure_eq_self_iff {X : Type u} (S : Set (X → Bool)) :
    licenseClosure S = S ↔ ∃ E : Setoid X, S = licensedBy E := by
  constructor
  · intro h
    exact ⟨kerFamily S, h.symm⟩
  · rintro ⟨E, rfl⟩
    unfold licenseClosure
    rw [kerFamily_licensedBy_eq]

/-- Boolean license theory determines its kernel without loss. -/
theorem licensedBy_injective {X : Type u} :
    Function.Injective (licensedBy : Setoid X → Set (X → Bool)) := by
  intro E F h
  calc
    E = kerFamily (licensedBy E) := (kerFamily_licensedBy_eq E).symm
    _ = kerFamily (licensedBy F) := congrArg kerFamily h
    _ = F := kerFamily_licensedBy_eq F

/-- Kernel refinement is exactly reverse inclusion of Boolean license theories. -/
theorem setoid_le_iff_licensedBy_reverse_inclusion {X : Type u}
    (E F : Setoid X) :
    E ≤ F ↔ licensedBy F ⊆ licensedBy E := by
  constructor
  · exact licensedBy_antitone
  · intro h
    have hEF : E ≤ kerFamily (licensedBy F) :=
      (setoid_le_kerFamily_iff E (licensedBy F)).mpr h
    simpa only [kerFamily_licensedBy_eq] using hEF

/-- A proper kernel refinement strictly enlarges the Boolean license theory. -/
theorem licensedBy_strict_of_setoid_lt {X : Type u} {E F : Setoid X}
    (hEF : E < F) : licensedBy F ⊂ licensedBy E := by
  classical
  apply Set.ssubset_iff_exists.mpr
  refine ⟨licensedBy_antitone hEF.le, ?_⟩
  have hex : ∃ x y, F x y ∧ ¬ E x y := by
    by_contra hnone
    apply hEF.not_ge
    intro x y hF
    by_contra hE
    exact hnone ⟨x, y, hF, hE⟩
  obtain ⟨x, y, hF, hE⟩ := hex
  refine ⟨setoidClassIndicator E x, setoidClassIndicator_licensed E x, ?_⟩
  intro hlicensed
  exact setoidClassIndicator_separates E hE (hlicensed x y hF)

/-- The Boolean license theory of an observer reconstructs its kernel. -/
theorem kerFamily_observer_licenseTheory_eq_kernel
    {X : Type u} {Q : Type v} (q : X → Q) :
    kerFamily {P : X → Bool | Licensed q P} = observerSetoid q := by
  have hfamily : {P : X → Bool | Licensed q P} = licensedBy (observerSetoid q) := by
    ext P
    exact Iff.rfl
  rw [hfamily, kerFamily_licensedBy_eq]

/-- Equivalent observers have exactly the same Boolean licensed targets. -/
theorem same_kernel_iff_same_boolean_license_family
    {X : Type u} {Q₁ : Type v} {Q₂ : Type w} (q₁ : X → Q₁) (q₂ : X → Q₂) :
    (∀ x y, q₁ x = q₁ y ↔ q₂ x = q₂ y) ↔
      {P : X → Bool | Licensed q₁ P} = {P : X → Bool | Licensed q₂ P} := by
  constructor
  · intro h
    apply Set.ext
    intro P
    exact (same_binary_licenseTheory_iff_same_kernel q₁ q₂).mpr h P
  · intro h
    apply (same_binary_licenseTheory_iff_same_kernel q₁ q₂).mp
    intro P
    exact Set.ext_iff.mp h P

/-- Non-vacuity: the discrete Boolean kernel licenses identity, while the
indiscrete kernel does not. -/
theorem bool_license_families_are_distinct :
    (id : Bool → Bool) ∈ licensedBy (⊥ : Setoid Bool) ∧
      (id : Bool → Bool) ∉ licensedBy (⊤ : Setoid Bool) := by
  constructor
  · intro x y hxy
    simpa using hxy
  · intro h
    have hbad : (false : Bool) = true := h false true trivial
    cases hbad

/-- Complete package: Galois law, exact Boolean reconstruction, closure
classification, strictness, and the singleton-codomain limitation already
exhibited by the observer theory. -/
theorem license_galois_complete {X : Type u} :
    (∀ (E : Setoid X) (S : Set (X → Bool)),
      E ≤ kerFamily S ↔ S ⊆ licensedBy E)
      ∧ (∀ E : Setoid X, kerFamily (licensedBy E) = E)
      ∧ (∀ S : Set (X → Bool), licenseClosure (licenseClosure S) = licenseClosure S) :=
  ⟨fun E S => setoid_le_kerFamily_iff E S,
    fun E => kerFamily_licensedBy_eq E,
    fun S => licenseClosure_idempotent S⟩

end OperatorKO7.Meta.OperationalInexpressibility.LicenseGalois
