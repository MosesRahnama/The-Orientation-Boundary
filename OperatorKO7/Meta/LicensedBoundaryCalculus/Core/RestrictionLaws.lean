import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.PartialComposition

/-!
# Restriction laws and exact totalization

State-domain and edge-license restrictions are independent idempotent
operations on partial licensed morphisms.  The module also proves the exact
criterion for eliminating partiality: a partial morphism comes from a total
licensed morphism exactly when every source state belongs to its domain.

## Audit slots

Relation: source-domain predicates and admitted source-edge subrelations.
Closure: one-step simulation inherited by restriction; no closure upgrade.
Trust: kernel-only.  Equality laws use `propext` through extensionality.
Scope: universal restriction algebra and totalization characterization.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Restrict the defined source states by an additional predicate. -/
def restrictDomain (F : PartialLicensedReductionMorphism A B)
    (P : A.Carrier -> Prop) : PartialLicensedReductionMorphism A B where
  domain := fun x => F.domain x ∧ P x
  admitted := fun x y => F.admitted x y ∧ P x ∧ P y
  admitted_sub_raw := fun h => F.admitted_sub_raw h.1
  admitted_source_domain := fun h => ⟨F.admitted_source_domain h.1, h.2.1⟩
  admitted_target_domain := fun h => ⟨F.admitted_target_domain h.1, h.2.2⟩
  map := fun x => F.map ⟨x.val, x.property.1⟩
  map_step := by
    intro x y h
    convert F.map_step h.1

/-- Restrict the admitted source edges by an additional guard. -/
def restrictEdges (F : PartialLicensedReductionMorphism A B)
    (L : A.Carrier -> A.Carrier -> Prop) :
    PartialLicensedReductionMorphism A B where
  domain := F.domain
  admitted := fun x y => F.admitted x y ∧ L x y
  admitted_sub_raw := fun h => F.admitted_sub_raw h.1
  admitted_source_domain := fun h => F.admitted_source_domain h.1
  admitted_target_domain := fun h => F.admitted_target_domain h.1
  map := F.map
  map_step := fun h => F.map_step h.1

/-- Restriction by the universal state predicate changes nothing. -/
theorem restrictDomain_true (F : PartialLicensedReductionMorphism A B) :
    restrictDomain F (fun _ => True) = F := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    simp [restrictDomain]
  · intro x y
    simp [restrictDomain]
  · intro x hxRestricted hxF
    rfl

/-- Two state restrictions combine by conjunction. -/
theorem restrictDomain_comp (F : PartialLicensedReductionMorphism A B)
    (P Q : A.Carrier -> Prop) :
    restrictDomain (restrictDomain F P) Q =
      restrictDomain F (fun x => P x ∧ Q x) := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    simp [restrictDomain, and_assoc]
  · intro x y
    simp [restrictDomain, and_assoc, and_left_comm, and_comm]
  · intro x hxLeft hxRight
    rfl

/-- State restriction is idempotent. -/
theorem restrictDomain_idempotent (F : PartialLicensedReductionMorphism A B)
    (P : A.Carrier -> Prop) :
    restrictDomain (restrictDomain F P) P = restrictDomain F P := by
  rw [restrictDomain_comp]
  apply PartialLicensedReductionMorphism.ext
  · intro x
    simp
  · intro x y
    simp
  · intro x hxLeft hxRight
    rfl

/-- Restriction by the universal edge guard changes nothing. -/
theorem restrictEdges_true (F : PartialLicensedReductionMorphism A B) :
    restrictEdges F (fun _ _ => True) = F := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    rfl
  · intro x y
    simp [restrictEdges]
  · intro x hxRestricted hxF
    rfl

/-- Two edge restrictions combine by conjunction. -/
theorem restrictEdges_comp (F : PartialLicensedReductionMorphism A B)
    (L M : A.Carrier -> A.Carrier -> Prop) :
    restrictEdges (restrictEdges F L) M =
      restrictEdges F (fun x y => L x y ∧ M x y) := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    rfl
  · intro x y
    simp [restrictEdges, and_assoc]
  · intro x hxLeft hxRight
    rfl

/-- Edge restriction is idempotent. -/
theorem restrictEdges_idempotent (F : PartialLicensedReductionMorphism A B)
    (L : A.Carrier -> A.Carrier -> Prop) :
    restrictEdges (restrictEdges F L) L = restrictEdges F L := by
  rw [restrictEdges_comp]
  apply PartialLicensedReductionMorphism.ext
  · intro x
    rfl
  · intro x y
    simp
  · intro x hxLeft hxRight
    rfl

/-- State and edge restriction commute because they modify independent fields. -/
theorem restrictDomain_restrictEdges_comm
    (F : PartialLicensedReductionMorphism A B)
    (P : A.Carrier -> Prop) (L : A.Carrier -> A.Carrier -> Prop) :
    restrictDomain (restrictEdges F L) P =
      restrictEdges (restrictDomain F P) L := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    rfl
  · intro x y
    simp [restrictDomain, restrictEdges, and_assoc, and_left_comm, and_comm]
  · intro x hxLeft hxRight
    rfl

/-- Every source state lies in the domain. -/
def IsTotal (F : PartialLicensedReductionMorphism A B) : Prop :=
  forall x, F.domain x

/-- A total-domain partial morphism produces an ordinary licensed morphism. -/
def toTotal (F : PartialLicensedReductionMorphism A B) (hTotal : F.IsTotal) :
    LicensedReductionMorphism A B where
  admitted := F.admitted
  admitted_sub_raw := F.admitted_sub_raw
  map := fun x => F.map ⟨x, hTotal x⟩
  map_step := by
    intro x y h
    convert F.map_step h

/-- Re-embedding a totalization recovers the original partial morphism. -/
theorem toTotal_toPartial (F : PartialLicensedReductionMorphism A B)
    (hTotal : F.IsTotal) :
    (F.toTotal hTotal).toPartial = F := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    constructor
    · intro _
      exact hTotal x
    · intro _
      trivial
  · intro x y
    rfl
  · intro x hxEmbedded hxF
    rfl

/-- Exact universal totalization criterion.  No total representative exists
precisely when at least one source state is outside the domain. -/
theorem isTotal_iff_exists_total_morphism
    (F : PartialLicensedReductionMorphism A B) :
    F.IsTotal <->
      exists T : LicensedReductionMorphism A B, T.toPartial = F := by
  constructor
  · intro hTotal
    exact ⟨F.toTotal hTotal, F.toTotal_toPartial hTotal⟩
  · rintro ⟨T, rfl⟩
    intro x
    trivial

/-- The genuinely partial fixture has no total licensed representative. -/
theorem partialChain_no_total_morphism_fixture :
    Not (exists T : LicensedReductionMorphism chainARS_fixture chainARS_fixture,
      T.toPartial = partialChain_fixture) := by
  intro h
  have hTotal := (isTotal_iff_exists_total_morphism partialChain_fixture).2 h
  exact partialChain_fixture_undefined_target (hTotal ChainNode.target)

#check @restrictDomain
#check @restrictEdges
#check @restrictDomain_idempotent
#check @restrictEdges_idempotent
#check @restrictDomain_restrictEdges_comm
#check @isTotal_iff_exists_total_morphism
#check partialChain_no_total_morphism_fixture
#print axioms restrictDomain
#print axioms restrictEdges
#print axioms restrictDomain_idempotent
#print axioms restrictEdges_idempotent
#print axioms restrictDomain_restrictEdges_comm
#print axioms isTotal_iff_exists_total_morphism
#print axioms partialChain_no_total_morphism_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
