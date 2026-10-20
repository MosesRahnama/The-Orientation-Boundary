import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedReductionMorphism

/-!
This module defines a reduction morphism whose laws apply on an admitted domain and lifts paths
through that relation. The included fixture demonstrates a non-total domain whose admitted edge
relation is empty.












-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

/-- Data record whose requirements are the fields displayed below.

-/
structure PartialLicensedReductionMorphism (A : ARS.{u}) (B : ARS.{v}) where
  /-- Field requirements are given by the displayed type. -/
  domain : A.Carrier -> Prop
  /-- Field requirements are given by the displayed type. -/
  admitted : A.Carrier -> A.Carrier -> Prop
  /-- Field requirements are given by the displayed type. -/
  admitted_sub_raw : forall {x y}, admitted x y -> A.step x y
  /-- Field requirements are given by the displayed type. -/
  admitted_source_domain : forall {x y}, admitted x y -> domain x
  /-- Field requirements are given by the displayed type. -/
  admitted_target_domain : forall {x y}, admitted x y -> domain y
  /-- Field requirements are given by the displayed type. -/
  map : {x // domain x} -> B.Carrier
  /-- Field requirements are given by the displayed type. -/
  map_step : forall {x y} (h : admitted x y),
    B.step (map ⟨x, admitted_source_domain h⟩)
      (map ⟨y, admitted_target_domain h⟩)

namespace LicensedReductionMorphism

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Definition with formal content given by the displayed type and body.
-/
def toPartial (F : LicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A B where
  domain := fun _ => True
  admitted := F.admitted
  admitted_sub_raw := F.admitted_sub_raw
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := fun x => F.map x.val
  map_step := fun h => F.map_step h

end LicensedReductionMorphism

namespace PartialLicensedReductionMorphism

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Definition with formal content given by the displayed type and body. -/
def admittedSystem (F : PartialLicensedReductionMorphism A B) : ARS.{u} where
  Carrier := {x // F.domain x}
  step := fun x y => F.admitted x.val y.val
  scope := { A.scope with admission := .guarded }

/-- Field requirements are given by the displayed type.

-/
@[ext] theorem ext (F G : PartialLicensedReductionMorphism A B)
    (hDomain : forall x, F.domain x <-> G.domain x)
    (hAdmitted : forall x y, F.admitted x y <-> G.admitted x y)
    (hMap : forall x (hxF : F.domain x) (hxG : G.domain x),
      F.map ⟨x, hxF⟩ = G.map ⟨x, hxG⟩) : F = G := by
  cases F with
  | mk domainF admittedF subF sourceF targetF mapF mapStepF =>
      cases G with
      | mk domainG admittedG subG sourceG targetG mapG mapStepG =>
          dsimp at hDomain hAdmitted hMap
          have hdomain : domainF = domainG := by
            funext x
            exact propext (hDomain x)
          have hadmitted : admittedF = admittedG := by
            funext x y
            exact propext (hAdmitted x y)
          cases hdomain
          cases hadmitted
          have hmap : mapF = mapG := by
            funext x
            exact hMap x.val x.property x.property
          cases hmap
          rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem map_steps (F : PartialLicensedReductionMorphism A B) {n : Nat}
    {x y : F.admittedSystem.Carrier} (h : Steps F.admittedSystem n x y) :
    Steps B n (F.map x) (F.map y) := by
  apply Steps.map (A := F.admittedSystem) (B := B) F.map _ h
  intro a b hab
  convert F.map_step hab using 1

/-- The displayed proposition follows from the stated hypotheses. -/
theorem reach_map (F : PartialLicensedReductionMorphism A B) {x y : A.Carrier}
    (hx : F.domain x) (hy : F.domain y)
    (h : Reach F.admittedSystem ⟨x, hx⟩ ⟨y, hy⟩) :
    Reach B (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, F.map_steps hn⟩

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body. -/
def partialChain_fixture :
    PartialLicensedReductionMorphism chainARS_fixture chainARS_fixture where
  domain := fun x => x = ChainNode.source
  admitted := fun _ _ => False
  admitted_sub_raw := by intro x y h; cases h
  admitted_source_domain := by intro x y h; cases h
  admitted_target_domain := by intro x y h; cases h
  map := fun x => x.val
  map_step := by intro x y h; cases h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem partialChain_fixture_undefined_target :
    ¬ partialChain_fixture.domain ChainNode.target := by
  intro h
  cases h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem chainMorphism_toPartial_domain_fixture
    (x : ChainNode) :
    (LicensedReductionMorphism.toPartial
      LicensedReductionMorphism.chainMorphism_fixture).domain x :=
  trivial

#check @PartialLicensedReductionMorphism.ext
#check @PartialLicensedReductionMorphism.map_steps
#check @PartialLicensedReductionMorphism.reach_map
#check @LicensedReductionMorphism.toPartial
#check partialChain_fixture_undefined_target
#check chainMorphism_toPartial_domain_fixture
#print axioms PartialLicensedReductionMorphism.ext
#print axioms PartialLicensedReductionMorphism.map_steps
#print axioms PartialLicensedReductionMorphism.reach_map
#print axioms LicensedReductionMorphism.toPartial
#print axioms partialChain_fixture_undefined_target
#print axioms chainMorphism_toPartial_domain_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
