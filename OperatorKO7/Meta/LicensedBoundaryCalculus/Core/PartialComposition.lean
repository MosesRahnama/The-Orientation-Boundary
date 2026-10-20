import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.PartialLicensedReductionMorphism

/-!
# Composition algebra for partial licensed morphisms

Composition retains a source state iff the state lies in the first domain and
its image lies in the second domain. An edge belongs to the composed admission
relation iff the first morphism admits it and the second morphism admits its
image.

## Formal scope

Relation: composed admitted subrelations and composed one-step simulations.
Closure: one-step simulation plus reachability transport from the partial
morphism layer.
Trust: kernel-only. Equality laws use `propext` through extensionality.
Scope: identity, composition, unit laws, associativity, formulas, and fixtures
for partial licensed morphisms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w z

/-- Identity is total-domain, admits the full source relation, and maps states
identically. -/
def id (A : ARS.{u}) : PartialLicensedReductionMorphism A A where
  domain := fun _ => True
  admitted := A.step
  admitted_sub_raw := fun h => h
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := fun x => x.val
  map_step := fun h => h

/-- Sequential composition of partial licensed morphisms. -/
def comp {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    PartialLicensedReductionMorphism A C where
  domain := fun x =>
    F.domain x ∧ forall hx : F.domain x, G.domain (F.map ⟨x, hx⟩)
  admitted := fun x y =>
    exists hF : F.admitted x y,
      G.admitted
        (F.map ⟨x, F.admitted_source_domain hF⟩)
        (F.map ⟨y, F.admitted_target_domain hF⟩)
  admitted_sub_raw := by
    intro x y h
    rcases h with ⟨hF, _⟩
    exact F.admitted_sub_raw hF
  admitted_source_domain := by
    intro x y h
    rcases h with ⟨hF, hG⟩
    refine ⟨F.admitted_source_domain hF, ?_⟩
    intro hx
    convert G.admitted_source_domain hG
  admitted_target_domain := by
    intro x y h
    rcases h with ⟨hF, hG⟩
    refine ⟨F.admitted_target_domain hF, ?_⟩
    intro hy
    convert G.admitted_target_domain hG
  map := fun x =>
    G.map
      ⟨F.map ⟨x.val, x.property.1⟩,
        x.property.2 x.property.1⟩
  map_step := by
    intro x y h
    rcases h with ⟨hF, hG⟩
    convert G.map_step hG

/-- Domain formula for partial composition. -/
theorem comp_domain_iff {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) (x : A.Carrier) :
    (comp F G).domain x <->
      F.domain x ∧ forall hx : F.domain x, G.domain (F.map ⟨x, hx⟩) :=
  Iff.rfl

/-- Admission formula for partial composition. -/
theorem comp_admitted_iff {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) (x y : A.Carrier) :
    (comp F G).admitted x y <->
      exists hF : F.admitted x y,
        G.admitted
          (F.map ⟨x, F.admitted_source_domain hF⟩)
          (F.map ⟨y, F.admitted_target_domain hF⟩) :=
  Iff.rfl

/-- Map formula for partial composition. -/
theorem comp_map_eq {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C)
    (x : {x // (comp F G).domain x}) :
    (comp F G).map x =
      G.map
        ⟨F.map ⟨x.val, x.property.1⟩,
          x.property.2 x.property.1⟩ :=
  rfl

/-- Left identity law. -/
theorem id_comp {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) : comp (id A) F = F := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    constructor
    · intro h
      exact h.2 trivial
    · intro h
      exact ⟨trivial, fun _ => h⟩
  · intro x y
    constructor
    · rintro ⟨_, h⟩
      simpa [id] using h
    · intro h
      exact ⟨F.admitted_sub_raw h, by simpa [id] using h⟩
  · intro x hxComp hxF
    rfl

/-- Right identity law. -/
theorem comp_id {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) : comp F (id B) = F := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, fun _ => trivial⟩
  · intro x y
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, by simpa [id] using F.map_step h⟩
  · intro x hxComp hxF
    rfl

/-- Composition is associative. -/
theorem comp_assoc {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} {D : ARS.{z}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C)
    (H : PartialLicensedReductionMorphism C D) :
    comp (comp F G) H = comp F (comp G H) := by
  apply PartialLicensedReductionMorphism.ext
  · intro x
    constructor
    · intro h
      refine ⟨h.1.1, ?_⟩
      intro hx
      refine ⟨h.1.2 hx, ?_⟩
      intro hy
      have hFG : (comp F G).domain x := ⟨hx, fun _ => h.1.2 hx⟩
      convert h.2 hFG
    · intro h
      refine ⟨⟨h.1, fun hx => (h.2 hx).1⟩, ?_⟩
      intro hFG
      convert (h.2 hFG.1).2 ((h.2 hFG.1).1)
  · intro x y
    constructor
    · rintro ⟨⟨hF, hG⟩, hH⟩
      refine ⟨hF, ⟨hG, ?_⟩⟩
      convert hH
    · rintro ⟨hF, ⟨hG, hH⟩⟩
      refine ⟨⟨hF, hG⟩, ?_⟩
      convert hH
  · intro x hxLeft hxRight
    rfl

/-! ## Fixtures -/

/-- Pure edge rejection with total domain and identity state map. -/
def pureEdgeRejection_fixture :
    PartialLicensedReductionMorphism chainARS_fixture chainARS_fixture where
  domain := fun _ => True
  admitted := fun _ _ => False
  admitted_sub_raw := by intro x y h; cases h
  admitted_source_domain := by intro x y h; cases h
  admitted_target_domain := by intro x y h; cases h
  map := fun x => x.val
  map_step := by intro x y h; cases h

/-- Pure state collapse with full admission into a one-point target. -/
def pureStateCollapseTarget_fixture : ARS where
  Carrier := Unit
  step := fun _ _ => True
  scope :=
    { location := .root
      closure := .oneStep
      admission := .full
      layer := .projected }

/-- Pure state collapse: no edge rejection, but both states map to unit. -/
def pureStateCollapse_fixture :
    PartialLicensedReductionMorphism chainARS_fixture pureStateCollapseTarget_fixture where
  domain := fun _ => True
  admitted := chainARS_fixture.step
  admitted_sub_raw := fun h => h
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := fun _ => ()
  map_step := fun _ => trivial

/-- Combined partiality, edge rejection, and state collapse. -/
def combinedPartialEdgeCollapse_fixture :
    PartialLicensedReductionMorphism chainARS_fixture pureStateCollapseTarget_fixture where
  domain := fun x => x = ChainNode.source
  admitted := fun _ _ => False
  admitted_sub_raw := by intro x y h; cases h
  admitted_source_domain := by intro x y h; cases h
  admitted_target_domain := by intro x y h; cases h
  map := fun _ => ()
  map_step := by intro x y h; cases h

/-- The collapse fixture exhibits a target self-step whose source representative
has zero corresponding chain steps, so forward simulation lacks reflection. -/
theorem pureStateCollapse_not_step_reflecting_fixture :
    pureStateCollapseTarget_fixture.step
      (pureStateCollapse_fixture.map ⟨ChainNode.source, trivial⟩)
      (pureStateCollapse_fixture.map ⟨ChainNode.source, trivial⟩) /\
      ¬ chainARS_fixture.step ChainNode.source ChainNode.source := by
  constructor
  · trivial
  · intro h
    cases h

/-- The partial composition of the chain identity representative with the
partial fixture preserves the partial domain. -/
theorem partial_id_comp_fixture :
    comp (id chainARS_fixture) partialChain_fixture = partialChain_fixture :=
  id_comp partialChain_fixture

#check @PartialLicensedReductionMorphism.id
#check @PartialLicensedReductionMorphism.comp
#check @PartialLicensedReductionMorphism.comp_domain_iff
#check @PartialLicensedReductionMorphism.comp_admitted_iff
#check @PartialLicensedReductionMorphism.comp_map_eq
#check @PartialLicensedReductionMorphism.id_comp
#check @PartialLicensedReductionMorphism.comp_id
#check @PartialLicensedReductionMorphism.comp_assoc
#check pureEdgeRejection_fixture
#check pureStateCollapse_fixture
#check combinedPartialEdgeCollapse_fixture
#check pureStateCollapse_not_step_reflecting_fixture
#check partial_id_comp_fixture
#print axioms PartialLicensedReductionMorphism.id
#print axioms PartialLicensedReductionMorphism.comp
#print axioms PartialLicensedReductionMorphism.comp_domain_iff
#print axioms PartialLicensedReductionMorphism.comp_admitted_iff
#print axioms PartialLicensedReductionMorphism.comp_map_eq
#print axioms PartialLicensedReductionMorphism.id_comp
#print axioms PartialLicensedReductionMorphism.comp_id
#print axioms PartialLicensedReductionMorphism.comp_assoc
#print axioms pureStateCollapse_not_step_reflecting_fixture
#print axioms partial_id_comp_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
