import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedARS

/-!
# Licensed reduction morphisms

A licensed reduction morphism combines an edge filter with a state map.  The
filter is a proved subrelation of the source, and every admitted edge maps to a
target edge.  The source and target audit scopes remain visible in their `ARS`
arguments.

## Audit slots

Relation: `A.step`, the admitted subrelation, and `B.step`.
Closure: one-step simulation plus finite-path and reflexive-transitive transport.
Trust: kernel-only; the public theorems use at most `propext`.
Scope: relation filtering and state-map simulation between abstract systems.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

/-- A state map together with a licensed source-edge filter and a one-step
simulation law. -/
structure LicensedReductionMorphism (A : ARS.{u}) (B : ARS.{v}) where
  /-- Source edges admitted by the license. -/
  admitted : A.Carrier -> A.Carrier -> Prop
  /-- Admission removes source edges and introduces none. -/
  admitted_sub_raw : forall {x y}, admitted x y -> A.step x y
  /-- State projection, quotient, interpretation, or identity map. -/
  map : A.Carrier -> B.Carrier
  /-- Every admitted source edge is simulated by one target edge. -/
  map_step : forall {x y}, admitted x y -> B.step (map x) (map y)

namespace LicensedReductionMorphism

variable {A : ARS.{u}} {B : ARS.{v}}

/-- The admitted source relation as its own guarded reduction system. -/
def admittedSystem (F : LicensedReductionMorphism A B) : ARS.{u} where
  Carrier := A.Carrier
  step := F.admitted
  scope := { A.scope with admission := .guarded }

/-- The morphism's admission proof exposes a raw source edge. -/
theorem admitted_is_source_step (F : LicensedReductionMorphism A B)
    {x y : A.Carrier} (h : F.admitted x y) : A.step x y :=
  F.admitted_sub_raw h

/-- Admitted paths map to target paths with the same length. -/
theorem map_steps (F : LicensedReductionMorphism A B) {n : Nat}
    {x y : A.Carrier} (h : Steps F.admittedSystem n x y) :
    Steps B n (F.map x) (F.map y) :=
  Steps.map (A := F.admittedSystem) (B := B) F.map F.map_step h

/-- One-step simulation lifts to reflexive-transitive reachability. -/
theorem reach_map (F : LicensedReductionMorphism A B) {x y : A.Carrier}
    (h : Reach F.admittedSystem x y) : Reach B (F.map x) (F.map y) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, F.map_steps hn⟩

/-- Extensional equality compares the admitted relation and state map.  The two
proof fields then agree by proof irrelevance. -/
@[ext] theorem ext (F G : LicensedReductionMorphism A B)
    (hAdmitted : forall x y, F.admitted x y <-> G.admitted x y)
    (hMap : F.map = G.map) : F = G := by
  cases F with
  | mk admittedF subF mapF mapStepF =>
      cases G with
      | mk admittedG subG mapG mapStepG =>
          dsimp at hAdmitted hMap
          cases hMap
          have hrel : admittedF = admittedG := by
            funext x y
            exact propext (hAdmitted x y)
          cases hrel
          rfl

/-! ## Non-vacuity fixture -/

/-- Identity state map and full admission on the two-state chain. -/
def chainMorphism_fixture :
    LicensedReductionMorphism chainARS_fixture chainARS_fixture where
  admitted := chainARS_fixture.step
  admitted_sub_raw := fun h => h
  map := id
  map_step := fun h => h

/-- The fixture maps its genuine admitted edge to the target edge. -/
theorem chainMorphism_maps_edge_fixture :
    chainARS_fixture.step
      (chainMorphism_fixture.map ChainNode.source)
      (chainMorphism_fixture.map ChainNode.target) :=
  chainMorphism_fixture.map_step ChainStep.descend

#check @LicensedReductionMorphism.ext
#check @LicensedReductionMorphism.map_steps
#check @LicensedReductionMorphism.reach_map
#check chainMorphism_maps_edge_fixture
#print axioms LicensedReductionMorphism.ext
#print axioms LicensedReductionMorphism.map_steps
#print axioms LicensedReductionMorphism.reach_map
#print axioms chainMorphism_maps_edge_fixture

end LicensedReductionMorphism

end OperatorKO7.Meta.LicensedBoundaryCalculus
