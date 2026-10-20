import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport
import OperatorKO7.Meta.DistinctionBoundary.GateTheorem
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient

/-!
# Boundary object functor on lifting morphisms

The boundary object of a licensing datum is its greatest persistent sublicense:
`Bd D x := Box D.dynamics D.license x`.  A licensing morphism transports this
object when target steps lift to source steps and the morphism advertises the
license-preservation capability.  It reflects the object from target to source
through the ordinary dynamics simulation already carried by every morphism and
the license-reflection capability.

The induced map on the `BdCarrier` subtype preserves identities and
composition.  Four concrete fibers instantiate the same object: the KO7
persistent comparator, compact-uniform metric separation, role erasure, and
the dependency-pair channel.

Relation: `LicensingDatum.dynamics` and its reflexive-transitive closure.
Closure: `Relation.ReflTransGen` inside `Box`.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

open Set
open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGradeTransport
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
open OperatorKO7.Meta.DistinctionBoundary.GateTheorem
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingCompletionRule
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
open OperatorKO7.Analysis.UniformSeparation

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor

universe v w v' w' v'' w''

/-- The boundary predicate of a licensing datum: the greatest forward-stable
part of its license. -/
abbrev Bd (D : LicensingDatum.{0,v,w}) : D.Carrier → Prop :=
  Box D.dynamics D.license

/-- The carrier of the boundary object. -/
def BdCarrier (D : LicensingDatum.{0,v,w}) : Type :=
  {x : D.Carrier // Bd D x}

/-- Dynamics restricted to the boundary carrier. -/
def restrictedDynamics (D : LicensingDatum.{0,v,w}) :
    BdCarrier D → BdCarrier D → Prop :=
  fun x y => D.dynamics x.1 y.1

/-- `Bd` is the greatest forward-invariant sublicense of the datum's license. -/
theorem bd_greatest_forwardInvariant (D : LicensingDatum.{0,v,w})
    (Q : D.Carrier → Prop)
    (hsub : ∀ x, Q x → D.license x)
    (hinv : ForwardInvariant D.dynamics Q) {x : D.Carrier}
    (hx : Q x) : Bd D x :=
  box_greatest hsub hinv hx

/-- The exact extra law needed for forward boundary transport. -/
def StepLiftingHom {A : LicensingDatum.{0,v,w}}
    {B : LicensingDatum.{0,v',w'}} (f : Hom A B) : Prop :=
  StepLifting f.stateMap A.dynamics B.dynamics

/-- A lifting, license-preserving morphism transports the persistent boundary
object. -/
theorem bd_transport_of_lifting
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (f : Hom A B) (hlift : StepLiftingHom f)
    (hpres : f.tag.preserves = true) {x : A.Carrier}
    (hx : Bd A x) : Bd B (f.stateMap x) := by
  refine ⟨f.license_preserve hpres hx.holds, ?_⟩
  intro y' hy'
  obtain ⟨y, hy, hfy⟩ := stepLifting_reflTransGen hlift hy'
  subst hfy
  exact f.license_preserve hpres (hx.persists y hy)

/-- A reflecting morphism reflects the persistent boundary object.  Forward
path transport is supplied by the morphism's built-in dynamics simulation. -/
theorem bd_reflect_of_simulation
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (f : Hom A B) (hreflect : f.tag.reflects = true) {x : A.Carrier}
    (hx : Bd B (f.stateMap x)) : Bd A x := by
  refine ⟨f.license_reflect hreflect hx.holds, ?_⟩
  intro y hy
  have hsim : StepSimulation f.stateMap A.dynamics B.dynamics := by
    intro a b hab
    exact f.dynamics_preserve hab
  have hpath : Relation.ReflTransGen B.dynamics
      (f.stateMap x) (f.stateMap y) :=
    stepSimulation_reflTransGen hsim hy
  exact f.license_reflect hreflect (hx.persists (f.stateMap y) hpath)

/-- Identity state maps satisfy the lifting law. -/
theorem stepLiftingHom_id (D : LicensingDatum.{0,v,w}) :
    StepLiftingHom (Hom.id D) := by
  intro x y h
  exact ⟨y, h, rfl⟩

/-- Step lifting composes. -/
theorem stepLiftingHom_comp
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    {C : LicensingDatum.{0,v'',w''}}
    {f : Hom A B} {g : Hom B C}
    (hf : StepLiftingHom f) (hg : StepLiftingHom g) :
    StepLiftingHom (Hom.comp f g) := by
  intro x z hz
  obtain ⟨b, hb, hgb⟩ := hg hz
  obtain ⟨a, ha, hfa⟩ := hf hb
  refine ⟨a, ha, ?_⟩
  change g.stateMap (f.stateMap a) = z
  rw [hfa, hgb]

/-- License-preservation capability composes at the Boolean tag. -/
theorem preserves_comp
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    {C : LicensingDatum.{0,v'',w''}}
    {f : Hom A B} {g : Hom B C}
    (hf : f.tag.preserves = true) (hg : g.tag.preserves = true) :
    (Hom.comp f g).tag.preserves = true := by
  simp [Hom.comp, LicenseTransportTag.comp, hf, hg]

/-- The map induced on boundary carriers by a lifting, preserving morphism. -/
def BdMap
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (f : Hom A B) (hlift : StepLiftingHom f)
    (hpres : f.tag.preserves = true) : BdCarrier A → BdCarrier B :=
  fun x => ⟨f.stateMap x.1, bd_transport_of_lifting f hlift hpres x.2⟩

/-- Boundary transport preserves identity maps. -/
theorem bdMap_id (D : LicensingDatum.{0,v,w}) :
    BdMap (Hom.id D) (stepLiftingHom_id D) rfl = id := by
  funext x
  apply Subtype.ext
  rfl

/-- Boundary transport preserves composition. -/
theorem bdMap_comp
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    {C : LicensingDatum.{0,v'',w''}}
    (f : Hom A B) (g : Hom B C)
    (hf : StepLiftingHom f) (hg : StepLiftingHom g)
    (hpf : f.tag.preserves = true) (hpg : g.tag.preserves = true) :
    BdMap (Hom.comp f g) (stepLiftingHom_comp hf hg)
        (preserves_comp hpf hpg) =
      BdMap g hg hpg ∘ BdMap f hf hpf := by
  funext x
  apply Subtype.ext
  rfl

/-- Functor laws at an arbitrary composable pair of lifting,
license-preserving morphisms. -/
theorem boundaryObject_functorial_on_lifting_morphisms
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    {C : LicensingDatum.{0,v'',w''}}
    (f : Hom A B) (g : Hom B C)
    (hf : StepLiftingHom f) (hg : StepLiftingHom g)
    (hpf : f.tag.preserves = true) (hpg : g.tag.preserves = true) :
    BdMap (Hom.id A) (stepLiftingHom_id A) rfl = id ∧
      BdMap (Hom.comp f g) (stepLiftingHom_comp hf hg)
          (preserves_comp hpf hpg) =
        BdMap g hg hpg ∘ BdMap f hf hpf :=
  ⟨bdMap_id A, bdMap_comp f g hf hg hpf hpg⟩

/-! ## Four fibers -/

/-- KO7 comparator licensing datum. -/
def ko7Datum : LicensingDatum where
  Carrier := Trace × Trace
  Policy := Unit
  Output := Trace × Trace
  dynamics := PairStep
  license := Distinct
  permits := fun _ => PairStep
  consume := id

/-- The KO7 boundary object is the persistent D1p comparator license. -/
theorem ko7_bd_iff_d1p (a b : Trace) :
    Bd ko7Datum (a, b) ↔ D1p EqGuardedStep (id : Trace → Trace) a b :=
  ko7_box_iff_d1p a b

/-- The KO7 boundary object is definitionally persistent distinction. -/
theorem ko7_bd_is_persistent_distinct (p : Trace × Trace) :
    Bd ko7Datum p ↔ Box PairStep Distinct p :=
  Iff.rfl

/-- Metric licensing datum for one compact set and one separation margin. -/
def metricDatum (F : ℕ → ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : LicensingDatum where
  Carrier := ℕ
  Policy := Unit
  Output := ℕ
  dynamics := shiftStep
  license := fun n => ∀ z ∈ K, ε ≤ ‖F n z‖
  permits := fun _ => shiftStep
  consume := id

/-- Existence of a metric boundary point is exactly eventual pointwise
separation on the fixed compact set and margin. -/
theorem metric_bd_iff (F : ℕ → ℂ → ℂ) (K : Set ℂ) (ε : ℝ) :
    (∃ N, Bd (metricDatum F K ε) N) ↔
      ∃ N, ∀ n ≥ N, ∀ z ∈ K, ε ≤ ‖F n z‖ := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact hN.persists n ((reflTransGen_shiftStep_iff_le N n).2 hn)
  · rintro ⟨N, hN⟩
    refine ⟨N, ⟨hN N (Nat.le_refl N), ?_⟩⟩
    intro n hn
    exact hN n ((reflTransGen_shiftStep_iff_le N n).1 hn)

/-- Compact-uniform separation is exactly existence of boundary points in all
fixed compact-set/margin metric data. -/
theorem compactUniformSeparation_iff_forall_bd
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) :
    CompactUniformSeparation F U ↔
      ∀ K ⊆ U, IsCompact K →
        ∃ ε, 0 < ε ∧ ∃ N, Bd (metricDatum F K ε) N := by
  constructor
  · intro h K hKU hK
    rcases h K hKU hK with ⟨ε, hε, N, hN⟩
    exact ⟨ε, hε, (metric_bd_iff F K ε).2 ⟨N, hN⟩⟩
  · intro h K hKU hK
    rcases h K hKU hK with ⟨ε, hε, N, hN⟩
    rcases (metric_bd_iff F K ε).1 ⟨N, hN⟩ with ⟨N', hN'⟩
    exact ⟨ε, hε, N', hN'⟩

/-- Role-collapse dynamics. -/
def roleStep {Y : Type} (x y : Occ Y) : Prop :=
  y = roleCollapse x

/-- Role-sensitive licensing datum. -/
def roleDatum (Y : Type) : LicensingDatum where
  Carrier := Occ Y
  Policy := Unit
  Output := Occ Y
  dynamics := roleStep
  license := isActive
  permits := fun _ => roleStep
  consume := roleCollapse

/-- Every role boundary object is empty: one role-collapse step reaches the
unlicensed frame copy. -/
theorem role_bd_empty (Y : Type) (o : (roleDatum Y).Carrier) :
    ¬ Bd (roleDatum Y) o := by
  intro h
  have hframe : isActive (roleCollapse o) :=
    h.persists (roleCollapse o) (Relation.ReflTransGen.single rfl)
  rcases o with ⟨y, r⟩
  exact Role.noConfusion hframe

/-- Dependency-pair channel licensing datum. -/
def dpDatum (b s n : Trace) : LicensingDatum where
  Carrier := Occ Unit
  Policy := Unit
  Output := Bool
  dynamics := roleStep
  license := fun o => actualDPChannel b s n o = true
  permits := fun _ => roleStep
  consume := actualDPChannel b s n

/-- The active DP occurrence is licensed. -/
theorem dp_issue_licensed (b s n : Trace) :
    (dpDatum b s n).license (((), Role.active) : Occ Unit) :=
  (actualDPChannel_decodes_isActive b s n
    (((), Role.active) : Occ Unit)).2 rfl

/-- No DP channel state has a persistent boundary license under role collapse. -/
theorem dp_bd_empty (b s n : Trace) (o : (dpDatum b s n).Carrier) :
    ¬ Bd (dpDatum b s n) o := by
  intro h
  have hframe : actualDPChannel b s n (roleCollapse o) = true :=
    h.persists (roleCollapse o) (Relation.ReflTransGen.single rfl)
  have hactive : isActive (roleCollapse o) :=
    (actualDPChannel_decodes_isActive b s n (roleCollapse o)).1 hframe
  rcases o with ⟨u, r⟩
  cases u
  exact Role.noConfusion hactive

/-- The DP issue is currently licensed while the persistent boundary object is
empty. -/
theorem dp_bd_empty_but_issue_licensed (b s n : Trace) :
    (dpDatum b s n).license (((), Role.active) : Occ Unit) ∧
      ¬ Bd (dpDatum b s n) (((), Role.active) : Occ Unit) :=
  ⟨dp_issue_licensed b s n,
    dp_bd_empty b s n (((), Role.active) : Occ Unit)⟩

/-- Closed package showing that one generic boundary object has all four live
fibers as exact instances. -/
structure FourFiberInstances : Prop where
  ko7 : ∀ a b : Trace,
    Bd ko7Datum (a, b) ↔ D1p EqGuardedStep (id : Trace → Trace) a b
  metric : ∀ (F : ℕ → ℂ → ℂ) (U : Set ℂ),
    CompactUniformSeparation F U ↔
      ∀ K ⊆ U, IsCompact K →
        ∃ ε, 0 < ε ∧ ∃ N, Bd (metricDatum F K ε) N
  role : ∀ (Y : Type) (o : (roleDatum Y).Carrier), ¬ Bd (roleDatum Y) o
  dp : ∀ b s n : Trace,
    (dpDatum b s n).license (((), Role.active) : Occ Unit) ∧
      ¬ Bd (dpDatum b s n) (((), Role.active) : Occ Unit)

/-- The KO7 comparator, metric separation, role-erasure, and DP channel are
instances of the same persistent boundary object. -/
theorem four_fibers_are_instances : FourFiberInstances where
  ko7 := ko7_bd_iff_d1p
  metric := compactUniformSeparation_iff_forall_bd
  role := role_bd_empty
  dp := dp_bd_empty_but_issue_licensed

end OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor

