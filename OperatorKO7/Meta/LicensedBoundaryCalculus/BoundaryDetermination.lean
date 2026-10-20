import OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor
import OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification
import Mathlib.Tactic.NormNum

/-!
# Boundary determination and the coupled-isomorphism law

A boundary isomorphism is an equivalence of persistent-license carriers that
preserves and reflects their restricted one-step dynamics. Such an isomorphism
transports and reflects finite paths and induces an equivalence between every
class of observables constant along those paths.

For finite boundary carriers, a release datum consists of a probability mass
and a release map. If both are transported along the same boundary
isomorphism, the released ensemble law is determined. The stronger statement
with separate isomorphisms for boundary, mass, and release is false. A two-state
countermodel uses an identity boundary isomorphism, a swap mass isomorphism,
and an identity release isomorphism; the resulting ensemble laws differ.

Relation: `restrictedDynamics` on persistent-license subtypes.
Closure: `Relation.ReflTransGen`.
Trust: kernel checked, Mathlib baseline only.
-/

set_option autoImplicit false

open scoped BigOperators
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryObjectFunctor
open OperatorKO7.Meta.DistinctionBoundary.DiagonalGradeStratification

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryDetermination

universe v w v' w' u

/-- An isomorphism of boundary objects is a carrier equivalence preserving and
reflecting the restricted one-step dynamics. -/
structure BoundaryIso (A : LicensingDatum.{0,v,w})
    (B : LicensingDatum.{0,v',w'}) where
  toEquiv : BdCarrier A ≃ BdCarrier B
  dynamics_iff : ∀ x y,
    restrictedDynamics A x y ↔
      restrictedDynamics B (toEquiv x) (toEquiv y)

namespace BoundaryIso

/-- Identity boundary isomorphism. -/
def refl (A : LicensingDatum.{0,v,w}) : BoundaryIso A A where
  toEquiv := Equiv.refl _
  dynamics_iff := by
    intro x y
    rfl

/-- Inverse boundary isomorphism. -/
def symm {A : LicensingDatum.{0,v,w}}
    {B : LicensingDatum.{0,v',w'}} (e : BoundaryIso A B) :
    BoundaryIso B A where
  toEquiv := e.toEquiv.symm
  dynamics_iff := by
    intro x y
    have h := e.dynamics_iff (e.toEquiv.symm x) (e.toEquiv.symm y)
    simpa using h.symm

/-- Composition of boundary isomorphisms. -/
def trans {A : LicensingDatum.{0,v,w}}
    {B : LicensingDatum.{0,v',w'}}
    {C : LicensingDatum.{0,u,u}}
    (e : BoundaryIso A B) (f : BoundaryIso B C) :
    BoundaryIso A C where
  toEquiv := e.toEquiv.trans f.toEquiv
  dynamics_iff := by
    intro x y
    exact (e.dynamics_iff x y).trans
      (f.dynamics_iff (e.toEquiv x) (e.toEquiv y))

/-- A boundary isomorphism transports every finite path. -/
theorem reflTransGen_forward
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) {x y : BdCarrier A}
    (h : Relation.ReflTransGen (restrictedDynamics A) x y) :
    Relation.ReflTransGen (restrictedDynamics B)
      (e.toEquiv x) (e.toEquiv y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        ((e.dynamics_iff _ _).1 hyz)

/-- A boundary isomorphism reflects every finite path. -/
theorem reflTransGen_reflect
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) {x y : BdCarrier A}
    (h : Relation.ReflTransGen (restrictedDynamics B)
      (e.toEquiv x) (e.toEquiv y)) :
    Relation.ReflTransGen (restrictedDynamics A) x y := by
  have hback := (symm e).reflTransGen_forward h
  simpa [symm] using hback

/-- Boundary isomorphisms preserve and reflect finite reachability. -/
theorem reflTransGen_iff
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) (x y : BdCarrier A) :
    Relation.ReflTransGen (restrictedDynamics A) x y ↔
      Relation.ReflTransGen (restrictedDynamics B)
        (e.toEquiv x) (e.toEquiv y) :=
  ⟨e.reflTransGen_forward, e.reflTransGen_reflect⟩

end BoundaryIso

/-- Observables at the closure are functions constant along every finite path
of the restricted boundary dynamics. -/
def ObservableClass (A : LicensingDatum.{0,v,w}) (Obs : Type u) :=
  {q : BdCarrier A → Obs //
    ∀ x y, Relation.ReflTransGen (restrictedDynamics A) x y → q x = q y}

/-- Push an observable forward along a boundary isomorphism. -/
def observablePush
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) {Obs : Type u} :
    ObservableClass A Obs → ObservableClass B Obs :=
  fun q => ⟨fun y => q.1 (e.toEquiv.symm y), by
    intro x y hxy
    have hback := (BoundaryIso.symm e).reflTransGen_forward hxy
    exact q.2 (e.toEquiv.symm x) (e.toEquiv.symm y) hback⟩

/-- Pull an observable back along a boundary isomorphism. -/
def observablePull
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) {Obs : Type u} :
    ObservableClass B Obs → ObservableClass A Obs :=
  observablePush (BoundaryIso.symm e)

/-- Isomorphic boundary objects have equivalent observable classes at every
codomain. -/
def boundaryIso_equiv_observableClass
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    (e : BoundaryIso A B) (Obs : Type u) :
    ObservableClass A Obs ≃ ObservableClass B Obs where
  toFun := observablePush e
  invFun := observablePull e
  left_inv := by
    intro q
    apply Subtype.ext
    funext x
    simp [observablePull, observablePush, BoundaryIso.symm]
  right_inv := by
    intro q
    apply Subtype.ext
    funext x
    simp [observablePull, observablePush, BoundaryIso.symm]

/-! ## Finite release laws -/

/-- A finite probability mass and a release map on one carrier. -/
structure ReleaseData (X : Type) [Fintype X] (Ω : Type) where
  mass : X → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum_one : ∑ x, mass x = 1
  release : X → Ω

/-- The released ensemble law is the pushforward mass of each output. -/
def ensembleLaw {X : Type} [Fintype X] {Ω : Type}
    [DecidableEq Ω] (r : ReleaseData X Ω) (ω : Ω) : ℝ :=
  ∑ x, if r.release x = ω then r.mass x else 0

/-- Coupled transport uses the same boundary isomorphism for the mass and
release maps. -/
structure ReleaseIso
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
    {Ω : Type} (e : BoundaryIso A B)
    (rA : ReleaseData (BdCarrier A) Ω)
    (rB : ReleaseData (BdCarrier B) Ω) : Prop where
  mass_commutes : ∀ x, rA.mass x = rB.mass (e.toEquiv x)
  release_commutes : ∀ x, rA.release x = rB.release (e.toEquiv x)

/-- Coupled boundary, mass, and release transport determines the ensemble law. -/
theorem strong_determination_transport
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
    {Ω : Type} [DecidableEq Ω]
    (e : BoundaryIso A B)
    (rA : ReleaseData (BdCarrier A) Ω)
    (rB : ReleaseData (BdCarrier B) Ω)
    (h : ReleaseIso e rA rB) :
    ensembleLaw rA = ensembleLaw rB := by
  funext ω
  unfold ensembleLaw
  apply Fintype.sum_equiv e.toEquiv
  intro x
  rw [h.release_commutes x, h.mass_commutes x]

/-- Separate isomorphisms for the boundary, mass, and release data need not
commute with one another. -/
structure UncoupledReleaseIso
    {A : LicensingDatum.{0,v,w}} {B : LicensingDatum.{0,v',w'}}
    [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
    {Ω : Type}
    (rA : ReleaseData (BdCarrier A) Ω)
    (rB : ReleaseData (BdCarrier B) Ω) where
  boundaryIso : BoundaryIso A B
  massEquiv : BdCarrier A ≃ BdCarrier B
  releaseEquiv : BdCarrier A ≃ BdCarrier B
  mass_commutes : ∀ x, rA.mass x = rB.mass (massEquiv x)
  release_commutes : ∀ x, rA.release x = rB.release (releaseEquiv x)

/-! ## Two-state countermodel for uncoupled determination -/

/-- Empty one-step dynamics on the two-state carrier. -/
def staticBoolStep (_ _ : Bool) : Prop := False

/-- A two-state datum whose full carrier lies in the persistent boundary. -/
def staticBoolDatum : LicensingDatum where
  Carrier := Bool
  Policy := Unit
  Output := Bool
  dynamics := staticBoolStep
  license := fun _ => True
  permits := fun _ => staticBoolStep
  consume := id

/-- Every Boolean state gives a boundary point. -/
def boolBoundary (b : Bool) : BdCarrier staticBoolDatum :=
  ⟨b, ⟨trivial, by
    intro y _hy
    trivial⟩⟩

/-- The static Boolean boundary carrier is equivalent to `Bool`. -/
def boolBoundaryEquiv : BdCarrier staticBoolDatum ≃ Bool where
  toFun := fun x => x.1
  invFun := boolBoundary
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro b
    rfl

noncomputable instance staticBoolBoundaryFintype :
    Fintype (BdCarrier staticBoolDatum) :=
  Fintype.ofEquiv Bool boolBoundaryEquiv.symm

/-- Boolean negation as an equivalence. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- Swap the two points of the static boundary. -/
def boolBoundarySwap :
    BdCarrier staticBoolDatum ≃ BdCarrier staticBoolDatum :=
  (boolBoundaryEquiv.trans boolNotEquiv).trans boolBoundaryEquiv.symm

/-- Identity is an isomorphism of the static boundary dynamics. -/
def staticBoolBoundaryIso :
    BoundaryIso staticBoolDatum staticBoolDatum :=
  BoundaryIso.refl staticBoolDatum

/-- First nonuniform probability mass, with release equal to the state. -/
noncomputable def releaseDataA :
    ReleaseData (BdCarrier staticBoolDatum) Bool where
  mass := fun x => bif x.1 then (2 / 3 : ℝ) else (1 / 3 : ℝ)
  mass_nonneg := by
    intro x
    cases x.1 <;> norm_num
  mass_sum_one := by
    calc
      (∑ x : BdCarrier staticBoolDatum,
          bif x.1 then (2 / 3 : ℝ) else (1 / 3 : ℝ)) =
          ∑ b : Bool,
            bif b then (2 / 3 : ℝ) else (1 / 3 : ℝ) := by
              apply Fintype.sum_equiv boolBoundaryEquiv
              intro x
              rfl
      _ = 1 := by
        rw [Fintype.sum_bool]
        norm_num
  release := fun x => x.1

/-- Second probability mass swaps the two weights while keeping the same
release map. -/
noncomputable def releaseDataB :
    ReleaseData (BdCarrier staticBoolDatum) Bool where
  mass := fun x => bif x.1 then (1 / 3 : ℝ) else (2 / 3 : ℝ)
  mass_nonneg := by
    intro x
    cases x.1 <;> norm_num
  mass_sum_one := by
    calc
      (∑ x : BdCarrier staticBoolDatum,
          bif x.1 then (1 / 3 : ℝ) else (2 / 3 : ℝ)) =
          ∑ b : Bool,
            bif b then (1 / 3 : ℝ) else (2 / 3 : ℝ) := by
              apply Fintype.sum_equiv boolBoundaryEquiv
              intro x
              rfl
      _ = 1 := by
        rw [Fintype.sum_bool]
        norm_num
  release := fun x => x.1

/-- The two data sets are separately isomorphic: identity for the boundary and
release maps, swap for the mass map. -/
noncomputable def releaseData_uncoupledIso :
    UncoupledReleaseIso releaseDataA releaseDataB where
  boundaryIso := staticBoolBoundaryIso
  massEquiv := boolBoundarySwap
  releaseEquiv := Equiv.refl _
  mass_commutes := by
    rintro ⟨b, hb⟩
    cases b <;>
      norm_num [releaseDataA, releaseDataB, boolBoundarySwap,
        boolBoundaryEquiv, boolNotEquiv, boolBoundary]
  release_commutes := by
    intro x
    rfl

/-- The two separately isomorphic release data have different ensemble laws. -/
theorem releaseData_ensembleLaw_ne :
    ensembleLaw releaseDataA ≠ ensembleLaw releaseDataB := by
  intro h
  have hfalse := congrFun h false
  have hA : ensembleLaw releaseDataA false = (1 / 3 : ℝ) := by
    unfold ensembleLaw
    calc
      (∑ x : BdCarrier staticBoolDatum,
          if releaseDataA.release x = false then releaseDataA.mass x else 0) =
          ∑ b : Bool,
            if b = false then
              (bif b then (2 / 3 : ℝ) else (1 / 3 : ℝ)) else 0 := by
                apply Fintype.sum_equiv boolBoundaryEquiv
                intro x
                simp [releaseDataA, boolBoundaryEquiv]
      _ = (1 / 3 : ℝ) := by
        rw [Fintype.sum_bool]
        norm_num
  have hB : ensembleLaw releaseDataB false = (2 / 3 : ℝ) := by
    unfold ensembleLaw
    calc
      (∑ x : BdCarrier staticBoolDatum,
          if releaseDataB.release x = false then releaseDataB.mass x else 0) =
          ∑ b : Bool,
            if b = false then
              (bif b then (1 / 3 : ℝ) else (2 / 3 : ℝ)) else 0 := by
                apply Fintype.sum_equiv boolBoundaryEquiv
                intro x
                simp [releaseDataB, boolBoundaryEquiv]
      _ = (2 / 3 : ℝ) := by
        rw [Fintype.sum_bool]
        norm_num
  rw [hA, hB] at hfalse
  norm_num at hfalse

/-- Strong determination fails when the three isomorphisms are allowed to be
chosen independently. -/
theorem strong_determination_kill_under_uncoupled_iso :
    ∃ (A B : LicensingDatum.{0,0,0})
      (_instA : Fintype (BdCarrier A))
      (_instB : Fintype (BdCarrier B))
      (Ω : Type) (_instΩ : DecidableEq Ω)
      (rA : ReleaseData (BdCarrier A) Ω)
      (rB : ReleaseData (BdCarrier B) Ω),
      Nonempty (UncoupledReleaseIso rA rB) ∧
        ensembleLaw rA ≠ ensembleLaw rB := by
  refine ⟨staticBoolDatum, staticBoolDatum,
    staticBoolBoundaryFintype, staticBoolBoundaryFintype,
    Bool, inferInstance, releaseDataA, releaseDataB, ?_⟩
  exact ⟨⟨releaseData_uncoupledIso⟩, releaseData_ensembleLaw_ne⟩

/-- Boundary determination resolves in two parts: coupled transport determines
the law, and uncoupled transport admits a finite countermodel. -/
theorem boundary_determination_resolved :
    (∀ {A : LicensingDatum.{0,v,w}}
      {B : LicensingDatum.{0,v',w'}}
      [Fintype (BdCarrier A)] [Fintype (BdCarrier B)]
      {Ω : Type} [DecidableEq Ω]
      (e : BoundaryIso A B)
      (rA : ReleaseData (BdCarrier A) Ω)
      (rB : ReleaseData (BdCarrier B) Ω),
      ReleaseIso e rA rB → ensembleLaw rA = ensembleLaw rB) ∧
    (∃ (A B : LicensingDatum.{0,0,0})
      (_instA : Fintype (BdCarrier A))
      (_instB : Fintype (BdCarrier B))
      (Ω : Type) (_instΩ : DecidableEq Ω)
      (rA : ReleaseData (BdCarrier A) Ω)
      (rB : ReleaseData (BdCarrier B) Ω),
      Nonempty (UncoupledReleaseIso rA rB) ∧
        ensembleLaw rA ≠ ensembleLaw rB) :=
  ⟨strong_determination_transport,
    strong_determination_kill_under_uncoupled_iso⟩

/-- The four computation rules used by boundary determination are already
inhabited by the declared computation-rule package. -/
theorem computation_rules_bundle : Nonempty DeclaredComputationRules :=
  ⟨declaredComputationRules⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryDetermination
