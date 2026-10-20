import OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory
import OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy

set_option autoImplicit false

/-!
# Licensed-ascent objects

`Meta/SafeStep/AscentProfileDegeneracy.lean` shows that the six-step ascent profile carries a
family tag and six truth values, and nothing else. This module supplies the witness-carrying
refinement over the expiry category of
`Meta/LicensedBoundaryCalculus/LicenseExpiryCategory.lean`.

A licensed-ascent object is an expiry object together with a self-obstruction site that holds
no internal license, and a repaired dynamics: a sub-relation of the ambient dynamics, every
step of which is licensed at its source. The last condition is the reimport law, the point at
which an external license is admitted back into the calculus. A morphism of such objects is an
expiry morphism that maps obstruction sites to obstruction sites and preserves repaired steps.

`toAscentProfile` forgets a licensed-ascent object down to a six-step profile, and
`toAscentProfile_realizes` shows every object realizes its profile, so the classification of
`AscentProfileDegeneracy` applies to all of them. The witness-level content lives in the
morphisms, and `Meta/LicensedBoundaryCalculus/LicensedAscentTransport.lean` shows those
separate the boundaries the profile identifies.

Stage note. The self-obstruction stage reads as "the obstruction site is an unlicensed state",
not "the obstruction site has a step out of it". The distinction boundary's obstruction is the
diagonal `(void, void)`, and `no_pairStep_from_consume` proves it is a normal form for
`PairStep`, so the second reading is uninhabitable there.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscent

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory

universe u v w

/-- An expiry object refined by a self-obstruction site and a repaired dynamics whose every
step is licensed at its source. -/
structure LicensedAscentObject extends ExpiryObject.{u} where
  obstruction : Carrier
  obstruction_unlicensed : ¬ license obstruction
  repaired : Carrier → Carrier → Prop
  repaired_sub : ∀ {x y : Carrier}, repaired x y → dynamics x y
  repaired_licensed : ∀ {x y : Carrier}, repaired x y → license x
  repair_witness : ∃ x y : Carrier, repaired x y

/-- A morphism of licensed-ascent objects: an expiry morphism that also matches obstruction
sites and preserves repaired steps. -/
structure AscentHom (A : LicensedAscentObject.{u}) (B : LicensedAscentObject.{v})
    extends Hom A.toExpiryObject B.toExpiryObject where
  obstruction_map : toFun A.obstruction = B.obstruction
  repaired_preserve : ∀ {x y : A.Carrier}, A.repaired x y → B.repaired (toFun x) (toFun y)

namespace AscentHom

/-- The forgetful map to the expiry category. -/
def toExpiryHom {A : LicensedAscentObject.{u}} {B : LicensedAscentObject.{v}}
    (f : AscentHom A B) : Hom A.toExpiryObject B.toExpiryObject :=
  f.toHom

def id (A : LicensedAscentObject.{u}) : AscentHom A A where
  toHom := Hom.id A.toExpiryObject
  obstruction_map := rfl
  repaired_preserve := fun h => h

def comp {A : LicensedAscentObject.{u}} {B : LicensedAscentObject.{v}}
    {C : LicensedAscentObject.{w}} (f : AscentHom A B) (g : AscentHom B C) :
    AscentHom A C where
  toHom := Hom.comp f.toHom g.toHom
  obstruction_map := by
    show g.toHom.toFun (f.toHom.toFun A.obstruction) = C.obstruction
    rw [f.obstruction_map, g.obstruction_map]
  repaired_preserve := fun h => g.repaired_preserve (f.repaired_preserve h)

theorem id_comp {A B : LicensedAscentObject.{u}} (f : AscentHom A B) :
    comp (id A) f = f := by
  cases f with
  | mk toHom _ _ => cases toHom; rfl

theorem comp_id {A B : LicensedAscentObject.{u}} (f : AscentHom A B) :
    comp f (id B) = f := by
  cases f with
  | mk toHom _ _ => cases toHom; rfl

theorem comp_assoc {A B C D : LicensedAscentObject.{u}}
    (f : AscentHom A B) (g : AscentHom B C) (h : AscentHom C D) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | mk fh _ _ =>
    cases g with
    | mk gh _ _ =>
      cases h with
      | mk hh _ _ => cases fh; cases gh; cases hh; rfl

end AscentHom

/-- Category laws for licensed-ascent objects and their morphisms. -/
theorem licensedAscent_category_laws :
    (∀ {A B : LicensedAscentObject.{u}} (f : AscentHom A B),
        AscentHom.comp (AscentHom.id A) f = f) ∧
    (∀ {A B : LicensedAscentObject.{u}} (f : AscentHom A B),
        AscentHom.comp f (AscentHom.id B) = f) ∧
    (∀ {A B C D : LicensedAscentObject.{u}}
        (f : AscentHom A B) (g : AscentHom B C) (h : AscentHom C D),
      AscentHom.comp (AscentHom.comp f g) h = AscentHom.comp f (AscentHom.comp g h)) :=
  ⟨AscentHom.id_comp, AscentHom.comp_id, AscentHom.comp_assoc⟩

/-! ## Forgetting a licensed-ascent object to a six-step profile -/

/-- The six-step profile of a licensed-ascent object. Each stage is a proposition about the
object's own data. -/
def toAscentProfile (A : LicensedAscentObject.{u}) : AscentProfile where
  shape :=
    { hasBaseSystem := ∃ x y : A.Carrier, A.dynamics x y
      hasSelfObstruction := ∃ c : A.Carrier, ¬ A.license c
      blockedInBase := ¬ A.license A.obstruction
      hasStrongerFramework := ∃ c : A.Carrier, A.license c
      resolvedInFramework := ∃ x y : A.Carrier, A.repaired x y
      licensedReimport := ∀ x y : A.Carrier, A.repaired x y → A.license x }
  family := AscentFamily.reflection

/-- Every licensed-ascent object realizes its own six-step profile, so the classification of
`AscentProfileDegeneracy` applies to all of them. -/
theorem toAscentProfile_realizes (A : LicensedAscentObject.{u}) :
    RealizesSixStepShape (toAscentProfile A).shape := by
  refine ⟨⟨A.issue, A.consume, A.crossing⟩, ⟨A.obstruction, A.obstruction_unlicensed⟩,
    A.obstruction_unlicensed, ⟨A.issue, A.issue_licensed⟩, A.repair_witness, ?_⟩
  intro _ _ h
  exact A.repaired_licensed h

/-- Consequently every licensed-ascent object is compatible with the dependency-pair profile,
which is the classification statement, not a transport of witnesses. -/
theorem toAscentProfile_compatible (A : LicensedAscentObject.{u}) :
    CompatibleWithDp (toAscentProfile A) :=
  (OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy.compatibleWithDp_iff_realizes
    (toAscentProfile A)).2 ⟨toAscentProfile_realizes A, rfl⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicensedAscent
