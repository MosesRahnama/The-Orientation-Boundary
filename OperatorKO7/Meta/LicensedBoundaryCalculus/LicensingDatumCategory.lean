set_option autoImplicit false

/-!
# Category of licensing data

A licensing datum carries exactly the five objects used by the Licensing
Boundary: carrier, dynamics, license, policy language, and consume operation.
Morphisms carry state, policy, and output maps, preserve permitted licensed
steps, and carry an explicit capability tag recording license preservation and
reflection.  Composition keeps only capabilities proved at both stages, so the
class is closed under composition without inventing a transport law.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory

universe u v w u' v' w' u'' v'' w''

structure LicensingDatum where
  Carrier : Type u
  Policy : Type v
  Output : Type w
  dynamics : Carrier → Carrier → Prop
  license : Carrier → Prop
  permits : Policy → Carrier → Carrier → Prop
  consume : Carrier → Output

/-- Two independent transport capabilities. `true` is proof-carrying: a hom
with that bit set must provide the corresponding implication. -/
structure LicenseTransportTag where
  preserves : Bool
  reflects : Bool
  deriving DecidableEq, Repr

/-- Capability intersection used by composition. -/
def LicenseTransportTag.comp (a b : LicenseTransportTag) : LicenseTransportTag :=
  ⟨a.preserves && b.preserves, a.reflects && b.reflects⟩

/-- Identity transports both directions. -/
def LicenseTransportTag.identity : LicenseTransportTag := ⟨true, true⟩

structure Hom (A : LicensingDatum.{u,v,w}) (B : LicensingDatum.{u',v',w'}) where
  stateMap : A.Carrier → B.Carrier
  policyMap : A.Policy → B.Policy
  outputMap : A.Output → B.Output
  tag : LicenseTransportTag
  dynamics_preserve : ∀ {x y}, A.dynamics x y → B.dynamics (stateMap x) (stateMap y)
  policy_preserve : ∀ {p x y}, A.permits p x y →
    B.permits (policyMap p) (stateMap x) (stateMap y)
  consume_preserve : ∀ x, outputMap (A.consume x) = B.consume (stateMap x)
  license_preserve : tag.preserves = true → ∀ {x}, A.license x → B.license (stateMap x)
  license_reflect : tag.reflects = true → ∀ {x}, B.license (stateMap x) → A.license x

namespace Hom

/-- Identity morphism. -/
def id (A : LicensingDatum) : Hom A A where
  stateMap := _root_.id
  policyMap := _root_.id
  outputMap := _root_.id
  tag := LicenseTransportTag.identity
  dynamics_preserve := fun h => h
  policy_preserve := fun h => h
  consume_preserve := fun _ => rfl
  license_preserve := fun _ _ h => h
  license_reflect := fun _ _ h => h

/-- Composition. Mixed preserve/reflect capabilities are not guessed: the
composite advertises a capability only when both factors carry it. -/
def comp {A : LicensingDatum.{u,v,w}} {B : LicensingDatum.{u',v',w'}}
    {C : LicensingDatum.{u'',v'',w''}} (f : Hom A B) (g : Hom B C) : Hom A C where
  stateMap := g.stateMap ∘ f.stateMap
  policyMap := g.policyMap ∘ f.policyMap
  outputMap := g.outputMap ∘ f.outputMap
  tag := LicenseTransportTag.comp f.tag g.tag
  dynamics_preserve := fun h => g.dynamics_preserve (f.dynamics_preserve h)
  policy_preserve := fun h => g.policy_preserve (f.policy_preserve h)
  consume_preserve := fun x => by
    change g.outputMap (f.outputMap (A.consume x)) = C.consume (g.stateMap (f.stateMap x))
    calc
      g.outputMap (f.outputMap (A.consume x)) = g.outputMap (B.consume (f.stateMap x)) :=
        congrArg g.outputMap (f.consume_preserve x)
      _ = C.consume (g.stateMap (f.stateMap x)) := g.consume_preserve (f.stateMap x)
  license_preserve := by
    intro hcap x hx
    simp [LicenseTransportTag.comp] at hcap
    exact g.license_preserve hcap.2 (f.license_preserve hcap.1 hx)
  license_reflect := by
    intro hcap x hx
    simp [LicenseTransportTag.comp] at hcap
    exact f.license_reflect hcap.1 (g.license_reflect hcap.2 hx)

/-- Left identity. -/
theorem id_comp {A : LicensingDatum} {B : LicensingDatum} (f : Hom A B) :
    comp (id A) f = f := by
  cases f with
  | mk stateMap policyMap outputMap tag dyn pol cons lp lr =>
      cases tag with
      | mk preserves reflects =>
          cases preserves <;> cases reflects <;>
            simp [comp, id, LicenseTransportTag.comp,
              LicenseTransportTag.identity, Function.comp_def]

/-- Right identity. -/
theorem comp_id {A : LicensingDatum} {B : LicensingDatum} (f : Hom A B) :
    comp f (id B) = f := by
  cases f with
  | mk stateMap policyMap outputMap tag dyn pol cons lp lr =>
      cases tag with
      | mk preserves reflects =>
          cases preserves <;> cases reflects <;>
            simp [comp, id, LicenseTransportTag.comp,
              LicenseTransportTag.identity, Function.comp_def]

/-- Associativity of licensing morphisms. -/
theorem comp_assoc {A B C D : LicensingDatum}
    (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | mk sf pf of tf df ppf cf lpf lrf =>
    cases g with
    | mk sg pg og tg dg ppg cg lpg lrg =>
      cases h with
      | mk sh ph oh th dh pph ch lph lrh =>
        cases tf <;> cases tg <;> cases th <;>
          simp [comp, LicenseTransportTag.comp, Function.comp_def, Bool.and_assoc]

end Hom

/-- The generic object/morphism/identity/composition package satisfies the
category laws needed by the paper: identity on identities, left identity, right
identity, and associativity.

STATEMENT CHANGE (2026-08-20): the associativity conjunct was added.  The former
statement carried the identity laws alone while the file already proved
`Hom.comp_assoc`, so the name claimed more than the type.  The change
strengthens the theorem and leaves every earlier use valid. -/
theorem licensingDatum_category_laws :
    (∀ (A : LicensingDatum), Hom.comp (Hom.id A) (Hom.id A) = Hom.id A) ∧
    (∀ {A B : LicensingDatum} (f : Hom A B), Hom.comp (Hom.id A) f = f) ∧
    (∀ {A B : LicensingDatum} (f : Hom A B), Hom.comp f (Hom.id B) = f) ∧
    (∀ {A B C D : LicensingDatum} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) :=
  ⟨fun A => Hom.id_comp (Hom.id A), Hom.id_comp, Hom.comp_id, Hom.comp_assoc⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingDatumCategory

