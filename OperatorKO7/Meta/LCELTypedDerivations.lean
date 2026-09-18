import Mathlib

set_option autoImplicit false

/-!
# Typed theories, derivations, and layer-crossing maps

LCEL's layers are represented here by sentence carriers and proof-object
families.  A layer-crossing map acts on both sentences and derivations.  The
identity and composite maps are defined on those objects, and their action laws
are pointwise theorems rather than proposition-level equivalence fields.
-/

namespace OperatorKO7.Meta.LCELTypedDerivations

universe u1 v1 u2 v2 u3 v3

/-- A theory with a sentence type and a type of derivation objects for each
sentence. -/
structure TypedTheory where
  Sentence : Type u1
  Derivation : Sentence -> Type v1

/-- An actual morphism of proof systems: sentences and their derivations are
both mapped. -/
structure DerivationMorphism
    (T : TypedTheory.{u1, v1}) (U : TypedTheory.{u2, v2}) where
  onSentence : T.Sentence -> U.Sentence
  onDerivation : ∀ {phi : T.Sentence},
    T.Derivation phi -> U.Derivation (onSentence phi)

namespace DerivationMorphism

/-- Identity morphism on a typed theory. -/
def id (T : TypedTheory.{u1, v1}) : DerivationMorphism T T where
  onSentence := fun phi => phi
  onDerivation := fun d => d

/-- Composition of layer-crossing maps. -/
def comp
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : DerivationMorphism U V) (f : DerivationMorphism T U) :
    DerivationMorphism T V where
  onSentence := fun phi => g.onSentence (f.onSentence phi)
  onDerivation := fun d => g.onDerivation (f.onDerivation d)

@[simp] theorem id_onSentence
    (T : TypedTheory.{u1, v1}) (phi : T.Sentence) :
    (id T).onSentence phi = phi := rfl

@[simp] theorem id_onDerivation
    (T : TypedTheory.{u1, v1}) {phi : T.Sentence}
    (d : T.Derivation phi) :
    (id T).onDerivation d = d := rfl

@[simp] theorem comp_onSentence
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : DerivationMorphism U V) (f : DerivationMorphism T U)
    (phi : T.Sentence) :
    (comp g f).onSentence phi = g.onSentence (f.onSentence phi) := rfl

@[simp] theorem comp_onDerivation
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : DerivationMorphism U V) (f : DerivationMorphism T U)
    {phi : T.Sentence} (d : T.Derivation phi) :
    (comp g f).onDerivation d = g.onDerivation (f.onDerivation d) := rfl

/-- Sentence action is associative under composition. -/
theorem comp_assoc_onSentence
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    {W : TypedTheory}
    (h : DerivationMorphism V W)
    (g : DerivationMorphism U V)
    (f : DerivationMorphism T U)
    (phi : T.Sentence) :
    (comp h (comp g f)).onSentence phi =
      (comp (comp h g) f).onSentence phi := rfl

/-- Derivation action is associative under composition. -/
theorem comp_assoc_onDerivation
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    {W : TypedTheory}
    (h : DerivationMorphism V W)
    (g : DerivationMorphism U V)
    (f : DerivationMorphism T U)
    {phi : T.Sentence} (d : T.Derivation phi) :
    (comp h (comp g f)).onDerivation d =
      (comp (comp h g) f).onDerivation d := rfl

end DerivationMorphism

/-- A theory extension is a genuine embedding on both sentences and
derivation objects.  A plain layer-crossing map remains a
`DerivationMorphism`; the word "extension" additionally requires the two
injectivity laws below. -/
structure TheoryExtension
    (T : TypedTheory.{u1, v1}) (U : TypedTheory.{u2, v2}) where
  onSentence : T.Sentence -> U.Sentence
  sentence_injective : Function.Injective onSentence
  onDerivation : ∀ {phi : T.Sentence},
    T.Derivation phi -> U.Derivation (onSentence phi)
  derivation_injective :
    ∀ {phi : T.Sentence} {left right : T.Derivation phi},
      onDerivation left = onDerivation right -> left = right

namespace TheoryExtension

/-- Forget only the injectivity witnesses, retaining the actual sentence and
derivation maps. -/
def toMorphism
    {T : TypedTheory.{u1, v1}} {U : TypedTheory.{u2, v2}}
    (extension : TheoryExtension T U) : DerivationMorphism T U where
  onSentence := extension.onSentence
  onDerivation := extension.onDerivation

/-- Identity is a genuine theory extension. -/
def id (T : TypedTheory.{u1, v1}) : TheoryExtension T T where
  onSentence := fun phi => phi
  sentence_injective := by
    intro left right h
    exact h
  onDerivation := fun d => d
  derivation_injective := by
    intro phi left right h
    exact h

/-- Genuine extensions compose, with both injectivity laws inherited from
the component extensions. -/
def comp
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : TheoryExtension U V) (f : TheoryExtension T U) :
    TheoryExtension T V where
  onSentence := fun phi => g.onSentence (f.onSentence phi)
  sentence_injective := by
    intro left right h
    exact f.sentence_injective (g.sentence_injective h)
  onDerivation := fun d => g.onDerivation (f.onDerivation d)
  derivation_injective := by
    intro phi left right h
    exact f.derivation_injective (g.derivation_injective h)

@[simp] theorem id_onSentence
    (T : TypedTheory.{u1, v1}) (phi : T.Sentence) :
    (id T).onSentence phi = phi :=
  rfl

@[simp] theorem id_onDerivation
    (T : TypedTheory.{u1, v1}) {phi : T.Sentence}
    (d : T.Derivation phi) :
    (id T).onDerivation d = d :=
  rfl

@[simp] theorem comp_onSentence
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : TheoryExtension U V) (f : TheoryExtension T U)
    (phi : T.Sentence) :
    (comp g f).onSentence phi = g.onSentence (f.onSentence phi) :=
  rfl

@[simp] theorem comp_onDerivation
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {V : TypedTheory.{u3, v3}}
    (g : TheoryExtension U V) (f : TheoryExtension T U)
    {phi : T.Sentence} (d : T.Derivation phi) :
    (comp g f).onDerivation d = g.onDerivation (f.onDerivation d) :=
  rfl

end TheoryExtension

section AuditChecks

#check @TypedTheory
#check @DerivationMorphism
#check @DerivationMorphism.id
#check @DerivationMorphism.comp
#check @DerivationMorphism.comp_assoc_onSentence
#check @DerivationMorphism.comp_assoc_onDerivation
#check @TheoryExtension
#check @TheoryExtension.toMorphism
#check @TheoryExtension.id
#check @TheoryExtension.comp

#print axioms DerivationMorphism.comp_assoc_onSentence
#print axioms DerivationMorphism.comp_assoc_onDerivation

end AuditChecks

end OperatorKO7.Meta.LCELTypedDerivations
