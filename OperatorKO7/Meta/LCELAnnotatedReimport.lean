import OperatorKO7.Meta.LCELTypedDerivations
import OperatorKO7.Meta.LCELBoundaryReimportRepair

set_option autoImplicit false

/-!
# Proof-carrying annotated reimport

An extension proof can return to the base layer only as an annotated derivation
carrying both the license and the extension proof.  The erasure map returns a
plain base derivation only for the base constructor.  Consequently a boundary
sentence, which has no base derivation, cannot acquire one by erasing a licensed
reimport.
-/

namespace OperatorKO7.Meta.LCELAnnotatedReimport

open OperatorKO7.Meta.LCELTypedDerivations

universe u1 v1 u2 v2 uL uL2 uL3

/-- Base derivation or licensed extension derivation, with the provenance kept
in the constructor. -/
inductive AnnotatedDerivation
    (T : TypedTheory.{u1, v1})
    (U : TypedTheory.{u2, v2})
    (embed : TheoryExtension T U)
    (License : Type uL) (phi : T.Sentence) where
| base : T.Derivation phi -> AnnotatedDerivation T U embed License phi
| licensed : License -> U.Derivation (embed.onSentence phi) ->
    AnnotatedDerivation T U embed License phi

/-- Erasure is deliberately partial: a licensed extension proof does not become
a plain base derivation. -/
def eraseToBase?
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence} :
    AnnotatedDerivation T U embed License phi -> Option (T.Derivation phi)
| .base d => some d
| .licensed _ _ => none

/-- Reimport an extension proof with an explicit license annotation. -/
def reimportAnnotated
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (license : License)
    (d : U.Derivation (embed.onSentence phi)) :
    AnnotatedDerivation T U embed License phi :=
  .licensed license d

/-- Embed a genuine base derivation into the annotated layer. -/
def annotateBase
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (d : T.Derivation phi) :
    AnnotatedDerivation T U embed License phi :=
  .base d

/-- Change only the license vocabulary while retaining the derivation and its
base/licensed provenance constructor. -/
def mapLicense
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {License' : Type uL2} {phi : T.Sentence}
    (f : License -> License') :
    AnnotatedDerivation T U embed License phi ->
      AnnotatedDerivation T U embed License' phi
| .base d => .base d
| .licensed license d => .licensed (f license) d

/-- License relabeling composes extensionally on the proof-carrying
derivation, rather than through a stored proposition field. -/
theorem mapLicense_comp
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {License' : Type uL2} {License'' : Type uL3}
    {phi : T.Sentence}
    (f : License -> License') (g : License' -> License'')
    (d : AnnotatedDerivation T U embed License phi) :
    mapLicense g (mapLicense f d) =
      mapLicense (fun license => g (f license)) d := by
  cases d <;> rfl

/-- Recover the complete licensed payload when the provenance constructor is
licensed.  Base derivations deliberately have no such payload. -/
def licensedPayload?
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence} :
    AnnotatedDerivation T U embed License phi ->
      Option (License × U.Derivation (embed.onSentence phi))
| .base _ => none
| .licensed license d => some (license, d)

/-- Total payload view of an annotated derivation.  Unlike the two partial
projections, this sum remembers which provenance constructor was used. -/
abbrev AnnotatedPayload
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    (embed : TheoryExtension T U)
    (License : Type uL) (phi : T.Sentence) :=
  T.Derivation phi ⊕
    (License × U.Derivation (embed.onSentence phi))

/-- Forget only the constructor wrapper, retaining the complete payload. -/
def toPayload
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence} :
    AnnotatedDerivation T U embed License phi ->
      AnnotatedPayload embed License phi
  | .base d => .inl d
  | .licensed license d => .inr (license, d)

/-- Reconstruct the provenance constructor from its total payload view. -/
def ofPayload
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence} :
    AnnotatedPayload embed License phi ->
      AnnotatedDerivation T U embed License phi
  | .inl d => .base d
  | .inr (license, d) => .licensed license d

/-- Annotated derivations are genuinely equivalent to the disjoint sum of
plain-base payloads and license-carrying extension payloads. -/
def annotatedDerivationEquivPayload
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence} :
    AnnotatedDerivation T U embed License phi ≃
      AnnotatedPayload embed License phi where
  toFun := toPayload
  invFun := ofPayload
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro payload
    rcases payload with d | ⟨license, d⟩ <;> rfl

/-- Total payload reconstruction is a round trip for every annotated proof,
including licensed reimports. -/
theorem annotatedPayload_roundTrip
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (d : AnnotatedDerivation T U embed License phi) :
    ofPayload (toPayload d) = d := by
  cases d <;> rfl

/-- Relabeling a license commutes exactly with annotated reimport. -/
theorem mapLicense_reimportAnnotated
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {License' : Type uL2} {phi : T.Sentence}
    (f : License -> License') (license : License)
    (d : U.Derivation (embed.onSentence phi)) :
    mapLicense f (reimportAnnotated license d) =
      reimportAnnotated (f license) d :=
  rfl

/-- License relabeling leaves a base annotation in the base constructor. -/
theorem mapLicense_annotateBase
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {License' : Type uL2} {phi : T.Sentence}
    (f : License -> License') (d : T.Derivation phi) :
    mapLicense f (annotateBase (U := U) (embed := embed)
      (License := License) d) =
      annotateBase (U := U) (embed := embed) (License := License') d :=
  rfl

/-- Plain-base annotation and partial erasure form a genuine round trip on
base derivations. -/
theorem eraseToBase?_annotateBase
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (d : T.Derivation phi) :
    eraseToBase? (annotateBase (U := U) (embed := embed)
      (License := License) d) = some d :=
  rfl

/-- Licensed reimport and licensed-payload recovery form a genuine round trip
at the annotated layer.  This does not erase the result to a plain base proof. -/
theorem licensedPayload?_reimportAnnotated
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (license : License)
    (d : U.Derivation (embed.onSentence phi)) :
    licensedPayload? (reimportAnnotated license d) = some (license, d) :=
  rfl

/-- Every extension derivation reimports as an actual proof object in the
annotated layer.  This is the proof-carrying replacement for plain-base
conservativity. -/
theorem extension_derivation_reimports_annotated
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (license : License) :
    Nonempty (U.Derivation (embed.onSentence phi)) ->
      Nonempty (AnnotatedDerivation T U embed License phi) := by
  rintro ⟨d⟩
  exact ⟨reimportAnnotated license d⟩

/-- Derived annotated-reimport reversibility at the licensed branch: the
extension proof and license are recovered exactly, and the total payload
reconstructs the same annotated derivation.  No base derivation is assumed,
so this theorem applies at a boundary sentence.  It deliberately supplies no
theorem of shape `T+ proves phi -> T proves phi`. -/
theorem annotated_reimport_reversibility_derived
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (license : License)
    (extensionDerivation : U.Derivation (embed.onSentence phi)) :
    licensedPayload? (reimportAnnotated license extensionDerivation) =
        some (license, extensionDerivation) ∧
      ofPayload (toPayload (reimportAnnotated license extensionDerivation)) =
        reimportAnnotated license extensionDerivation :=
  ⟨licensedPayload?_reimportAnnotated license extensionDerivation,
    annotatedPayload_roundTrip (reimportAnnotated license extensionDerivation)⟩

/-- A boundary sentence is one with no plain base derivation. -/
def BoundarySentence (T : TypedTheory.{u1, v1}) (phi : T.Sentence) : Prop :=
  ¬ Nonempty (T.Derivation phi)

/-- No annotated derivation of a boundary sentence erases to a plain base
derivation. -/
theorem boundary_annotation_erases_to_none
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (hboundary : BoundarySentence T phi)
    (d : AnnotatedDerivation T U embed License phi) :
    eraseToBase? d = none := by
  cases d with
  | base baseDerivation =>
      exact False.elim (hboundary ⟨baseDerivation⟩)
  | licensed _ _ => rfl

/-- In particular, a licensed reimport at a boundary sentence cannot be
identified with a successful plain erasure. -/
theorem licensed_reimport_not_plain
    {T : TypedTheory.{u1, v1}}
    {U : TypedTheory.{u2, v2}}
    {embed : TheoryExtension T U}
    {License : Type uL} {phi : T.Sentence}
    (hboundary : BoundarySentence T phi)
    (license : License)
    (d : U.Derivation (embed.onSentence phi)) :
    eraseToBase? (reimportAnnotated license d) = none :=
  boundary_annotation_erases_to_none hboundary
    (reimportAnnotated license d)

section AuditChecks

#check @AnnotatedDerivation
#check @eraseToBase?
#check @reimportAnnotated
#check @annotateBase
#check @mapLicense
#check @mapLicense_comp
#check @licensedPayload?
#check @AnnotatedPayload
#check @toPayload
#check @ofPayload
#check @annotatedDerivationEquivPayload
#check @annotatedPayload_roundTrip
#check @mapLicense_reimportAnnotated
#check @mapLicense_annotateBase
#check @eraseToBase?_annotateBase
#check @licensedPayload?_reimportAnnotated
#check @extension_derivation_reimports_annotated
#check @annotated_reimport_reversibility_derived
#check @BoundarySentence
#check @boundary_annotation_erases_to_none
#check @licensed_reimport_not_plain

#print axioms boundary_annotation_erases_to_none
#print axioms licensed_reimport_not_plain
#print axioms mapLicense_comp
#print axioms eraseToBase?_annotateBase
#print axioms licensedPayload?_reimportAnnotated
#print axioms extension_derivation_reimports_annotated
#print axioms annotatedPayload_roundTrip
#print axioms mapLicense_reimportAnnotated
#print axioms mapLicense_annotateBase
#print axioms annotated_reimport_reversibility_derived

end AuditChecks

end OperatorKO7.Meta.LCELAnnotatedReimport
