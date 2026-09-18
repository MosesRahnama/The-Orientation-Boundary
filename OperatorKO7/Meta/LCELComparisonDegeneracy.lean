import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy

/-!
# What the six-slot LCEL comparison carries

`LCELQuasiFunctor` stores six `↔` fields and no carrier maps. Any two realized
slot profiles therefore compare, and the hom-sets are subsingletons. This is
the same classification as `AscentProfileDegeneracy`: six truth values, no
stage witness transported.

`LCELComparisonWitness` is also proof-irrelevant, but its inhabitation asks
stagewise equivalence of the underlying six-step comparison profiles, which
include `blockedInBase` and `resolvedInFramework` (not LCEL slots). The
published `thm:lcel-structural-identity` cites
`LCELComparisonWitness.transports_realization` and is that conditional
transport, not an identity of carriers. This module does not edit the paper.
-/

open OperatorKO7.LCELSchema
open OperatorKO7.LCELStructuralIdentity

namespace OperatorKO7.LCELComparisonDegeneracy

/-- Any two realized LCEL slot profiles are stagewise equivalent: each clause
`↔` holds between two true propositions. -/
theorem stagewiseLCEL_of_realizes {P Q : LCELSlotProfile}
    (hP : RealizesLCELSchema P) (hQ : RealizesLCELSchema Q) :
    StagewiseLCELEquivalent P Q := by
  intro c
  cases c with
  | baseSystem => exact ⟨fun _ => hQ.1, fun _ => hP.1⟩
  | boundary => exact ⟨fun _ => hQ.2.1, fun _ => hP.2.1⟩
  | externalLicense => exact ⟨fun _ => hQ.2.2.1, fun _ => hP.2.2.1⟩
  | licensedExtension => exact ⟨fun _ => hQ.2.2.2.1, fun _ => hP.2.2.2.1⟩
  | reimportClass => exact ⟨fun _ => hQ.2.2.2.2.1, fun _ => hP.2.2.2.2.1⟩
  | annotationFunctor =>
      exact ⟨fun _ => hQ.2.2.2.2.2, fun _ => hP.2.2.2.2.2⟩

/-- Six `True` clauses: a slot profile with no content. -/
def contentlessSlotProfile : LCELSlotProfile where
  hasBaseSystem := True
  hasBoundary := True
  hasExternalLicense := True
  hasLicensedExtension := True
  hasReimportClass := True
  hasAnnotationFunctor := True

theorem contentless_realizes : RealizesLCELSchema contentlessSlotProfile :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem contentless_stagewise {P : LCELSlotProfile}
    (hP : RealizesLCELSchema P) :
    StagewiseLCELEquivalent contentlessSlotProfile P :=
  stagewiseLCEL_of_realizes contentless_realizes hP

/-- Six clause `↔` between any two realized typed instances. Each direction
returns the stored inhabitant and ignores its input, matching
`LCELStructuralIdentity.iff_of_true`. -/
def quasiFunctor_of_realizes {L₁ L₂ : FormalLCELInstance}
    (h₁ : RealizesLCELSchema L₁.toSlotProfile)
    (h₂ : RealizesLCELSchema L₂.toSlotProfile) :
    LCELQuasiFunctor L₁ L₂ where
  baseSystemMap := ⟨fun _ => h₂.1, fun _ => h₁.1⟩
  boundaryMap := ⟨fun _ => h₂.2.1, fun _ => h₁.2.1⟩
  externalLicenseMap := ⟨fun _ => h₂.2.2.1, fun _ => h₁.2.2.1⟩
  licensedExtensionMap := ⟨fun _ => h₂.2.2.2.1, fun _ => h₁.2.2.2.1⟩
  reimportClassMap := ⟨fun _ => h₂.2.2.2.2.1, fun _ => h₁.2.2.2.2.1⟩
  annotationFunctorMap := ⟨fun _ => h₂.2.2.2.2.2, fun _ => h₁.2.2.2.2.2⟩

/-- Any two realized LCEL instances inhabit the six-clause comparison. -/
theorem contentless_lcel_compares {L₁ L₂ : FormalLCELInstance}
    (h₁ : RealizesLCELSchema L₁.toSlotProfile)
    (h₂ : RealizesLCELSchema L₂.toSlotProfile) :
    Nonempty (LCELQuasiFunctor L₁ L₂) :=
  ⟨quasiFunctor_of_realizes h₁ h₂⟩

/-- Hom-sets of `LCELQuasiFunctor` are subsingletons: six `↔` fields, all
proof-irrelevant. -/
theorem lcelQuasiFunctor_subsingleton (L₁ L₂ : FormalLCELInstance) :
    Subsingleton (LCELQuasiFunctor L₁ L₂) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- Hom-sets of `LCELComparisonWitness` are subsingletons when inhabited.
Inhabitation still needs stagewise equivalence of the six-step comparison
profiles, not merely LCEL realization. -/
theorem lcelComparison_subsingleton (L₁ L₂ : FormalLCELInstance) :
    Subsingleton (LCELComparisonWitness L₁ L₂) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- **The six-slot LCEL comparison is a classification, not a transport of
witnesses.** Realized instances always compare; a contentless all-`True`
profile is stagewise equivalent to every realized profile; and both
comparison structures are subsingletons. -/
theorem lcel_identity_is_classification :
    (∀ {L₁ L₂ : FormalLCELInstance},
        RealizesLCELSchema L₁.toSlotProfile →
          RealizesLCELSchema L₂.toSlotProfile →
            Nonempty (LCELQuasiFunctor L₁ L₂))
      ∧ (∀ {P : LCELSlotProfile}, RealizesLCELSchema P →
            StagewiseLCELEquivalent contentlessSlotProfile P)
      ∧ (∀ L₁ L₂ : FormalLCELInstance, Subsingleton (LCELQuasiFunctor L₁ L₂))
      ∧ (∀ L₁ L₂ : FormalLCELInstance, Subsingleton (LCELComparisonWitness L₁ L₂)) :=
  ⟨contentless_lcel_compares, contentless_stagewise,
    lcelQuasiFunctor_subsingleton, lcelComparison_subsingleton⟩

end OperatorKO7.LCELComparisonDegeneracy
