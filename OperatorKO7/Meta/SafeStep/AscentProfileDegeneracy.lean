import OperatorKO7.Meta.SafeStep.DistinctionAscentProfile

/-!
# What the six-step ascent-profile identity carries

`Meta/SafeStep/DistinctionAscentProfile.lean` places the distinction boundary and the
dependency-pair boundary in the same six-step licensed-ascent profile and produces a
comparison witness in both directions. This module measures how much that carries.

The six-step profile stores six `Prop` fields and a family tag, and a `ComparisonWitness`
stores an equality of family tags together with a stagewise `↔`. Two realized profiles of the
same family are therefore always comparison-equivalent, whatever their stages say, because
each stage `↔` holds between two true propositions. `compatibleWithDp_iff_realizes` states
this as a biconditional, `contentlessToDistinction` and `distinctionToContentless` exhibit a
profile whose six stages are `True` as isomorphic to the distinction boundary in both
directions, and `comparisonWitness_subsingleton` shows the hom-sets carry no further data.

The identity at this layer is therefore a classification by family tag and six truth values,
with no stage witness transported. `ascent_profile_identity_is_classification` bundles the
three facts. Witness-level structure is a separate question, answered by the licensed-ascent
objects of `Meta/LicensedBoundaryCalculus/LicensedAscentObject.lean` and their transport
table, where the two boundaries are provably distinct.
-/

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.StructuralIdentityComparison
open OperatorKO7.Meta.SafeStep.DistinctionAscentProfile

namespace OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy

/-- Any two realized six-step profiles are stagewise equivalent: every stage `↔` holds
between two true propositions. -/
theorem stagewiseEquivalent_of_realizes {P Q : SixStepStructuralProfile}
    (hP : RealizesSixStepShape P) (hQ : RealizesSixStepShape Q) :
    StagewiseEquivalent P Q := by
  rcases (realizesSixStepShape_iff_stagewise P).1 hP with ⟨rP⟩
  rcases (realizesSixStepShape_iff_stagewise Q).1 hQ with ⟨rQ⟩
  intro s
  exact ⟨fun _ => rQ.realizes s, fun _ => rP.realizes s⟩

/-- Compatibility with the dependency-pair profile is exactly six true stages plus the
reflection tag. Nothing about the stages' content enters. -/
theorem compatibleWithDp_iff_realizes (C : AscentProfile) :
    CompatibleWithDp C ↔
      (RealizesSixStepShape C.shape ∧ C.family = AscentFamily.reflection) := by
  constructor
  · intro h
    exact ⟨compatibleWithDp_realizesSixStep C h, h.2⟩
  · rintro ⟨hR, hF⟩
    exact ⟨stagewiseEquivalent_of_realizes hR structural_identity, hF⟩

/-- A comparison witness between any two realized profiles of the same family. -/
def comparisonOfRealized {P Q : AscentProfile}
    (hP : RealizesSixStepShape P.shape) (hQ : RealizesSixStepShape Q.shape)
    (hF : P.family = Q.family) : ComparisonWitness P Q where
  sameFamily := hF
  sameShape := stagewiseEquivalent_of_realizes hP hQ

/-- Six `True` stages and the reflection tag: a profile with no content at all. -/
def contentlessProfile : AscentProfile where
  shape :=
    { hasBaseSystem := True
      hasSelfObstruction := True
      blockedInBase := True
      hasStrongerFramework := True
      resolvedInFramework := True
      licensedReimport := True }
  family := AscentFamily.reflection

/-- The contentless profile maps to the distinction boundary. -/
def contentlessToDistinction :
    ComparisonWitness contentlessProfile distinctionBoundaryAscentProfile :=
  comparisonOfRealized ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    distinctionBoundary_has_dp_structural_identity.1 rfl

/-- And back, so the two are isomorphic in the comparison category. -/
def distinctionToContentless :
    ComparisonWitness distinctionBoundaryAscentProfile contentlessProfile :=
  comparisonOfRealized distinctionBoundary_has_dp_structural_identity.1
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl

/-- The synthetic Gödel-labelled profile, whose six stages are also `True`, is isomorphic to
the distinction boundary by the same argument. -/
def syntheticToDistinction :
    ComparisonWitness godel1931PaperAscentProfile distinctionBoundaryAscentProfile :=
  comparisonOfRealized godel1931PaperAscentProfile_realizesSixStep
    distinctionBoundary_has_dp_structural_identity.1 rfl

/-- Hom-sets in the comparison category are subsingletons: a morphism carries an equality of
family tags and a stagewise `↔`, and both are proof-irrelevant. -/
theorem comparisonWitness_subsingleton (P Q : AscentProfile) :
    Subsingleton (ComparisonWitness P Q) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- Comparability with the dependency-pair profile is the same classification, read through
the comparison category. -/
theorem nonempty_comparison_dp_iff (C : AscentProfile) :
    Nonempty (ComparisonWitness C dpAsClassicalAscentProfile) ↔
      (RealizesSixStepShape C.shape ∧ C.family = AscentFamily.reflection) := by
  constructor
  · rintro ⟨W⟩
    have hcompat : CompatibleWithDp C :=
      ⟨by simpa [dpAsClassicalAscentProfile] using W.sameShape,
       by simpa [dpAsClassicalAscentProfile] using W.sameFamily⟩
    exact (compatibleWithDp_iff_realizes C).1 hcompat
  · rintro ⟨hR, hF⟩
    exact ⟨comparisonOfRealized hR
      (by simpa [dpAsClassicalAscentProfile] using structural_identity)
      (by simpa [dpAsClassicalAscentProfile] using hF)⟩

/-- **The six-step identity is a classification, not a transport of witnesses.** Membership
is six true stages and the reflection tag; a profile whose six stages are `True` is isomorphic
to the distinction boundary in both directions; and the hom-sets are subsingletons, so a
morphism carries no data beyond the classification. -/
theorem ascent_profile_identity_is_classification :
    (∀ C : AscentProfile,
        CompatibleWithDp C ↔
          (RealizesSixStepShape C.shape ∧ C.family = AscentFamily.reflection))
      ∧ Nonempty (ComparisonWitness contentlessProfile distinctionBoundaryAscentProfile)
      ∧ Nonempty (ComparisonWitness distinctionBoundaryAscentProfile contentlessProfile)
      ∧ (∀ P Q : AscentProfile, Subsingleton (ComparisonWitness P Q)) :=
  ⟨compatibleWithDp_iff_realizes, ⟨contentlessToDistinction⟩, ⟨distinctionToContentless⟩,
    comparisonWitness_subsingleton⟩

end OperatorKO7.Meta.SafeStep.AscentProfileDegeneracy
