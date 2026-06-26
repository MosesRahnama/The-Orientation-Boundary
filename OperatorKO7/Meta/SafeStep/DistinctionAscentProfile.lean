import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.StructuralIdentityComparison
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.SafeStep.SmugglingUndecidability

/-!
# The Distinction boundary as a six-step licensed-ascent profile

This module upgrades the orientation/distinction duality from a stated analogy to
a structural-identity theorem, by exhibiting the confluence-side (Distinction)
boundary as a `ClassicalAscentProfile.AscentProfile` and invoking the
already-mechanized comparison theorem
`ClassicalAscentProfile.compatible_profile_has_dp_structural_identity`. It mirrors,
stage for stage, the proven `godel1931PaperAscentProfile_compatible` and the
benchmark-transport profile, except that every one of the six stages is discharged
by a real, already-mechanized eqW-boundary theorem rather than a placeholder.

It contains no `sorry`, no `admit`, no new `axiom`, no `native_decide`, and no
`@[csimp]`. The public theorem has been spot-checked with `#print axioms`
(baseline whitelist `{propext, Classical.choice, Quot.sound}`; `Classical.em` is
used in the stronger-framework stage and reduces to `Classical.choice`).

## Honest scope

The structural identity is asserted at the **licensed-ascent (repair) level**: the
six-step shape base / self-obstruction / blocked-in-base / stronger-framework /
resolved / licensed-reimport, which is exactly the level at which
`GaugeFixingGuard.safestep_is_meta_halt` already places SafeStep. The family is
classified as `reflection` because the repair imports an external soundness/observer
license; this classifies the licensed ascent, not the fracture's self-reference,
exactly as the Gödel-side profile classifies the reflective ascent rather than the
diagonal construction. At the raw-rewrite level the two boundaries' mechanisms still
differ (non-left-linear diagonal vs right-hand duplication); that remains a shared
syntactic principle, not a single theorem, per the operational-inexpressibility
development. The theorem here is the licensed-ascent structural identity, not a claim
that the raw fracture and the raw duplication are one object.

## Stage-to-witness map

* base system          : the eqW kernel has reductions (`Step.R_eq_refl`)
* self-obstruction     : the diagonal critical pair (`local_confluence_fails_at_eqW_void_void`)
* blocked in base      : the two verdicts are unjoinable (`eqW_void_void_normal_forms_are_unjoinable`)
* stronger framework   : an external gauge choice exists (`ExternalGaugeChoice`, via `Classical.em`)
* resolved in framework: SafeStep restores confluence (`safestep_guard_restores_local_confluence`)
* licensed reimport    : the guard yields the verdict (`safestep_guard_smuggles_external_observer`)
-/

open OperatorKO7 Trace
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
open OperatorKO7.Meta.SafeStep.GaugeFixingGuard
open OperatorKO7.Meta.SafeStep.SmugglingUndecidability
open MetaSN_KO7

namespace OperatorKO7.Meta.SafeStep.DistinctionAscentProfile

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q :=
  ⟨fun _ => hQ, fun _ => hP⟩

/-- The external gauge choice is available at every pair: the supervisor can always
commit to one arm of the disequality, classically. -/
theorem distinction_stronger_framework :
    ∀ a b : Trace, Nonempty (ExternalGaugeChoice a b) :=
  fun a b => ⟨⟨(Classical.em (a = b)).elim Or.inr Or.inl⟩⟩

/-- Off the diagonal, the imported disequality guard restores local confluence. -/
theorem distinction_resolved :
    ∀ a b : Trace, a ≠ b → LocalJoinSafe (eqW a b) :=
  fun _ _ h => safestep_guard_restores_local_confluence ⟨h⟩

/-- The guard licenses the verdict it imports: a SafeStep guard yields the
disequality the signature could not derive. -/
theorem distinction_licensed_reimport :
    ∀ a b : Trace, SafeStepGuard a b → a ≠ b :=
  fun _ _ g => safestep_guard_smuggles_external_observer g

/-- The confluence-side (Distinction) boundary cast as a comparison-ready six-step
licensed-ascent profile. Every stage field is a real eqW-boundary proposition. -/
def distinctionBoundaryAscentProfile : AscentProfile where
  shape :=
    { hasBaseSystem := ∃ a, Step (eqW a a) void
      hasSelfObstruction :=
        Nonempty (CriticalPairAt (eqW void void) void (integrate (merge void void)))
      blockedInBase :=
        ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge void void)) d
      hasStrongerFramework := ∀ a b : Trace, Nonempty (ExternalGaugeChoice a b)
      resolvedInFramework := ∀ a b : Trace, a ≠ b → LocalJoinSafe (eqW a b)
      licensedReimport := ∀ a b : Trace, SafeStepGuard a b → a ≠ b }
  family := AscentFamily.reflection

/-- The Distinction-boundary ascent profile is compatible with the mechanized
dependency-pair ascent profile: stagewise-equivalent and in the reflection family.
Each stage iff holds because both sides are inhabited, the DP side by
`structural_identity` and the eqW side by its named witness. -/
theorem distinctionBoundaryAscentProfile_compatible :
    CompatibleWithDp distinctionBoundaryAscentProfile := by
  rcases structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  refine ⟨?_, rfl⟩
  intro s
  cases s with
  | baseSystem =>
      exact iff_of_true ⟨void, Step.R_eq_refl void⟩ hBase
  | selfObstruction =>
      exact iff_of_true ⟨local_confluence_fails_at_eqW_void_void⟩ hSelf
  | blockedInBase =>
      exact iff_of_true eqW_void_void_normal_forms_are_unjoinable hBlocked
  | strongerFramework =>
      exact iff_of_true distinction_stronger_framework hStronger
  | resolvedInFramework =>
      exact iff_of_true distinction_resolved hResolved
  | licensedReimport =>
      exact iff_of_true distinction_licensed_reimport hLicensed

/-- THE DUALITY, AS A THEOREM (at the licensed-ascent level). The Distinction
(confluence) boundary is structurally identical to the orientation (termination)
boundary: it realizes the six-step shape, sits in the reflection family, and is
stagewise-equivalent to the mechanized dependency-pair ascent profile. Obtained by
the existing comparison theorem, with no new axiom. -/
theorem distinctionBoundary_has_dp_structural_identity :
    RealizesSixStepShape distinctionBoundaryAscentProfile.shape
      ∧ distinctionBoundaryAscentProfile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent distinctionBoundaryAscentProfile.shape
          dpAsClassicalAscentProfile.shape :=
  OperatorKO7.StructuralIdentityComparison.compatible_profile_has_dp_structural_identity
    distinctionBoundaryAscentProfile distinctionBoundaryAscentProfile_compatible

/-- THE DUALITY AS A MORPHISM. The comparison witness from the Distinction boundary
to the orientation/dependency-pair boundary, in the six-step ascent-profile
comparison category. This is a witnessed morphism of objects, not a bare
stagewise-equivalence proposition. -/
def distinctionToOrientationMorphism :
    OperatorKO7.StructuralIdentityComparison.ComparisonWitness
      distinctionBoundaryAscentProfile dpAsClassicalAscentProfile :=
  OperatorKO7.StructuralIdentityComparison.comparisonAgainstDp
    distinctionBoundaryAscentProfile distinctionBoundaryAscentProfile_compatible

/-- The inverse morphism. With both directions, the orientation and distinction
boundaries are isomorphic objects in the comparison category, not merely
stagewise-equivalent profiles. -/
def orientationToDistinctionMorphism :
    OperatorKO7.StructuralIdentityComparison.ComparisonWitness
      dpAsClassicalAscentProfile distinctionBoundaryAscentProfile where
  sameFamily := distinctionToOrientationMorphism.sameFamily.symm
  sameShape := distinctionToOrientationMorphism.sameShape.symm

/-- Structure preservation: the morphism transports six-step realization in both
directions, so the orientation and distinction boundaries stand or fall together
as licensed ascents. -/
theorem distinction_iso_orientation_realization :
    RealizesSixStepShape distinctionBoundaryAscentProfile.shape
      ↔ RealizesSixStepShape dpAsClassicalAscentProfile.shape :=
  ⟨distinctionToOrientationMorphism.right_realizes,
   distinctionToOrientationMorphism.left_realizes⟩

end OperatorKO7.Meta.SafeStep.DistinctionAscentProfile
