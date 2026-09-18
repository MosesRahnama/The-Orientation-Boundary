import OperatorKO7.Meta.ConfessionMethod_UniversalInstances
import OperatorKO7.Meta.ConfessionMethod_UsableRulesConcrete

/-!
# Confession Method Universal Usable Rules

This module does not invent a new usable-rules confession method. Instead it
packages the existing usable-rules residual and concrete-candidate boundaries
into the universal confession surface introduced for WS-A'.

The route evidence agrees with the common KO7 confession core.  The canonical
source-soundness bridge is inhabited in `ConfessionMethod_UsableRulesConcrete`,
so this module exports both the generic bridge-parameterized construction and a
fully closed canonical universal instance.
-/

namespace OperatorKO7.Meta.ConfessionMethodUniversalUsableRules

open OperatorKO7
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.InformationTheoreticConfession
open OperatorKO7.Meta.ConfessionMethodUniversalInstances

private abbrev UniversalUsableRulesKO7Carrier : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalInstances.KO7Carrier

private abbrev UniversalUsableRulesKO7Verdict : UniversalUsableRulesKO7Carrier → Prop :=
  OperatorKO7.Meta.InformationTheoreticConfession.ko7ConfessionVerdict

private abbrev UniversalUsableRulesRouteLicense : Type :=
  SoundnessLicense

private def usableRulesRouteLicenseWitness : UniversalUsableRulesRouteLicense :=
  SoundnessLicense.artsGiesl2000

/-- Any admitted usable-rules residual package recovers the canonical DP confession rank at the
route-evidence layer. -/
theorem usableRulesResidual_routeEvidence_rank_eq_dpConfession
    (R : UsableRulesConfessionRouteResidualObligation) :
    (R.toRouteEvidence R.witness).rank = dpConfession.rank := by
  simpa using usableRulesResidual_projects_forgetting_rank R

/-- Route-evidence canonical move for the universal usable-rules theorem data.
This keeps the usable-rules wrapper on the same Arts-Giesl license type
used by the four theorem-backed confession routes. -/
def canonicalRouteEvidenceConfessionMove :
    UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
      UniversalUsableRulesRouteLicense :=
  rankToGenericConfessionMove
    usableRulesRouteLicenseWitness
    schemaDPGenericRouteEvidence.rank
    dpRouteEvidence_rank_eq_dpConfession

/-- Route-evidence information profile on the usable-rules license surface. -/
def canonicalRouteEvidenceInformationTheoreticConfession :
    UniversalInfo canonicalRouteEvidenceConfessionMove where
  PreConfessionInformation := UniversalUsableRulesKO7Carrier
  PostVerdictInformation := Nat
  DiscardedInformation := Nat
  preEncode := id
  postEncode := id
  discardEncode := schemaDPGenericRouteEvidence.rank
  discardedBits := id
  canonicalDiscardedBits := 0

/-- Universal wrapper constructed from any proof-bearing usable-rules residual package. -/
def usableRulesResidualToGenericConfessionMove
    (R : UsableRulesConfessionRouteResidualObligation) :
    UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
      UniversalUsableRulesRouteLicense :=
  rankToGenericConfessionMove
    usableRulesRouteLicenseWitness
    (R.toRouteEvidence R.witness).rank
    (usableRulesResidual_routeEvidence_rank_eq_dpConfession R)

/-- Information profile attached to a proof-bearing usable-rules wrapper. -/
def usableRulesResidualToInformationTheoreticConfession
    (R : UsableRulesConfessionRouteResidualObligation) :
    UniversalInfo (usableRulesResidualToGenericConfessionMove R) where
  PreConfessionInformation := UniversalUsableRulesKO7Carrier
  PostVerdictInformation := Nat
  DiscardedInformation := Nat
  preEncode := id
  postEncode := id
  discardEncode := (R.toRouteEvidence R.witness).rank
  discardedBits := id
  canonicalDiscardedBits := 0

/-- Any admitted usable-rules residual package projects to the canonical
confession move. -/
theorem usableRulesResidualToGenericConfessionMove_refines_canonical
    (R : UsableRulesConfessionRouteResidualObligation) :
    GenericConfessionMove.Refines
      (usableRulesResidualToGenericConfessionMove R)
      canonicalConfessionMove := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x
  }⟩

theorem canonical_refines_usableRulesResidualToGenericConfessionMove
    (R : UsableRulesConfessionRouteResidualObligation) :
    GenericConfessionMove.Refines
      canonicalConfessionMove
      (usableRulesResidualToGenericConfessionMove R) := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact (congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x).symm
  }⟩

/-- Any admitted usable-rules residual package is H-equivalent to the canonical
confession move. -/
theorem usableRulesResidualToGenericConfessionMove_HEquivalent_canonical
    (R : UsableRulesConfessionRouteResidualObligation) :
    GenericConfessionMove.HEquivalent
      (usableRulesResidualToGenericConfessionMove R)
      canonicalConfessionMove := by
  exact ⟨{
    forward := Classical.choice (usableRulesResidualToGenericConfessionMove_refines_canonical R)
    backward := Classical.choice (canonical_refines_usableRulesResidualToGenericConfessionMove R)
  }⟩

/-- Universal-characterization data for an admitted usable-rules residual package. -/
def usableRulesResidualUniversalCharacterizationData
    (R : UsableRulesConfessionRouteResidualObligation) :
    UniversalConfessionCharacterizationData
      canonicalRouteEvidenceConfessionMove
      (usableRulesResidualToGenericConfessionMove R) where
  factorization := by
    exact ⟨{
      factor := id
      commutes := by
        intro x
        simpa [canonicalRouteEvidenceConfessionMove,
          usableRulesResidualToGenericConfessionMove,
          usableRulesRouteLicenseWitness,
          rankToGenericConfessionMove] using
          congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x
    }⟩

/-- `OptimalityData` for an admitted residual package; uniqueness uses the identity factor and stored rank equality. -/
def usableRulesResidualOptimalityData
    (R : UsableRulesConfessionRouteResidualObligation) :
    OptimalityData
      canonicalRouteEvidenceConfessionMove
      (usableRulesResidualToGenericConfessionMove R) where
  factorization := usableRulesResidualUniversalCharacterizationData R
  uniqueness := by
    intro _
    refine ⟨id, ?_⟩
    intro x
    simpa [canonicalRouteEvidenceConfessionMove,
      usableRulesResidualToGenericConfessionMove,
      usableRulesRouteLicenseWitness,
      rankToGenericConfessionMove] using
      (congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x).symm

/-- Discarded-information minimality package for an admitted usable-rules residual package. -/
def usableRulesResidualDiscardedInformationMinimalityData
    (R : UsableRulesConfessionRouteResidualObligation) :
    DiscardedInformationMinimalityData
      canonicalRouteEvidenceInformationTheoreticConfession
      (usableRulesResidualToInformationTheoreticConfession R) where
  canonical_le_candidate := by
    simp [canonicalRouteEvidenceInformationTheoreticConfession,
      usableRulesResidualToInformationTheoreticConfession]

/-- Package a proof-bearing usable-rules residual value with its move and information profile. -/
structure UsableRulesUniversalInstance where
  residual : UsableRulesConfessionRouteResidualObligation
  move : UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
    UniversalUsableRulesRouteLicense
  informationProfile : UniversalInfo move

/-- Package an admitted usable-rules residual route as a universal instance. -/
def usableRulesResidualUniversalInstance
    (R : UsableRulesConfessionRouteResidualObligation) :
    UsableRulesUniversalInstance where
  residual := R
  move := usableRulesResidualToGenericConfessionMove R
  informationProfile := usableRulesResidualToInformationTheoreticConfession R

/-- Construct a residual package for the concrete candidate from an explicit soundness bridge. -/
def usableRulesConcreteCandidateResidual
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteRouteCandidate_to_residual usableRulesConcreteRouteCandidate B

/-- Generic bridge-parameterized universal instance for the canonical usable-rules candidate. -/
def usableRulesConcreteCandidateConditionalInstance
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    UsableRulesUniversalInstance :=
  usableRulesResidualUniversalInstance (usableRulesConcreteCandidateResidual B)

/-- Every proof-bearing canonical usable-rules candidate projects to the universal confession surface. -/
theorem usableRulesConcreteCandidate_with_soundnessBridge_projects_to_universal_surface
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.Refines
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesResidualToGenericConfessionMove_refines_canonical
    (usableRulesConcreteCandidateResidual B)

/-- Every proof-bearing canonical usable-rules candidate is H-equivalent to the canonical confession move. -/
theorem usableRulesConcreteCandidate_with_soundnessBridge_is_HEquivalent_canonical
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.HEquivalent
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesResidualToGenericConfessionMove_HEquivalent_canonical
    (usableRulesConcreteCandidateResidual B)


/-- Closed universal instance for the canonical usable-rules route. -/
def usableRulesConcreteCandidateUniversalInstance :
    UsableRulesUniversalInstance :=
  usableRulesConcreteCandidateConditionalInstance
    usableRulesConcreteSoundnessBridge

/-- Closed universal-characterization data for the canonical usable-rules route. -/
def usableRulesConcreteCandidateUniversalCharacterizationData :
    UniversalConfessionCharacterizationData
      canonicalRouteEvidenceConfessionMove
      usableRulesConcreteCandidateUniversalInstance.move :=
  usableRulesResidualUniversalCharacterizationData
    usableRulesConcreteRouteResidual

/-- Closed optimality data for the canonical usable-rules route. -/
def usableRulesConcreteCandidateOptimalityData :
    OptimalityData
      canonicalRouteEvidenceConfessionMove
      usableRulesConcreteCandidateUniversalInstance.move :=
  usableRulesResidualOptimalityData usableRulesConcreteRouteResidual

/-- Closed discarded-information minimality data for the canonical usable-rules route. -/
def usableRulesConcreteCandidateDiscardedInformationMinimalityData :
    DiscardedInformationMinimalityData
      canonicalRouteEvidenceInformationTheoreticConfession
      usableRulesConcreteCandidateUniversalInstance.informationProfile :=
  usableRulesResidualDiscardedInformationMinimalityData
    usableRulesConcreteRouteResidual

/-- Unconditional refinement theorem for the canonical usable-rules route. -/
theorem usableRulesConcreteCandidate_projects_to_universal_surface :
    GenericConfessionMove.Refines
      usableRulesConcreteCandidateUniversalInstance.move
      canonicalConfessionMove :=
  usableRulesConcreteCandidate_with_soundnessBridge_projects_to_universal_surface
    usableRulesConcreteSoundnessBridge

/-- Unconditional H-equivalence theorem for the canonical usable-rules route. -/
theorem usableRulesConcreteCandidate_is_HEquivalent_canonical :
    GenericConfessionMove.HEquivalent
      usableRulesConcreteCandidateUniversalInstance.move
      canonicalConfessionMove :=
  usableRulesConcreteCandidate_with_soundnessBridge_is_HEquivalent_canonical
    usableRulesConcreteSoundnessBridge

end OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
