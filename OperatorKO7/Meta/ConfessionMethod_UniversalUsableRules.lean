import OperatorKO7.Meta.ConfessionMethod_UniversalInstances
import OperatorKO7.Meta.ConfessionMethod_UsableRulesConcrete

/-!
# Confession Method Universal Usable Rules

This module does not invent a new usable-rules confession method. Instead it
packages the existing usable-rules residual and concrete-candidate boundaries
into the universal confession surface introduced for WS-A'.

The key status is explicit:
- route-evidence agreement with the common KO7 confession core is already
  available in the source tree;
- admission of a usable-rules route still depends on the explicit
  soundness-bridge object carried by the residual package.
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
  OperatorKO7.Meta.ConfessionMethodUniversalInstances.ko7ConfessionVerdict

private abbrev UniversalUsableRulesRouteLicense : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalInstances.UniversalRouteLicense

/-- Any admitted usable-rules residual package already recovers the canonical
DP confession rank at the route-evidence layer. -/
theorem usableRulesResidual_routeEvidence_rank_eq_dpConfession
    (R : UsableRulesConfessionRouteResidualObligation) :
    (R.toRouteEvidence R.witness).rank = dpConfession.rank := by
  simpa using usableRulesResidual_projects_forgetting_rank R

/-- Route-evidence canonical move for the universal usable-rules theorem data.
This keeps the license type aligned with the conditional usable-rules route. -/
def canonicalRouteEvidenceConfessionMove :
    UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
      UniversalUsableRulesRouteLicense :=
  routeEvidenceToGenericConfessionMove
    schemaDPGenericRouteEvidence
    dpRouteEvidence_rank_eq_dpConfession

/-- Route-evidence information profile matching the conditional usable-rules
license surface. -/
def canonicalRouteEvidenceInformationTheoreticConfession :
    UniversalInfo canonicalRouteEvidenceConfessionMove :=
  routeEvidenceToInformationTheoreticConfession
    schemaDPGenericRouteEvidence
    dpRouteEvidence_rank_eq_dpConfession

/-- Conditional universal wrapper for an admitted usable-rules residual
package. The route stays conditional because inhabiting the residual package
still requires an explicit soundness bridge. -/
def usableRulesResidualToGenericConfessionMove
    (R : UsableRulesConfessionRouteResidualObligation) :
    UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
      UniversalUsableRulesRouteLicense :=
  routeEvidenceToGenericConfessionMove
    (R.toRouteEvidence R.witness)
    (usableRulesResidual_routeEvidence_rank_eq_dpConfession R)

/-- Abstract information profile attached to the admitted usable-rules wrapper.
The profile remains quotient-level and does not claim a mechanized information
or Landauer theorem. -/
def usableRulesResidualToInformationTheoreticConfession
    (R : UsableRulesConfessionRouteResidualObligation) :
    UniversalInfo (usableRulesResidualToGenericConfessionMove R) :=
  routeEvidenceToInformationTheoreticConfession
    (R.toRouteEvidence R.witness)
    (usableRulesResidual_routeEvidence_rank_eq_dpConfession R)

/-- Any admitted usable-rules residual package projects to the canonical
confession move. -/
theorem usableRulesResidualToGenericConfessionMove_refines_canonical
    (R : UsableRulesConfessionRouteResidualObligation) :
    GenericConfessionMove.Refines
      (usableRulesResidualToGenericConfessionMove R)
      canonicalConfessionMove :=
  routeEvidenceToGenericConfessionMove_refines_canonical
    (R.toRouteEvidence R.witness)
    (usableRulesResidual_routeEvidence_rank_eq_dpConfession R)

/-- Any admitted usable-rules residual package is H-equivalent to the canonical
confession move. -/
theorem usableRulesResidualToGenericConfessionMove_HEquivalent_canonical
    (R : UsableRulesConfessionRouteResidualObligation) :
    GenericConfessionMove.HEquivalent
      (usableRulesResidualToGenericConfessionMove R)
      canonicalConfessionMove :=
  routeEvidenceToGenericConfessionMove_HEquivalent_canonical
    (R.toRouteEvidence R.witness)
    (usableRulesResidual_routeEvidence_rank_eq_dpConfession R)

/-- Conditional universal-characterization data for an admitted usable-rules
residual package. -/
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
          routeEvidenceToGenericConfessionMove,
          rankToGenericConfessionMove] using
          congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x
    }⟩

/-- Conditional optimality package for an admitted usable-rules residual
package. The uniqueness witness stays quotient-level, exactly as in the rest of
this honest theorem surface. -/
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
      routeEvidenceToGenericConfessionMove,
      rankToGenericConfessionMove] using
      (congrFun (usableRulesResidual_routeEvidence_rank_eq_dpConfession R) x).symm

/-- Conditional minimality package for an admitted usable-rules residual
package. -/
def usableRulesResidualDiscardedInformationMinimalityData
    (R : UsableRulesConfessionRouteResidualObligation) :
    DiscardedInformationMinimalityData
      canonicalRouteEvidenceInformationTheoreticConfession
      (usableRulesResidualToInformationTheoreticConfession R) where
  canonical_le_candidate := by
    simp [canonicalRouteEvidenceInformationTheoreticConfession,
      usableRulesResidualToInformationTheoreticConfession,
      routeEvidenceToInformationTheoreticConfession]

/-- API package for a usable-rules route once the residual package is actually
inhabited. -/
structure ConditionalUsableRulesUniversalInstance where
  residual : UsableRulesConfessionRouteResidualObligation
  move : UniversalMove UniversalUsableRulesKO7Carrier UniversalUsableRulesKO7Verdict
    UniversalUsableRulesRouteLicense
  informationProfile : UniversalInfo move

/-- Package an admitted usable-rules residual route as a universal instance. -/
def usableRulesResidualUniversalInstance
    (R : UsableRulesConfessionRouteResidualObligation) :
    ConditionalUsableRulesUniversalInstance where
  residual := R
  move := usableRulesResidualToGenericConfessionMove R
  informationProfile := usableRulesResidualToInformationTheoreticConfession R

/-- The concrete usable-rules candidate becomes a residual package only from an
explicit soundness bridge. This is the exact conditional boundary carried
forward into the universal surface. -/
def usableRulesConcreteCandidateResidual
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteRouteCandidate_to_residual usableRulesConcreteRouteCandidate B

/-- Conditional universal instance for the canonical usable-rules candidate.
It exists only when the explicit soundness bridge is supplied. -/
def usableRulesConcreteCandidateConditionalInstance
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    ConditionalUsableRulesUniversalInstance :=
  usableRulesResidualUniversalInstance (usableRulesConcreteCandidateResidual B)

/-- Exact conditional corollary for the canonical usable-rules candidate: once
its explicit soundness bridge is supplied, the candidate projects to the
universal confession surface. -/
theorem usableRulesConcreteCandidate_with_soundnessBridge_projects_to_universal_surface
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.Refines
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesResidualToGenericConfessionMove_refines_canonical
    (usableRulesConcreteCandidateResidual B)

/-- Exact conditional H-equivalence corollary for the canonical usable-rules
candidate. -/
theorem usableRulesConcreteCandidate_with_soundnessBridge_is_HEquivalent_canonical
    (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.HEquivalent
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesResidualToGenericConfessionMove_HEquivalent_canonical
    (usableRulesConcreteCandidateResidual B)

end OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
