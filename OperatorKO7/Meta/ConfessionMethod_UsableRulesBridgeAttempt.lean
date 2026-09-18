import OperatorKO7.Meta.ConfessionMethod_UniversalUsableRules

/-!
# Confession Method Usable-Rules Bridge Boundary

## Formal Scope

The obstruction structures are retained as diagnostics for two narrower failed
construction attempts.  The canonical bridge itself is now inhabited by the
independent KO7 polynomial termination theorem, and the exported attempt result
is therefore witnessed rather than obstructed.
-/

namespace OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

open OperatorKO7
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules

/-- Required bridge type for the concrete usable-rules candidate. -/
abbrev ConcreteUsableRulesBridgeWitness : Prop :=
  UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate

private abbrev ConcreteUsableRulesRouteLicense : Type :=
  PUnit

/-- Universal admission carrying the canonical source-soundness bridge. -/
structure ConcreteUsableRulesUniversalAdmission where
  bridge : ConcreteUsableRulesBridgeWitness


/-- Canonical proof-bearing bridge witness. -/
def concreteUsableRulesBridgeWitness : ConcreteUsableRulesBridgeWitness :=
  usableRulesConcreteSoundnessBridge

/-- Canonical universal admission for usable rules. -/
def concreteUsableRulesUniversalAdmission :
    ConcreteUsableRulesUniversalAdmission :=
  ⟨concreteUsableRulesBridgeWitness⟩

/-- The universal usable-rules admission is inhabited unconditionally. -/
theorem concreteUsableRulesUniversalAdmission_inhabited :
    Nonempty ConcreteUsableRulesUniversalAdmission :=
  ⟨concreteUsableRulesUniversalAdmission⟩

/-- Convert an explicitly supplied bridge into the conditional admission
package. -/
def concreteUsableRulesUniversalAdmissionOfBridge
    (B : ConcreteUsableRulesBridgeWitness) :
    ConcreteUsableRulesUniversalAdmission :=
  ⟨B⟩

/-- Recover the conditional universal instance determined by an admission. -/
def ConcreteUsableRulesUniversalAdmission.conditionalInstance
    (admission : ConcreteUsableRulesUniversalAdmission) :
    UsableRulesUniversalInstance :=
  usableRulesConcreteCandidateConditionalInstance admission.bridge

/-- Route-local rank agreement available for the concrete candidate. -/
def usableRulesConcreteRouteLocalWitnessField : UsableRulesRouteLocalWitnessField :=
  usableRulesCommonRouteLocalWitnessField

/-- Dependency-pair substrate evidence available alongside the closed source-soundness transport. -/
theorem usableRulesConcreteDPSubstrateEvidence :
    UsableRulesDPSubstrateEvidence :=
  usableRulesDPSubstrateEvidence_witness

/-- Universal move obtained from the shared route-evidence rank.  Processor
soundness is supplied separately by `concreteUsableRulesBridgeWitness`. -/
def usableRulesConcreteCommonRouteMove :
    UniversalMove KO7Carrier ko7ConfessionVerdict ConcreteUsableRulesRouteLicense :=
  routeEvidenceToGenericConfessionMove
    confessionRouteConvergencePackage.commonRouteEvidence
    usableRulesConcreteRouteLocalWitnessField.commonRoute_rank_eq_dpConfession

/-- Rank-level H-equivalence between the shared candidate move and the canonical
confession move. This theorem does not transport pair-problem termination to
the source relation. -/
theorem usableRulesConcreteCommonRoute_is_HEquivalent_canonical :
    Nonempty
      (GenericConfessionMove.HEquivalenceWitness
        usableRulesConcreteCommonRouteMove canonicalConfessionMove) := by
  exact routeEvidenceToGenericConfessionMove_HEquivalent_canonical
    confessionRouteConvergencePackage.commonRouteEvidence
    usableRulesConcreteRouteLocalWitnessField.commonRoute_rank_eq_dpConfession

/-- Diagnostic record for a construction attempt that did not itself produce
the DP-problem-to-source-`Step` transport theorem. -/
structure UsableRulesSoundnessBridgeObstruction where
  candidate : UsableRulesConcreteRouteCandidate
  attemptedSubstrate : String
  availableRouteAgreement :
    candidate.toRouteEvidence candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence
  availableForgettingRankAgreement :
    (OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofRouteEvidence
      (candidate.toRouteEvidence candidate.witness)).rank = dpConfession.rank
  openBridgeObligations : List UsableRulesBridgeObligation
  openBridgeObligations_exact :
    openBridgeObligations =
      [UsableRulesBridgeObligation.sourceSoundnessTransport]
  obstructionSummary : String
  scopeNote : String

/-- Historical diagnostic for the shared dependency-pair-only construction.
The canonical bridge is supplied independently below. -/
def usableRulesSoundnessBridgeObstruction :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "shared dependency-pair route evidence"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations :=
    [UsableRulesBridgeObligation.sourceSoundnessTransport]
  openBridgeObligations_exact := rfl
  obstructionSummary :=
    "The candidate rank agrees with the dependency-pair projection, but no theorem in this module transports pair-problem well-foundedness to root termination of the original Step relation."
  scopeNote :=
    "H-equivalence of rank maps and an external-license tag are not a usable-rules processor soundness theorem."

/-- Result type for a bridge attempt. -/
inductive UsableRulesSoundnessBridgeAttempt where
  | witnessed (bridge : ConcreteUsableRulesBridgeWitness)
  | obstructed (obstruction : UsableRulesSoundnessBridgeObstruction)

/-- Final bridge-attempt result: the canonical proof-bearing bridge is witnessed. -/
def usableRulesSoundnessBridgeAttemptResult :
    UsableRulesSoundnessBridgeAttempt :=
  .witnessed concreteUsableRulesBridgeWitness

/-- Diagnostic record for the Arts-Giesl-labelled construction route before
using the independently proved KO7 source-termination theorem. -/
def usableRulesSoundnessBridgeObstruction_artsGiesl :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "Arts-Giesl derivational-complexity route"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations :=
    [UsableRulesBridgeObligation.sourceSoundnessTransport]
  openBridgeObligations_exact := rfl
  obstructionSummary :=
    "The derivational-complexity layer does not provide the required usable-rules DP-problem-to-source transport for this candidate."
  scopeNote :=
    "The Arts-Giesl license tag records intended external provenance; it is not itself a Lean proof of the transport theorem."

/-- Diagnostic record for the LCEL-labelled construction route before using
the independently proved KO7 source-termination theorem. -/
def usableRulesSoundnessBridgeObstruction_lcel :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "LCEL native DP/emitter license route"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations :=
    [UsableRulesBridgeObligation.sourceSoundnessTransport]
  openBridgeObligations_exact := rfl
  obstructionSummary :=
    "The LCEL-side license surface does not provide the required usable-rules DP-problem-to-source transport for this candidate."
  scopeNote :=
    "An external-license carrier is metadata unless a theorem connects it to source-system termination."

/-- Arts-Giesl-labelled route closed by the canonical bridge. -/
def usableRulesSoundnessBridgeAttemptResult_artsGiesl :
    UsableRulesSoundnessBridgeAttempt :=
  .witnessed concreteUsableRulesBridgeWitness

/-- LCEL-labelled route closed by the canonical bridge. -/
def usableRulesSoundnessBridgeAttemptResult_lcel :
    UsableRulesSoundnessBridgeAttempt :=
  .witnessed concreteUsableRulesBridgeWitness

/-- Both labelled construction routes now project to the same witnessed bridge. -/
theorem usableRulesSoundnessBridgeAttemptResult_combined :
    [usableRulesSoundnessBridgeAttemptResult_artsGiesl,
      usableRulesSoundnessBridgeAttemptResult_lcel]
      = [UsableRulesSoundnessBridgeAttempt.witnessed
            concreteUsableRulesBridgeWitness,
          UsableRulesSoundnessBridgeAttempt.witnessed
            concreteUsableRulesBridgeWitness] :=
  rfl

/-- Admission is equivalent to bridge inhabitation; both sides are inhabited above. -/
theorem usableRulesUniversal_iff_soundnessBridgeWitnessed :
    Nonempty ConcreteUsableRulesUniversalAdmission
      ↔ Nonempty ConcreteUsableRulesBridgeWitness := by
  constructor
  · intro h
    rcases h with ⟨admission⟩
    exact ⟨admission.bridge⟩
  · intro h
    rcases h with ⟨bridge⟩
    exact ⟨concreteUsableRulesUniversalAdmissionOfBridge bridge⟩


/-- The canonical bridge closes the fifth confession route. -/
theorem usableRules_fifth_route_closed : HasUsableRulesConfessionRoute :=
  usableRulesConcreteRoute_inhabited

/-- The final bridge attempt is witnessed. -/
theorem usableRulesSoundnessBridgeAttemptResult_witnessed :
    usableRulesSoundnessBridgeAttemptResult =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  rfl

end OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt
