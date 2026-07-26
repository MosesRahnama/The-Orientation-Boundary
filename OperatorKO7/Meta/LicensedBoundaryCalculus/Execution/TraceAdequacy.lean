import OperatorKO7.Meta.LicensedBoundaryCalculus.Execution.EventSemantics

/-!
# Trace adequacy

An adequate trace is the canonical trace of its certified decision.
The remaining fields expose four consequences:
event soundness, required-event completeness, morphism agreement, and output
agreement. They are stored explicitly for use by dependent builders.

## Audit slots

Relation: domain and admitted predicates of the executed morphism.
Closure: exact finite decision trace.
Trust: kernel-only dependent case analysis.
Scope: one boundary execution and its finite event trace.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

/-- Propositional meaning of a decision at one input. -/
def DecisionMatchesMorphism
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B)
    (input : BoundaryExecutionInput F) : BoundaryDecision → Prop
  | .refuseState =>
      ¬ F.domain input.source ∨ ¬ F.domain input.proposedTarget
  | .refuseEdge =>
      F.domain input.source ∧ F.domain input.proposedTarget ∧
        ¬ F.admitted input.source input.proposedTarget
  | .commit => F.admitted input.source input.proposedTarget

/-- Propositional meaning of the output attached to one decision. -/
def OutputMatchesMorphism
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B)
    (input : BoundaryExecutionInput F) :
    BoundaryDecision → Option B.Carrier → Prop
  | .refuseState, output => output = none
  | .refuseEdge, output => output = none
  | .commit, output =>
      ∃ admitted : F.admitted input.source input.proposedTarget,
        output = some (F.map
          ⟨input.proposedTarget, F.admitted_target_domain admitted⟩)

/-- Every decision certificate entails the decision's morphism semantics. -/
theorem DecisionCertificate.decision_matches
    {A : ARS.{u}} {B : ARS.{v}}
    {F : PartialLicensedReductionMorphism A B}
    {input : BoundaryExecutionInput F}
    {decision : BoundaryDecision} {output : Option B.Carrier}
    (certificate : DecisionCertificate F input decision output) :
    DecisionMatchesMorphism F input decision := by
  cases certificate with
  | stateRefusal outside =>
      change ¬ F.domain input.source ∨ ¬ F.domain input.proposedTarget
      tauto
  | edgeRefusal inside rejected =>
      exact ⟨inside.1, inside.2, rejected⟩
  | commit admitted => exact admitted

/-- Every decision certificate entails the unique permitted output shape. -/
theorem DecisionCertificate.output_matches
    {A : ARS.{u}} {B : ARS.{v}}
    {F : PartialLicensedReductionMorphism A B}
    {input : BoundaryExecutionInput F}
    {decision : BoundaryDecision} {output : Option B.Carrier}
    (certificate : DecisionCertificate F input decision output) :
    OutputMatchesMorphism F input decision output := by
  cases certificate with
  | stateRefusal outside => rfl
  | edgeRefusal inside rejected => rfl
  | commit admitted => exact ⟨admitted, rfl⟩

/-- Full trace certificate for one execution result. -/
structure TraceAdequacy
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B)
    (input : BoundaryExecutionInput F)
    (result : BoundaryExecutionResult F input) : Prop where
  traceExact : result.trace = decisionTrace result.decision
  everyEventSound : ∀ event ∈ result.trace,
    EventSemantics result.decision event.kind
  requiredEventsComplete : ∀ kind,
    EventSemantics result.decision kind →
      ∃ event ∈ result.trace, event.kind = kind
  decisionMatchesMorphism :
    DecisionMatchesMorphism F input result.decision
  outputMatchesMap :
    OutputMatchesMorphism F input result.decision result.output?

/-- The generic `execute` function emits a trace satisfying `TraceAdequacy`. -/
theorem execute_trace_adequate
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B)
    (input : BoundaryExecutionInput F) :
    TraceAdequacy F input (execute F input) := by
  refine
    { traceExact := execute_trace_eq F input
      everyEventSound := ?_
      requiredEventsComplete := ?_
      decisionMatchesMorphism :=
        (execute F input).certificate.decision_matches
      outputMatchesMap := (execute F input).certificate.output_matches }
  · intro event hevent
    rw [execute_trace_eq F input] at hevent
    exact (mem_decisionTrace_iff_eventSemantics _ _).mp hevent
  · intro kind hkind
    refine ⟨⟨kind⟩, ?_, rfl⟩
    rw [execute_trace_eq F input]
    exact (mem_decisionTrace_iff_eventSemantics _ _).mpr hkind

/-! ## Counterexample fixtures -/

open PartialLicensedReductionMorphism

theorem stateRefusalInput_outside_fixture :
    ¬ (partialChain_fixture.domain stateRefusalInput_fixture.source ∧
      partialChain_fixture.domain stateRefusalInput_fixture.proposedTarget) := by
  rintro ⟨_, htarget⟩
  exact partialChain_fixture_undefined_target htarget

/-- A manually fabricated empty trace carrying a genuine refusal certificate. -/
def emptyStateRefusalResult_fixture :
    BoundaryExecutionResult partialChain_fixture stateRefusalInput_fixture where
  decision := .refuseState
  trace := []
  output? := none
  certificate := .stateRefusal stateRefusalInput_outside_fixture

/-- Adequacy of the empty refusal fixture implies a contradictory trace
equality. -/
theorem empty_state_refusal_not_adequate_fixture :
    ¬ TraceAdequacy partialChain_fixture stateRefusalInput_fixture
      emptyStateRefusalResult_fixture := by
  intro certificate
  have h := certificate.traceExact
  cases h

/-- A manually fabricated certificate event attached to a commit. -/
def fabricatedCertificateCommitResult_fixture :
    BoundaryExecutionResult
      (PartialLicensedReductionMorphism.id chainARS_fixture)
      commitInput_fixture where
  decision := .commit
  trace := [⟨.certificateBit⟩]
  output? :=
    some ((PartialLicensedReductionMorphism.id chainARS_fixture).map
      ⟨ChainNode.target, trivial⟩)
  certificate := .commit ChainStep.descend

/-- The fabricated certificate-bit trace fails `TraceAdequacy` for a commit. -/
theorem fabricated_certificate_event_not_adequate_fixture :
    ¬ TraceAdequacy
      (PartialLicensedReductionMorphism.id chainARS_fixture)
      commitInput_fixture fabricatedCertificateCommitResult_fixture := by
  intro certificate
  have hsound := certificate.everyEventSound
    ⟨.certificateBit⟩ (by simp [fabricatedCertificateCommitResult_fixture])
  exact certificateBit_not_generic_event .commit hsound

/-- The out-of-domain fixture's generated decision differs from `.commit`. -/
theorem commit_outside_domain_impossible_fixture :
    (execute partialChain_fixture stateRefusalInput_fixture).decision ≠
      .commit := by
  intro hcommit
  have h := (execute_commit_iff_domain_and_admitted
    partialChain_fixture stateRefusalInput_fixture).mp hcommit
  exact partialChain_fixture_undefined_target h.2.1

#check @execute_trace_adequate
#check empty_state_refusal_not_adequate_fixture
#check fabricated_certificate_event_not_adequate_fixture
#check commit_outside_domain_impossible_fixture
#print axioms DecisionCertificate.decision_matches
#print axioms DecisionCertificate.output_matches
#print axioms execute_trace_adequate
#print axioms empty_state_refusal_not_adequate_fixture
#print axioms fabricated_certificate_event_not_adequate_fixture
#print axioms commit_outside_domain_impossible_fixture

end OperatorKO7.Meta.LicensedBoundaryCalculus
