import OperatorKO7.Meta.BoundaryOperator.PromotionGate
import OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace
import OperatorKO7.Meta.LicensedBoundaryCalculus.DistinctionFace
import OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation

/-!
# Finite transport disposition registry

`transportRegistry` assigns one disposition to each of fifteen `TransportClaimKey` constructors.
Three entries contain verified forward-step simulations: orientation projection, distinction-edge
restriction, and observer quotient projection. The remaining entries contain `NoTransportCard`
records with a named missing proposition and a nonempty falsifier description. Verified-card
nontriviality is source-side; in particular, `orientationFaceCard` has `Unit` as its target.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.LicensedBoundaryCalculus.Audit
open OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace
open OperatorKO7.Meta.LicensedBoundaryCalculus.DistinctionFace
open OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

abbrev BOFClaimID := TransportClaimKey

def allBOFClaimIDs : List BOFClaimID := allTransportClaimKeys

def transportClaimName : BOFClaimID -> String
  | .orientationFace => "orientation-face"
  | .distinctionFace => "distinction-face"
  | .observerQuotient => "observer-quotient"
  | .normalization => "normalization"
  | .dependencyPairProjection => "dependency-pair-projection"
  | .qecFiniteAdmission => "qec-finite-admission"
  | .supervisoryEngine => "supervisory-engine"
  | .finiteMeasurementCarrier => "finite-measurement-carrier"
  | .landauerThermalErasure => "landauer-thermal-erasure"
  | .quantumMeasurement => "quantum-measurement"
  | .gravityUUET => "gravity-uuet"
  | .financePlug => "finance-plug"
  | .lawPlug => "law-plug"
  | .chemistryPlug => "chemistry-plug"
  | .riemannHypothesisAnalogy => "riemann-hypothesis-analogy"

/-- Existence of a verified card with the requested claim name and transport strength. -/
def NamedTransportObligation
    (claim : BOFClaimID) (strength : TransportStrength) : Prop :=
  ∃ card : VerifiedTransportCard,
    card.name = transportClaimName claim ∧ card.strength = strength

def namedNoTransportCard
    (claim : BOFClaimID) (tier : ClaimTier)
    (desiredStrength : TransportStrength)
    (missingName falsifierDescription : String)
    (hmissing : missingName ≠ "")
    (hfalsifier : falsifierDescription ≠ "")
    (currentMaximumStrength : Option TransportStrength := none)
    (sourceAnchorHints targetAnchorHints : List String := []) :
    NoTransportCard where
  name := transportClaimName claim
  missingTheorem :=
    { name := missingName
      name_nonempty := hmissing
      statement := NamedTransportObligation claim desiredStrength }
  currentMaximumStrength := currentMaximumStrength
  falsifierSpec :=
    sourceCounterexampleFalsifier falsifierDescription hfalsifier
  claimTier := tier
  sourceAnchorHints := sourceAnchorHints
  targetAnchorHints := targetAnchorHints

/-! ## Three verified forward-step simulations -/

def orientationFaceCard : VerifiedTransportCard where
  name := "orientation-face"
  Source := Bool
  Target := Unit
  sourceStep := (rdrsSourceARS boolStep_fixture).step
  targetStep := (rdrsProjectedARS unitStep_fixture).step
  forwardMap := boolOrientationFace_fixture.toMorphism.map
  backwardMap? := none
  strength := .forwardStepSimulation
  evidence := boolOrientationFace_fixture.toMorphism.map_step
  sourceNontrivial := ⟨false, true, by decide⟩
  preservedRelations := ["RDRS root step"]
  preservedObservables := ["projected RDRS state"]
  preservedResources := ["retained counter coordinate"]
  claimTier := .theorem
  sourceAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace.boolStep_fixture
  targetAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace.unitStep_fixture
  mapAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace.toMorphism

def distinctionFaceCard : VerifiedTransportCard where
  name := "distinction-face"
  Source := Trace
  Target := Trace
  sourceStep := ko7DistinctionFace_fixture.toMorphism.admitted
  targetStep := ko7SafeARS.step
  forwardMap := ko7DistinctionFace_fixture.toMorphism.map
  backwardMap? := none
  strength := .forwardStepSimulation
  evidence := ko7DistinctionFace_fixture.toMorphism.map_step
  sourceNontrivial := ⟨void, integrate void, by decide⟩
  preservedRelations := ["guard-admitted SafeStep edge"]
  preservedObservables := ["trace state"]
  preservedResources := []
  claimTier := .theorem
  sourceAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.ko7RawARS
  targetAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.ko7SafeARS
  mapAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.DistinctionFace.toMorphism

def observerQuotientCard : VerifiedTransportCard where
  name := "observer-quotient"
  Source := ChainNode
  Target := ObserverQuotient chainObserver_fixture
  sourceStep := chainARS_fixture.step
  targetStep :=
    (observerQuotientARS chainARS_fixture chainObserver_fixture).step
  forwardMap := quotientMap chainObserver_fixture
  backwardMap? := none
  strength := .forwardStepSimulation
  evidence :=
    (quotientProjection chainARS_fixture chainObserver_fixture).map_step
  sourceNontrivial := ⟨.source, .target, by decide⟩
  preservedRelations := ["representative-generated quotient edge"]
  preservedObservables := ["observer orbit"]
  preservedResources := []
  claimTier := .theorem
  sourceAnchor :=
    ``OperatorKO7.Meta.LicensedBoundaryCalculus.chainARS_fixture
  targetAnchor :=
    ``OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation.observerQuotientARS
  mapAnchor :=
    ``OperatorKO7.Meta.OperationalInexpressibility.OrbitSimulation.quotientProjection

structure RegisteredTransport where
  claim : BOFClaimID
  disposition : TransportDisposition

def entryForClaim : BOFClaimID -> RegisteredTransport
  | .orientationFace => ⟨.orientationFace, .verified orientationFaceCard⟩
  | .distinctionFace => ⟨.distinctionFace, .verified distinctionFaceCard⟩
  | .observerQuotient => ⟨.observerQuotient, .verified observerQuotientCard⟩
  | .normalization =>
      ⟨.normalization, .blocked <| namedNoTransportCard .normalization
        .noTransport .forwardReachSimulation
        "normalization_transport_preserves_and_reflects_normal_forms"
        "A licensed path whose endpoint normal-form status is not preserved falsifies the proposed transport."
        (by decide) (by decide)⟩
  | .dependencyPairProjection =>
      ⟨.dependencyPairProjection, .blocked <| namedNoTransportCard
        .dependencyPairProjection .noTransport .forwardReachSimulation
        "dependency_pair_projection_reach_simulation"
        "A minimal dependency-pair chain absent from the projected boundary reach relation falsifies the proposed map."
        (by decide) (by decide)⟩
  | .qecFiniteAdmission =>
      ⟨.qecFiniteAdmission, .blocked <| namedNoTransportCard
        .qecFiniteAdmission .noTransport .forwardStepSimulation
        "qec_admission_to_lbc_forward_step_transport"
        "A checked QEC admission whose LBC image is not admitted falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.Qec_BoundaryOperator_inhabited"]⟩
  | .supervisoryEngine =>
      ⟨.supervisoryEngine, .blocked <| namedNoTransportCard
        .supervisoryEngine .noTransport .forwardStepSimulation
        "runtime_engine_to_lbc_trace_transport"
        "A runtime verdict, typed output, trace, or ledger delta unequal to its LBC image falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.supervisory_boundary_instance_nonvacuous"]⟩
  | .finiteMeasurementCarrier =>
      ⟨.finiteMeasurementCarrier, .blocked <| namedNoTransportCard
        .finiteMeasurementCarrier .noTransport .forwardStepSimulation
        "finite_measurement_branch_to_boundary_step_transport"
        "A legal finite measurement branch whose weight or verdict is not preserved falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.finite_measurement_instance_nonvacuous"]⟩
  | .landauerThermalErasure =>
      ⟨.landauerThermalErasure, .blocked <| namedNoTransportCard
        .landauerThermalErasure .noTransport .forwardStepSimulation
        "thermal_erasure_process_to_boundary_transaction_transport"
        "A committed thermal process whose mapped debit violates the calibrated floor falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.boundaryLandauerCostDominatesPerBitFloor"]⟩
  | .quantumMeasurement =>
      ⟨.quantumMeasurement, .blocked <| namedNoTransportCard
        .quantumMeasurement .analogy .forwardStepSimulation
        "quantum_measurement_to_boundary_admission_transport"
        "A finite quantum measurement satisfying the source premises but breaking the admission image falsifies the analogy."
        (by decide) (by decide)⟩
  | .gravityUUET =>
      ⟨.gravityUUET, .blocked <| namedNoTransportCard
        .gravityUUET .analogy .forwardStepSimulation
        "uuet_transition_to_boundary_ledger_transport"
        "A UUET transition whose ledger image fails the named invariant falsifies the analogy."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.UUETBridge.uuet_bridge_nonvacuous"]⟩
  | .financePlug =>
      ⟨.financePlug, .blocked <| namedNoTransportCard
        .financePlug .noTransport .forwardStepSimulation
        "finance_state_machine_to_lbc_typed_output_transport"
        "A finance plug transition whose verdict escapes the LBC typed-output image falsifies the transport."
        (by decide) (by decide)⟩
  | .lawPlug =>
      ⟨.lawPlug, .blocked <| namedNoTransportCard
        .lawPlug .noTransport .forwardStepSimulation
        "law_state_machine_to_lbc_typed_output_transport"
        "A law plug transition whose verdict escapes the LBC typed-output image falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.Law_BoundaryOperator_inhabited"]⟩
  | .chemistryPlug =>
      ⟨.chemistryPlug, .blocked <| namedNoTransportCard
        .chemistryPlug .noTransport .forwardStepSimulation
        "chemistry_state_machine_to_lbc_typed_output_transport"
        "A chemistry plug transition whose verdict escapes the LBC typed-output image falsifies the transport."
        (by decide) (by decide) none
        ["OperatorKO7.Meta.BoundaryOperator.Pharma_BoundaryOperator_inhabited"]⟩
  | .riemannHypothesisAnalogy =>
      ⟨.riemannHypothesisAnalogy, .blocked <| namedNoTransportCard
        .riemannHypothesisAnalogy .analogy .forwardReachSimulation
        "arithmetic_zero_side_to_lbc_reach_transport"
        "An arithmetic boundary map that fails to preserve the named zero-side invariant falsifies the analogy."
        (by decide) (by decide)⟩

def transportRegistry : List RegisteredTransport :=
  allBOFClaimIDs.map entryForClaim

def EveryBOFClaimCovered (registry : List RegisteredTransport) : Prop :=
  ∀ claim, ∃ entry, entry ∈ registry ∧ entry.claim = claim

def RegisteredTransport.Governed (entry : RegisteredTransport) : Prop :=
  match entry.disposition with
  | .verified card =>
      card.claimTier = .theorem ∨ card.claimTier = .conditional ∨
        card.claimTier = .model
  | .blocked card =>
      card.claimTier = .analogy ∨ card.claimTier = .noTransport ∨
        card.claimTier = .externalCitation

def RegisteredTransport.NoPlaceholder (entry : RegisteredTransport) : Prop :=
  match entry.disposition with
  | .verified card => ¬ card.UsesUnitPlaceholder
  | .blocked _ => True

def RegisteredTransport.PromotesLanguage
    (entry : RegisteredTransport) (language : ClaimLanguage) : Prop :=
  match entry.disposition with
  | .verified card => StrengthSufficient card.strength language
  | .blocked _ => False

theorem noTransportCard_has_typed_evidence (card : NoTransportCard) :
    card.missingTheorem.name ≠ "" ∧
      card.falsifierSpec.description ≠ "" :=
  ⟨card.missingTheorem.name_nonempty,
    card.falsifierSpec.description_nonempty⟩

/-- Characterize language promotion by a verified disposition carrying sufficient strength. -/
theorem promoted_language_iff_evidence_strength
    (entry : RegisteredTransport) (language : ClaimLanguage) :
    entry.PromotesLanguage language ↔
      ∃ card : VerifiedTransportCard,
        entry.disposition = .verified card ∧
          StrengthSufficient card.strength language := by
  cases hdisposition : entry.disposition with
  | verified card =>
      simp [RegisteredTransport.PromotesLanguage, hdisposition]
  | blocked card =>
      simp [RegisteredTransport.PromotesLanguage, hdisposition]

theorem entryForClaim_mem (claim : BOFClaimID) :
    entryForClaim claim ∈ transportRegistry := by
  cases claim <;> simp [transportRegistry, allBOFClaimIDs,
    allTransportClaimKeys, entryForClaim]

private theorem entryForClaim_claim (claim : BOFClaimID) :
    (entryForClaim claim).claim = claim := by
  cases claim <;> rfl

theorem all_bof_cross_domain_claims_registered :
    EveryBOFClaimCovered transportRegistry := by
  intro claim
  exact ⟨entryForClaim claim, entryForClaim_mem claim,
    entryForClaim_claim claim⟩

theorem entryForClaim_governed (claim : BOFClaimID) :
    (entryForClaim claim).Governed := by
  cases claim <;>
    simp [entryForClaim, RegisteredTransport.Governed,
      namedNoTransportCard, orientationFaceCard, distinctionFaceCard,
      observerQuotientCard, sourceCounterexampleFalsifier]

theorem every_registry_entry_governed
    {entry : RegisteredTransport} (hentry : entry ∈ transportRegistry) :
    entry.Governed := by
  rw [transportRegistry] at hentry
  rcases List.mem_map.mp hentry with ⟨claim, _hclaim, rfl⟩
  exact entryForClaim_governed claim

/-- Every verified registry entry carries a source-side distinctness witness. -/
theorem no_placeholder_transport_cards
    {entry : RegisteredTransport} (hentry : entry ∈ transportRegistry) :
    entry.NoPlaceholder := by
  rw [transportRegistry] at hentry
  rcases List.mem_map.mp hentry with ⟨claim, _hclaim, rfl⟩
  cases claim <;>
    simp [entryForClaim, RegisteredTransport.NoPlaceholder,
      verifiedTransportCard_not_unit_placeholder]

theorem transportRegistry_length_fixture : transportRegistry.length = 15 := by
  rfl

#check all_bof_cross_domain_claims_registered
#check noTransportCard_has_typed_evidence
#check promoted_language_iff_evidence_strength
#check every_registry_entry_governed
#check no_placeholder_transport_cards
#check transportRegistry_length_fixture
#print axioms all_bof_cross_domain_claims_registered
#print axioms noTransportCard_has_typed_evidence
#print axioms promoted_language_iff_evidence_strength
#print axioms every_registry_entry_governed
#print axioms no_placeholder_transport_cards
#print axioms transportRegistry_length_fixture

end OperatorKO7.Meta.BoundaryOperator
