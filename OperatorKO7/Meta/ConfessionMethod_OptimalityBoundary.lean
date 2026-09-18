import OperatorKO7.Meta.ConfessionMethod_UniversalRouteLedger

/-!
# Confession Method Optimality Boundary

This module maps the closed universal-confession theorem-status ledger to
theorem-specific records.  All six theorem interfaces are theorem-projected on
their declared proof-bearing domains; optional physics-module tags record
provenance rather than unresolved obligations.
-/

namespace OperatorKO7.Meta.ConfessionMethodOptimalityBoundary

open OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger

/-- Optional supporting physics-module tags for theorem-boundary entries. -/
inductive SupportingPhaseModule where
  | L1RecordFormation
  | L2LandauerHeatBound
  | L3BornRuleFromLandauer
  | L4HawkingLandauerCycle
  | L5QECSyndromeAsStage2
  deriving DecidableEq, Repr

/-- Stable file-path names for the Phase L1-L5 tags. -/
def supportingPhaseModuleFile : SupportingPhaseModule → String
  | .L1RecordFormation => "OperatorKO7/Meta/Physics/RecordFormation.lean"
  | .L2LandauerHeatBound => "OperatorKO7/Meta/Physics/LandauerHeatBound.lean"
  | .L3BornRuleFromLandauer => "OperatorKO7/Meta/Physics/BornRuleFromLandauer.lean"
  | .L4HawkingLandauerCycle => "OperatorKO7/Meta/Physics/HawkingLandauerCycle.lean"
  | .L5QECSyndromeAsStage2 => "OperatorKO7/Meta/Physics/QECSyndromeAsStage2.lean"

/-- Proof-bearing input vocabulary retained for theorem-signature documentation. -/
inductive UniversalBoundaryHypothesis where
  | optimalityData
  | discardedInformationMinimalityData
  | confessionCostFloorData
  deriving DecidableEq, Repr

/-- Stable display names for the theorem-boundary hypothesis vocabulary. -/
def universalBoundaryHypothesisName : UniversalBoundaryHypothesis → String
  | .optimalityData => "OptimalityData canonical candidate"
  | .discardedInformationMinimalityData =>
      "DiscardedInformationMinimalityData Icanonical Icandidate"
  | .confessionCostFloorData => "ConfessionCostFloorData I"

/-- One theorem-by-theorem boundary record for the universal-confession surface. -/
structure OptimalityBoundaryEntry where
  theoremId : UniversalTheoremId
  theoremName : String
  status : UniversalTheoremStatus
  requiredHypothesis? : Option UniversalBoundaryHypothesis
  supportingPhaseModule? : Option SupportingPhaseModule

/-- The theorem-boundary entry for a named universal-confession theorem. -/
def optimalityBoundary : UniversalTheoremId → OptimalityBoundaryEntry
  | .universalConfessionCharacterization =>
      ⟨.universalConfessionCharacterization,
        universalTheoremName .universalConfessionCharacterization,
        .theoremProjected,
        none,
        none⟩
  | .confessionCostFloor =>
      ⟨.confessionCostFloor,
        universalTheoremName .confessionCostFloor,
        .theoremProjected,
        none,
        some .L2LandauerHeatBound⟩
  | .confessionConvergenceIffHEquivalent =>
      ⟨.confessionConvergenceIffHEquivalent,
        universalTheoremName .confessionConvergenceIffHEquivalent,
        .theoremProjected,
        none,
        none⟩
  | .optimalConfessionUniversalProperty =>
      ⟨.optimalConfessionUniversalProperty,
        universalTheoremName .optimalConfessionUniversalProperty,
        .theoremProjected,
        none,
        none⟩
  | .canonicalConfessionMinimizesDiscardedInformation =>
      ⟨.canonicalConfessionMinimizesDiscardedInformation,
        universalTheoremName .canonicalConfessionMinimizesDiscardedInformation,
        .theoremProjected,
        none,
        none⟩
  | .gaugeFixingIdentity =>
      ⟨.gaugeFixingIdentity,
        universalTheoremName .gaugeFixingIdentity,
        .theoremProjected,
        none,
        none⟩

/-- Stable theorem-boundary ledger. -/
def optimalityBoundaryLedger : List OptimalityBoundaryEntry :=
  [optimalityBoundary .universalConfessionCharacterization,
    optimalityBoundary .confessionCostFloor,
    optimalityBoundary .confessionConvergenceIffHEquivalent,
    optimalityBoundary .optimalConfessionUniversalProperty,
    optimalityBoundary .canonicalConfessionMinimizesDiscardedInformation,
    optimalityBoundary .gaugeFixingIdentity]

def unconditionallyTheoremBackedTheorems : List UniversalTheoremId :=
  [.universalConfessionCharacterization,
    .confessionCostFloor,
    .optimalConfessionUniversalProperty,
    .canonicalConfessionMinimizesDiscardedInformation,
    .confessionConvergenceIffHEquivalent,
    .gaugeFixingIdentity]

def conditionalOnOptimalityPayloadTheorems : List UniversalTheoremId :=
  []

def conditionalOnInformationPayloadTheorems : List UniversalTheoremId :=
  []

def conditionalOnInformationAndLandauerPayloadTheorems : List UniversalTheoremId :=
  []

/-- Predicate associating a theorem status with its designated ledger bucket. -/
def TheoremBucketWitness
    (theoremId : UniversalTheoremId) (status : UniversalTheoremStatus) : Prop :=
  (status = .theoremProjected ∧ theoremId ∈ unconditionallyTheoremBackedTheorems)
    ∨ (status = .conditionalOnOptimalityPayload
        ∧ theoremId ∈ conditionalOnOptimalityPayloadTheorems)
    ∨ (status = .conditionalOnInformationPayload
        ∧ theoremId ∈ conditionalOnInformationPayloadTheorems)
    ∨ (status = .conditionalOnInformationAndLandauerPayload
        ∧ theoremId ∈ conditionalOnInformationAndLandauerPayloadTheorems)

theorem optimalityBoundary_status_matches_ledger
    (theoremId : UniversalTheoremId) :
    (optimalityBoundary theoremId).status = universalTheoremStatus theoremId := by
  cases theoremId <;> rfl

theorem optimalityBoundary_entry_matches_bucket
    (theoremId : UniversalTheoremId) :
    TheoremBucketWitness theoremId (optimalityBoundary theoremId).status := by
  cases theoremId
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndLandauerPayloadTheorems,
    optimalityBoundary]

/-- Every universal-confession theorem has a unique status represented by one
boundary bucket. -/
theorem optimalityBoundary_exhaustive
    (theoremId : UniversalTheoremId) :
    ∃! status : UniversalTheoremStatus, TheoremBucketWitness theoremId status := by
  cases theoremId
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndLandauerPayloadTheorems] using hstatus

end OperatorKO7.Meta.ConfessionMethodOptimalityBoundary
