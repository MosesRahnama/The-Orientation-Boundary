import OperatorKO7.Meta.ConfessionMethod_UniversalRouteLedger

/-!
# Confession Method Optimality Boundary

This module maps the closed universal-confession theorem-status ledger to
theorem-specific records.  All six theorem interfaces are theorem-projected on
their declared proof-bearing domains; optional supporting-module tags record
provenance rather than unresolved obligations.
-/

namespace OperatorKO7.Meta.ConfessionMethodOptimalityBoundary

open OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger

/-- Optional supporting-module tags for theorem-boundary entries. -/
inductive SupportingPhaseModule where
  | L1
  | L2
  | L3
  | L4
  | L5
  deriving DecidableEq, Repr

/-- Stable names for the L1-L5 tags. -/
def supportingPhaseModuleFile : SupportingPhaseModule → String
  | .L1 => "L1"
  | .L2 => "L2"
  | .L3 => "L3"
  | .L4 => "L4"
  | .L5 => "L5"

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
        some .L2⟩
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

def conditionalOnInformationAndCostPayloadTheorems : List UniversalTheoremId :=
  []

/-- Predicate associating a theorem status with its designated ledger bucket. -/
def TheoremBucketWitness
    (theoremId : UniversalTheoremId) (status : UniversalTheoremStatus) : Prop :=
  (status = .theoremProjected ∧ theoremId ∈ unconditionallyTheoremBackedTheorems)
    ∨ (status = .conditionalOnOptimalityPayload
        ∧ theoremId ∈ conditionalOnOptimalityPayloadTheorems)
    ∨ (status = .conditionalOnInformationPayload
        ∧ theoremId ∈ conditionalOnInformationPayloadTheorems)
    ∨ (status = .conditionalOnInformationAndCostPayload
        ∧ theoremId ∈ conditionalOnInformationAndCostPayloadTheorems)

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
    conditionalOnInformationAndCostPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndCostPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndCostPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndCostPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndCostPayloadTheorems,
    optimalityBoundary]
  · simp [TheoremBucketWitness,
    unconditionallyTheoremBackedTheorems,
    conditionalOnOptimalityPayloadTheorems,
    conditionalOnInformationPayloadTheorems,
    conditionalOnInformationAndCostPayloadTheorems,
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
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus
  · refine ⟨.theoremProjected, ?_, ?_⟩
    · simp [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems]
    · intro status hstatus
      simpa [TheoremBucketWitness,
        unconditionallyTheoremBackedTheorems,
        conditionalOnOptimalityPayloadTheorems,
        conditionalOnInformationPayloadTheorems,
        conditionalOnInformationAndCostPayloadTheorems] using hstatus

end OperatorKO7.Meta.ConfessionMethodOptimalityBoundary
