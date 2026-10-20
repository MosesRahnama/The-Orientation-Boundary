import OperatorKO7.Meta.DPSubtermCriterionExact
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# RDRS Dependency-Pair Processor Classification

Finite T5 ledger for DP processors against RDRS.

The classification separates processors that close the schema by projection,
processors that inherit the need for a duplication-tolerant base order, neutral
processors that do not close the cycle alone, and the usable-rules minimality
boundary.
-/

namespace OperatorKO7.RDRSDPProcessorClassification

open OperatorKO7.RDRSTerminationMethodUniverse

/-- Finite DP-processor row set for the T5 sprint. -/
inductive DPProcessorFamily
  | subtermCriterion
  | argumentFiltering
  | typeIntroduction
  | manySortedDP
  | orderSortedDP
  | csdpFrozenPosition
  | sizeChangeTermination
  | reductionPairProcessor
  | polynomialDP
  | reductionTriples
  | narrowing
  | instantiation
  | forwardInstantiation
  | rewriting
  | formativeRules
  | usableRulesMinimality
  deriving DecidableEq, Repr

/-- Classification styles used by the T5 ledger. -/
inductive DPProcessorStyle
  | projectionStyle
  | inheritanceStyle
  | neutral
  | usableRulesBoundary
  deriving DecidableEq, Repr

/-- Projection mechanisms that erase or project away the duplicated `s` slot. -/
inductive ProjectionMechanism
  | counterSubterm
  | argumentFilteringCollapse
  | typedProjection
  | sortedProjection
  | frozenPosition
  | sizeChangeThread
  deriving DecidableEq, Repr

/-- Imported-order obligation for inheritance-style DP processors. -/
inductive BaseOrderRequirement
  | duplicationTolerantBaseOrder
  deriving DecidableEq, Repr

/-- Pairing that may be supplied to a neutral or usable-rules row. -/
inductive ProcessorPairing
  | none
  | withProjection
  | withImportedOrder
  deriving DecidableEq, Repr

/-- Exact finite inventory for T5. -/
def allDPProcessorFamilies : List DPProcessorFamily :=
  [ .subtermCriterion
  , .argumentFiltering
  , .typeIntroduction
  , .manySortedDP
  , .orderSortedDP
  , .csdpFrozenPosition
  , .sizeChangeTermination
  , .reductionPairProcessor
  , .polynomialDP
  , .reductionTriples
  , .narrowing
  , .instantiation
  , .forwardInstantiation
  , .rewriting
  , .formativeRules
  , .usableRulesMinimality
  ]

/-- Projection-style rows. -/
def projectionStyleProcessors : List DPProcessorFamily :=
  [ .subtermCriterion
  , .argumentFiltering
  , .typeIntroduction
  , .manySortedDP
  , .orderSortedDP
  , .csdpFrozenPosition
  , .sizeChangeTermination
  ]

/-- Inheritance-style rows. -/
def inheritanceStyleProcessors : List DPProcessorFamily :=
  [ .reductionPairProcessor
  , .polynomialDP
  , .reductionTriples
  ]

/-- Neutral rows. -/
def neutralProcessors : List DPProcessorFamily :=
  [ .narrowing
  , .instantiation
  , .forwardInstantiation
  , .rewriting
  , .formativeRules
  ]

theorem allDPProcessorFamilies_nodup : allDPProcessorFamilies.Nodup := by
  decide

theorem allDPProcessorFamilies_length : allDPProcessorFamilies.length = 16 := by
  rfl

theorem allDPProcessorFamilies_complete
    (processor : DPProcessorFamily) :
    processor ∈ allDPProcessorFamilies := by
  cases processor <;> decide

theorem projectionStyleProcessors_nodup : projectionStyleProcessors.Nodup := by
  decide

theorem projectionStyleProcessors_length : projectionStyleProcessors.length = 7 := by
  rfl

theorem inheritanceStyleProcessors_nodup :
    inheritanceStyleProcessors.Nodup := by
  decide

theorem inheritanceStyleProcessors_length :
    inheritanceStyleProcessors.length = 3 := by
  rfl

theorem neutralProcessors_nodup : neutralProcessors.Nodup := by
  decide

theorem neutralProcessors_length : neutralProcessors.length = 5 := by
  rfl

/-- Style assignment for each DP-processor row. -/
def processorStyle : DPProcessorFamily -> DPProcessorStyle
  | .subtermCriterion => .projectionStyle
  | .argumentFiltering => .projectionStyle
  | .typeIntroduction => .projectionStyle
  | .manySortedDP => .projectionStyle
  | .orderSortedDP => .projectionStyle
  | .csdpFrozenPosition => .projectionStyle
  | .sizeChangeTermination => .projectionStyle
  | .reductionPairProcessor => .inheritanceStyle
  | .polynomialDP => .inheritanceStyle
  | .reductionTriples => .inheritanceStyle
  | .narrowing => .neutral
  | .instantiation => .neutral
  | .forwardInstantiation => .neutral
  | .rewriting => .neutral
  | .formativeRules => .neutral
  | .usableRulesMinimality => .usableRulesBoundary

/-- Projection mechanism, when the processor closes RDRS by position erasure or projection. -/
def projectionMechanism? : DPProcessorFamily -> Option ProjectionMechanism
  | .subtermCriterion => some .counterSubterm
  | .argumentFiltering => some .argumentFilteringCollapse
  | .typeIntroduction => some .typedProjection
  | .manySortedDP => some .sortedProjection
  | .orderSortedDP => some .sortedProjection
  | .csdpFrozenPosition => some .frozenPosition
  | .sizeChangeTermination => some .sizeChangeThread
  | _ => none

/-- Inheritance obligation, when a processor must import a base order. -/
def baseOrderRequirement? : DPProcessorFamily -> Option BaseOrderRequirement
  | .reductionPairProcessor => some .duplicationTolerantBaseOrder
  | .polynomialDP => some .duplicationTolerantBaseOrder
  | .reductionTriples => some .duplicationTolerantBaseOrder
  | _ => none

/-- Neutral rows do not close RDRS without projection or an imported order. -/
def neutralPairingNeed? : DPProcessorFamily -> Option ProcessorPairing
  | .narrowing => some .withProjection
  | .instantiation => some .withProjection
  | .forwardInstantiation => some .withProjection
  | .rewriting => some .withProjection
  | .formativeRules => some .withProjection
  | _ => none

/-- A concrete projection profile: duplicated payload removed, counter descent kept. -/
structure ProjectionProfile where
  mechanism : ProjectionMechanism
  erasesOrProjectsDuplicatedArgument : Bool
  keepsCounterDescent : Bool

/-- Profile extracted from a projection-style processor. -/
def projectionProfile? (processor : DPProcessorFamily) : Option ProjectionProfile :=
  match projectionMechanism? processor with
  | some mechanism =>
      some {
        mechanism := mechanism
        erasesOrProjectsDuplicatedArgument := true
        keepsCounterDescent := true
      }
  | none => none

/-- Semantic content of closing RDRS by projection. -/
def ClosesRDRSByProjection (processor : DPProcessorFamily) : Prop :=
  ∃ profile : ProjectionProfile,
    projectionProfile? processor = some profile
      /\ profile.erasesOrProjectsDuplicatedArgument = true
      /\ profile.keepsCounterDescent = true

/-- Semantic content of inheriting the base-order duplication obligation. -/
def RequiresDuplicationTolerantBaseOrder
    (processor : DPProcessorFamily) : Prop :=
  baseOrderRequirement? processor = some .duplicationTolerantBaseOrder

/-- Semantic content of a neutral processor row. -/
def NeutralUnlessPaired (processor : DPProcessorFamily) : Prop :=
  neutralPairingNeed? processor = some .withProjection

theorem projectionStyle_iff_closes_by_projection
    (processor : DPProcessorFamily) :
    processorStyle processor = .projectionStyle <->
      ClosesRDRSByProjection processor := by
  cases processor <;>
    simp [processorStyle, ClosesRDRSByProjection, projectionProfile?,
      projectionMechanism?]

theorem inheritanceStyle_iff_requires_base_order
    (processor : DPProcessorFamily) :
    processorStyle processor = .inheritanceStyle <->
      RequiresDuplicationTolerantBaseOrder processor := by
  cases processor <;>
    simp [processorStyle, RequiresDuplicationTolerantBaseOrder,
      baseOrderRequirement?]

theorem neutral_iff_neutral_unless_paired
    (processor : DPProcessorFamily) :
    processorStyle processor = .neutral <->
      NeutralUnlessPaired processor := by
  cases processor <;>
    simp [processorStyle, NeutralUnlessPaired, neutralPairingNeed?]

theorem projection_rows_are_exact
    (processor : DPProcessorFamily) :
    processor ∈ projectionStyleProcessors ↔
      processorStyle processor = .projectionStyle := by
  cases processor <;> decide

theorem inheritance_rows_are_exact
    (processor : DPProcessorFamily) :
    processor ∈ inheritanceStyleProcessors ↔
      processorStyle processor = .inheritanceStyle := by
  cases processor <;> decide

theorem neutral_rows_are_exact
    (processor : DPProcessorFamily) :
    processor ∈ neutralProcessors ↔
      processorStyle processor = .neutral := by
  cases processor <;> decide

/-- Stronger local support attached to each projection-style row. -/
def ProjectionSupport : DPProcessorFamily -> Prop
  | .subtermCriterion =>
      WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev
  | .argumentFiltering =>
      ∀ x y : OperatorKO7.Trace,
        OperatorKO7.ConfessionMethodFamily.schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
          (OperatorKO7.Trace.app x y) = 0
  | .sizeChangeTermination =>
      OperatorKO7.ConfessionMethodFamily.sctSatisfied
        OperatorKO7.ConfessionMethodFamily.schemaRecCallGraph
  | processor => ClosesRDRSByProjection processor

theorem projection_support_holds
    (processor : DPProcessorFamily)
    (h : processorStyle processor = .projectionStyle) :
    ProjectionSupport processor := by
  cases processor <;>
    simp [processorStyle, ProjectionSupport, ClosesRDRSByProjection,
      projectionProfile?, projectionMechanism?] at h ⊢
  · exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev
  · exact OperatorKO7.ConfessionMethodFamily.argumentFilteringWitness_forgets_wrapper_payload
  · exact OperatorKO7.ConfessionMethodFamily.schema_sct_satisfied

/-- Atlas status induced by the T5 classification. -/
def processorStatus : DPProcessorFamily -> RDRSMethodStatus
  | .subtermCriterion => .conditional_escape
  | .argumentFiltering => .conditional_escape
  | .typeIntroduction => .conditional_escape
  | .manySortedDP => .conditional_escape
  | .orderSortedDP => .conditional_escape
  | .csdpFrozenPosition => .conditional_escape
  | .sizeChangeTermination => .conditional_escape
  | .reductionPairProcessor => .import_dependent
  | .polynomialDP => .import_dependent
  | .reductionTriples => .import_dependent
  | .narrowing => .not_applicable
  | .instantiation => .not_applicable
  | .forwardInstantiation => .not_applicable
  | .rewriting => .not_applicable
  | .formativeRules => .not_applicable
  | .usableRulesMinimality => .conditional_barrier

/-- Atlas row indexed by each processor row. -/
def atlasFamily? : DPProcessorFamily -> Option RDRSMethodFamily
  | .subtermCriterion => some .dpSubtermCriterion
  | .argumentFiltering => some .dpArgumentFiltering
  | .typeIntroduction => some .typeIntroduction
  | .manySortedDP => some .manySortedPersistence
  | .orderSortedDP => some .orderSortedDP
  | .csdpFrozenPosition => some .contextSensitiveDP
  | .sizeChangeTermination => some .sizeChangeTerminationEscape
  | .reductionPairProcessor => some .dpReductionPairProcessor
  | .polynomialDP => some .dpReductionPairProcessor
  | .reductionTriples => some .dpReductionTriples
  | .narrowing => some .dpNeutralProcessors
  | .instantiation => some .dpNeutralProcessors
  | .forwardInstantiation => some .dpNeutralProcessors
  | .rewriting => some .dpNeutralProcessors
  | .formativeRules => some .formativeRules
  | .usableRulesMinimality => some .usableRulesMinimality

/-- Atlas status projected from the global RDRS method-universe row. -/
def atlasStatus? (processor : DPProcessorFamily) : Option RDRSMethodStatus :=
  match atlasFamily? processor with
  | some family => some (statusOf family)
  | none => none

theorem atlasStatus_matches_processorStatus
    (processor : DPProcessorFamily) :
    atlasStatus? processor = some (processorStatus processor) := by
  cases processor <;>
    rfl

/-- Usable-rules minimality can erase the duplicating rule only when paired with projection. -/
def eliminatesDuplicatingRule
    (processor : DPProcessorFamily) (pairing : ProcessorPairing) : Bool :=
  match processor, pairing with
  | .usableRulesMinimality, .withProjection => true
  | .usableRulesMinimality, _ => false
  | processor, .withProjection =>
      match projectionMechanism? processor with
      | some _ => true
      | none => false
  | _, _ => false

theorem usableRulesMinimality_non_elimination_without_projection
    (pairing : ProcessorPairing)
    (h : pairing ≠ .withProjection) :
    eliminatesDuplicatingRule .usableRulesMinimality pairing = false := by
  cases pairing <;> simp [eliminatesDuplicatingRule] at h ⊢

theorem usableRulesMinimality_projection_pairing_eliminates :
    eliminatesDuplicatingRule .usableRulesMinimality .withProjection = true := by
  rfl

theorem neutral_rows_do_not_eliminate_without_pairing
    (processor : DPProcessorFamily)
    (h : processorStyle processor = .neutral) :
    eliminatesDuplicatingRule processor .none = false
      /\ NeutralUnlessPaired processor := by
  have hn := (neutral_iff_neutral_unless_paired processor).1 h
  cases processor <;>
    simp [processorStyle, NeutralUnlessPaired, neutralPairingNeed?,
      eliminatesDuplicatingRule] at h hn ⊢

/-- Final closure certificate for T5. -/
structure RDRSDPProcessorClassificationClosed where
  complete : ∀ processor : DPProcessorFamily, processor ∈ allDPProcessorFamilies
  nodup : allDPProcessorFamilies.Nodup
  projectionExact :
    ∀ processor : DPProcessorFamily,
      processor ∈ projectionStyleProcessors ↔
        ClosesRDRSByProjection processor
  inheritanceExact :
    ∀ processor : DPProcessorFamily,
      processor ∈ inheritanceStyleProcessors ↔
        RequiresDuplicationTolerantBaseOrder processor
  neutralExact :
    ∀ processor : DPProcessorFamily,
      processor ∈ neutralProcessors ↔
        NeutralUnlessPaired processor
  atlasStatuses :
    ∀ processor : DPProcessorFamily,
      atlasStatus? processor = some (processorStatus processor)
  usableRulesBoundary :
    (∀ pairing : ProcessorPairing,
      pairing ≠ .withProjection ->
        eliminatesDuplicatingRule .usableRulesMinimality pairing = false)
      /\ eliminatesDuplicatingRule .usableRulesMinimality .withProjection = true

/-- T5 acceptance marker: the DP processor classification sprint is closed. -/
theorem rdrs_dp_processor_classification_closed :
    RDRSDPProcessorClassificationClosed where
  complete := allDPProcessorFamilies_complete
  nodup := allDPProcessorFamilies_nodup
  projectionExact := by
    intro processor
    exact (projection_rows_are_exact processor).trans
      (projectionStyle_iff_closes_by_projection processor)
  inheritanceExact := by
    intro processor
    exact (inheritance_rows_are_exact processor).trans
      (inheritanceStyle_iff_requires_base_order processor)
  neutralExact := by
    intro processor
    exact (neutral_rows_are_exact processor).trans
      (neutral_iff_neutral_unless_paired processor)
  atlasStatuses := atlasStatus_matches_processorStatus
  usableRulesBoundary :=
    ⟨usableRulesMinimality_non_elimination_without_projection,
      usableRulesMinimality_projection_pairing_eliminates⟩

end OperatorKO7.RDRSDPProcessorClassification
