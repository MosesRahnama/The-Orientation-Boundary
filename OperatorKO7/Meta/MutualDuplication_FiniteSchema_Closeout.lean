import OperatorKO7.Meta.MutualDuplication_FiniteSchema_AlgorithmicSearch
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_FinalCatalog

/-!
# H3 Finite-Schema Closeout

This module closes the theorem-visible H3 surface by packaging the finite schema,
builder, builder-mapping, graph-search certificate, algorithmic search, typed
missing-edge boundary, and concrete two-rule/three-rule instances into one finite
closeout catalog.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchemaCloseout

open OperatorKO7.StepDuplicating
open OperatorKO7.MutualDuplicationFiniteSchema

/-- Finite H3 closeout rows. -/
inductive H3CloseoutRow
  | finiteSchema
  | builder
  | builderMapping
  | graphSearchCertificate
  | algorithmicEncodedSearchSpace
  | soundness
  | finiteCompleteness
  | missingSuccessorEdgeBoundary
  | twoRuleInstance
  | threeRuleInstance
  deriving DecidableEq, Repr

/-- Finite status labels for the H3 closeout rows. -/
inductive H3CloseoutRowStatus
  | theoremCovered
  | typedBoundary
  deriving DecidableEq, Repr

/-- Canonical finite H3 closeout rows. -/
def h3CloseoutRows : List H3CloseoutRow :=
  [ .finiteSchema
  , .builder
  , .builderMapping
  , .graphSearchCertificate
  , .algorithmicEncodedSearchSpace
  , .soundness
  , .finiteCompleteness
  , .missingSuccessorEdgeBoundary
  , .twoRuleInstance
  , .threeRuleInstance
  ]

/-- Status projection for the finite H3 closeout rows. -/
def h3CloseoutRowStatus : H3CloseoutRow → H3CloseoutRowStatus
  | .finiteSchema => .theoremCovered
  | .builder => .theoremCovered
  | .builderMapping => .theoremCovered
  | .graphSearchCertificate => .theoremCovered
  | .algorithmicEncodedSearchSpace => .theoremCovered
  | .soundness => .theoremCovered
  | .finiteCompleteness => .theoremCovered
  | .missingSuccessorEdgeBoundary => .typedBoundary
  | .twoRuleInstance => .theoremCovered
  | .threeRuleInstance => .theoremCovered

theorem h3CloseoutRows_length : h3CloseoutRows.length = 10 := by
  rfl

theorem h3CloseoutRows_mem_iff {row : H3CloseoutRow} :
    row ∈ h3CloseoutRows ↔
      row = .finiteSchema ∨
      row = .builder ∨
      row = .builderMapping ∨
      row = .graphSearchCertificate ∨
      row = .algorithmicEncodedSearchSpace ∨
      row = .soundness ∨
      row = .finiteCompleteness ∨
      row = .missingSuccessorEdgeBoundary ∨
      row = .twoRuleInstance ∨
      row = .threeRuleInstance := by
  cases row <;> simp [h3CloseoutRows]

theorem h3CloseoutRows_nodup : h3CloseoutRows.Nodup := by
  decide

@[simp] theorem h3CloseoutRowStatus_finiteSchema :
    h3CloseoutRowStatus .finiteSchema = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_builder :
    h3CloseoutRowStatus .builder = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_builderMapping :
    h3CloseoutRowStatus .builderMapping = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_graphSearchCertificate :
    h3CloseoutRowStatus .graphSearchCertificate = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_algorithmicEncodedSearchSpace :
    h3CloseoutRowStatus .algorithmicEncodedSearchSpace = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_soundness :
    h3CloseoutRowStatus .soundness = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_finiteCompleteness :
    h3CloseoutRowStatus .finiteCompleteness = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_missingSuccessorEdgeBoundary :
    h3CloseoutRowStatus .missingSuccessorEdgeBoundary = .typedBoundary := rfl

@[simp] theorem h3CloseoutRowStatus_twoRuleInstance :
    h3CloseoutRowStatus .twoRuleInstance = .theoremCovered := rfl

@[simp] theorem h3CloseoutRowStatus_threeRuleInstance :
    h3CloseoutRowStatus .threeRuleInstance = .theoremCovered := rfl

/-- Any theorem-visible H3 graph-search certificate projects a finite schema. -/
theorem final_catalog_projects_finite_schema
    {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k}
    (_ : FiniteCycleMutualDuplicationFinalCatalog C) :
    Nonempty (KCycleSchema k) :=
  ⟨C.toBuilder.toKCycleSystem.toKCycleSchema⟩

/-- Any executable H3 search space is itself a theorem-visible finite object. -/
theorem algorithmic_search_space_nonempty
    {k : Nat} (_S : FiniteCycleGraphSearch.EncodedSearchSpace k) :
    Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace k) :=
  ⟨_S⟩

/-- Paper-facing closeout catalog for the accepted H3 finite-search surface. -/
structure MutualDuplicationFiniteSchemaCloseoutCatalog : Prop where
  rowCount : h3CloseoutRows.length = 10
  membershipIff :
    ∀ {row : H3CloseoutRow},
      row ∈ h3CloseoutRows ↔
        row = .finiteSchema ∨
        row = .builder ∨
        row = .builderMapping ∨
        row = .graphSearchCertificate ∨
        row = .algorithmicEncodedSearchSpace ∨
        row = .soundness ∨
        row = .finiteCompleteness ∨
        row = .missingSuccessorEdgeBoundary ∨
        row = .twoRuleInstance ∨
        row = .threeRuleInstance
  noDupRows : h3CloseoutRows.Nodup
  finiteSchemaRowEvidence :
    ∀ {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k},
      FiniteCycleMutualDuplicationFinalCatalog C → Nonempty (KCycleSchema k)
  builderRowEvidence :
    ∀ {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k},
      FiniteCycleMutualDuplicationFinalCatalog C → Nonempty (FiniteCycleBuilder.Builder k)
  builderMappingRowEvidence :
    ∀ {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k},
      FiniteCycleMutualDuplicationFinalCatalog C → Nonempty (FiniteCycleBuilderMapping.SearchCertificate k)
  graphSearchCertificateRowEvidence :
    ∀ {k : Nat} {C : FiniteCycleGraphSearch.GraphSearchCertificate k},
      FiniteCycleMutualDuplicationFinalCatalog C → Nonempty (FiniteCycleGraphSearch.GraphSearchCertificate k)
  algorithmicEncodedSearchSpaceRowEvidence :
    ∀ {k : Nat} (_S : FiniteCycleGraphSearch.EncodedSearchSpace k),
      Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace k)
  soundnessRowEvidence :
    ∀ {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k}
      {W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S},
      FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W →
        FiniteCycleMutualDuplicationFinalCatalog W.toGraphSearchCertificate
  finiteCompletenessRowEvidence :
    ∀ {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k},
      (∀ i : Fin (k + 1),
        FiniteCycleGraphSearch.EncodedSearchSpace.Edge S i (FiniteCycleBuilder.advance i)) →
          ∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate S,
            FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = some W
  missingSuccessorEdgeBoundaryRowEvidence :
    ∀ {k : Nat} {S : FiniteCycleGraphSearch.EncodedSearchSpace k},
      FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle? S = none →
        Nonempty (FiniteCycleGraphSearch.EncodedSearchSpace.MissingSuccessorEdgeStatus S)
  twoRuleInstanceRowEvidence :
    FiniteCycleMutualDuplicationFinalCatalog KCycleSystem.twoRuleWitnessGraphSearchCertificate ∧
      (∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate
        FiniteCycleGraphSearch.KCycleSystem.twoRuleWitnessEncodedSearchSpace,
          FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle?
            FiniteCycleGraphSearch.KCycleSystem.twoRuleWitnessEncodedSearchSpace = some W)
  threeRuleInstanceRowEvidence :
    FiniteCycleMutualDuplicationFinalCatalog KCycleSystem.threeRuleWitnessGraphSearchCertificate ∧
      (∃ W : FiniteCycleGraphSearch.EncodedSearchSpace.CycleCandidate
        FiniteCycleGraphSearch.KCycleSystem.threeRuleWitnessEncodedSearchSpace,
          FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle?
            FiniteCycleGraphSearch.KCycleSystem.threeRuleWitnessEncodedSearchSpace = some W)

/-- Canonical closeout catalog for the accepted H3 finite-search surface. -/
theorem mutual_duplication_finite_schema_closeout_catalog :
    MutualDuplicationFiniteSchemaCloseoutCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h3CloseoutRows_length
  · intro row
    exact h3CloseoutRows_mem_iff
  · exact h3CloseoutRows_nodup
  · intro k C h
    exact final_catalog_projects_finite_schema h
  · intro k C h
    exact final_catalog_projects_builder h
  · intro k C h
    exact final_catalog_projects_search_certificate h
  · intro k C h
    exact ⟨C⟩
  · intro k S
    exact algorithmic_search_space_nonempty S
  · intro k S W hsearch
    exact finite_cycle_mutual_duplication_final_catalog W.toGraphSearchCertificate
  · intro k S hall
    exact FiniteCycleGraphSearch.EncodedSearchSpace.exists_searchCycle?_eq_some hall
  · intro k S hnone
    exact
      (FiniteCycleGraphSearch.EncodedSearchSpace.searchCycle?_eq_none_iff_missingSuccessorEdgeStatus S).1
        hnone
  · refine ⟨finite_cycle_mutual_duplication_final_catalog KCycleSystem.twoRuleWitnessGraphSearchCertificate, ?_⟩
    exact FiniteCycleGraphSearch.KCycleSystem.twoRuleWitness_searchCycle?_succeeds
  · refine ⟨finite_cycle_mutual_duplication_final_catalog KCycleSystem.threeRuleWitnessGraphSearchCertificate, ?_⟩
    exact FiniteCycleGraphSearch.KCycleSystem.threeRuleWitness_searchCycle?_succeeds

end OperatorKO7.MutualDuplicationFiniteSchemaCloseout
