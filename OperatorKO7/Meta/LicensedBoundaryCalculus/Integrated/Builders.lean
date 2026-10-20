import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.QuantitativeLaws
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7ExactProfile

/-!
# Canonical integrated builders

This module supplies non-vacuous orientation and distinction transactions.
Both pass through the construction-data builder, so their profiles and ledgers
are computed projections.

## Audit slots

Relation: the two-state orientation chain and the KO7 local distinction cone.
Closure: root-local reflexive-transitive semantic scopes and finite traces.
Trust: kernel-only.
Scope: canonical finite inhabitants, not claims about every application domain.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace IntegratedBuilders

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-! ## Orientation-chain inhabitant -/

def orientationScope : SemanticScope chainARS_fixture :=
  SemanticScope.raw chainARS_fixture ChainNode.source .local .base 0

instance orientationChain_fintype : Fintype chainARS_fixture.Carrier := by
  change Fintype ChainNode
  infer_instance

def orientationCloses (_ : Unit) : Finset Unit := ∅

theorem orientationCoverable :
    IsRepairCover (∅ : Finset Unit) orientationCloses Finset.univ := by
  intro defect hdefect
  simp at hdefect

def orientationSemanticData :
    SemanticConstructionData chainARS_fixture Unit Unit where
  scope := orientationScope
  defects := ∅
  closes := orientationCloses
  coverable := orientationCoverable
  actionCost := fun _ => 1
  witnessAdequacy := baseAdequacy
  fixedLengthAlternatives := 1
  prefixCodeAlternatives := 1

/-- A concrete oriented one-step execution. -/
def orientationConstruction :
    BoundaryConstructionData chainARS_fixture chainARS_fixture Unit Unit where
  morphism := PartialLicensedReductionMorphism.id chainARS_fixture
  semantics := orientationSemanticData
  semantic_relation_iff := fun _ _ => Iff.rfl
  eventTrace := [⟨.domainCheck⟩, ⟨.edgeCheck⟩, ⟨.replayStep⟩]

def orientationTransaction_fixture :
    IntegratedBoundaryTransaction chainARS_fixture chainARS_fixture Unit Unit :=
  IntegratedBoundaryTransaction.build orientationConstruction

def orientationExactProfile : SemanticProfile where
  terminalMultiplicity := 1
  terminalHartley := some 0
  criticalPairDefect := 0
  minimumRepairCover := 0
  minimumRepairCost := 0
  witnessRank := 0
  fixedLengthCertificateFloor := 0
  prefixCodeCertificateFloor := 0

theorem orientationConfluentAt_source :
    ConfluentAt orientationScope.relation orientationScope.source := by
  apply confluentAt_of_unique_normalForms
    SemanticScope.chain_normalizing_fixture
  intro n₁ n₂ _ hn₁ _ hn₂
  cases n₁ <;> cases n₂
  · rfl
  · exact False.elim (hn₁ _ ChainStep.descend)
  · exact False.elim (hn₂ _ ChainStep.descend)
  · rfl

theorem orientation_terminalMultiplicity_eq_one :
    SemanticScope.terminalMultiplicity orientationScope = 1 := by
  change terminalMultiplicity orientationScope.relation orientationScope.source = 1
  exact terminalMultiplicity_eq_one_of_confluentAt
    SemanticScope.chain_normalizing_fixture orientationConfluentAt_source

theorem orientationSemanticData_profile_exact :
    semanticProfile orientationSemanticData = orientationExactProfile := by
  apply SemanticProfile.ext
  · exact orientation_terminalMultiplicity_eq_one
  · change SemanticScope.terminalHartley? orientationScope = some 0
    rw [SemanticScope.terminalHartley?_eq_some_of_normalizingAt
      orientationScope SemanticScope.chain_normalizing_fixture]
    congr 1
    rw [terminalHartleyEntropy]
    change Real.logb 2 (SemanticScope.terminalMultiplicity orientationScope) = 0
    rw [orientation_terminalMultiplicity_eq_one]
    simp [Real.logb]
  · rfl
  · change repairCoverNumber ∅ orientationCloses orientationCoverable = 0
    exact repairCoverNumber_empty_eq_zero orientationCloses orientationCoverable
  · change minimumRepairCoverCost ∅ orientationCloses
      (fun _ : Unit => 1) orientationCoverable = 0
    exact minimumRepairCoverCost_empty_eq_zero
      orientationCloses (fun _ : Unit => 1) orientationCoverable
  · change witnessRank baseAdequacy = 0
    exact baseAdequacy_rank_zero
  · change Nat.clog 2 1 = 0
    norm_num [Nat.clog]
  · change Nat.clog 2 1 = 0
    norm_num [Nat.clog]

theorem orientation_transaction_profile_exact :
    orientationTransaction_fixture.semanticProfile = orientationExactProfile :=
  orientationSemanticData_profile_exact

theorem orientation_transaction_ledger_fixture :
    orientationTransaction_fixture.ledger .domainCheck = 1 ∧
      orientationTransaction_fixture.ledger .edgeCheck = 1 ∧
      orientationTransaction_fixture.ledger .replayStep = 1 := by
  change
    countEvents [⟨.domainCheck⟩, ⟨.edgeCheck⟩, ⟨.replayStep⟩]
          .domainCheck = 1 ∧
      countEvents [⟨.domainCheck⟩, ⟨.edgeCheck⟩, ⟨.replayStep⟩]
          .edgeCheck = 1 ∧
      countEvents [⟨.domainCheck⟩, ⟨.edgeCheck⟩, ⟨.replayStep⟩]
          .replayStep = 1
  simp [countEvents, singletonEventLedger]

/-! ## KO7 distinction inhabitant -/

open KO7DistinctionAdapter

def distinctionConstruction :
    BoundaryConstructionData rawARS licensedARS CanonicalDefect RepairAction where
  morphism := licenseMorphism
  semantics := licensedData
  semantic_relation_iff := fun _ _ => Iff.rfl
  eventTrace :=
    [⟨.edgeCheck⟩, ⟨.edgeRefusal⟩, ⟨.witnessGradeUse⟩,
      ⟨.certificateBit⟩]

def distinctionTransaction_fixture :
    IntegratedBoundaryTransaction rawARS licensedARS CanonicalDefect RepairAction :=
  IntegratedBoundaryTransaction.build distinctionConstruction

theorem distinction_transaction_morphism_exact :
    distinctionTransaction_fixture.morphism = licenseMorphism :=
  rfl

theorem distinction_transaction_profile_exact :
    distinctionTransaction_fixture.semanticProfile = licensedExactProfile :=
  licensed_semanticProfile_exact

theorem distinction_transaction_ledger_fixture :
    distinctionTransaction_fixture.ledger .edgeRefusal = 1 ∧
      distinctionTransaction_fixture.ledger .witnessGradeUse = 1 ∧
      distinctionTransaction_fixture.ledger .certificateBit = 1 := by
  change
    countEvents
          [⟨.edgeCheck⟩, ⟨.edgeRefusal⟩, ⟨.witnessGradeUse⟩,
            ⟨.certificateBit⟩] .edgeRefusal = 1 ∧
      countEvents
          [⟨.edgeCheck⟩, ⟨.edgeRefusal⟩, ⟨.witnessGradeUse⟩,
            ⟨.certificateBit⟩] .witnessGradeUse = 1 ∧
      countEvents
          [⟨.edgeCheck⟩, ⟨.edgeRefusal⟩, ⟨.witnessGradeUse⟩,
            ⟨.certificateBit⟩] .certificateBit = 1
  simp [countEvents, singletonEventLedger]

/-- Both canonical faces inhabit the derived integrated API. -/
theorem integrated_orientation_distinction_nonvacuous :
    orientationTransaction_fixture.eventTrace.length = 3 ∧
      distinctionTransaction_fixture.eventTrace.length = 4 ∧
      distinctionTransaction_fixture.semanticProfile = licensedExactProfile := by
  exact ⟨rfl, rfl, distinction_transaction_profile_exact⟩

#check orientationTransaction_fixture
#check distinctionTransaction_fixture
#check orientation_transaction_profile_exact
#check distinction_transaction_profile_exact
#check integrated_orientation_distinction_nonvacuous
#print axioms orientationSemanticData_profile_exact
#print axioms orientation_transaction_profile_exact
#print axioms orientation_transaction_ledger_fixture
#print axioms distinction_transaction_profile_exact
#print axioms distinction_transaction_ledger_fixture
#print axioms integrated_orientation_distinction_nonvacuous

end IntegratedBuilders
end OperatorKO7.Meta.LicensedBoundaryCalculus
