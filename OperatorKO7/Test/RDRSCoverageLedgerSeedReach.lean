import OperatorKO7.Meta.RDRSCoverageLedgerSeed

/-!
# Reach test: RDRS Coverage Ledger Seed (Phase U3)

Verifies that all public names exported by `RDRSCoverageLedgerSeed` are
reachable and that key concrete row properties hold by `rfl`.
-/

open OperatorKO7.RDRSCoverageLedger
open OperatorKO7.RDRSTerminationMethodUniverse

-- Public name reachability checks
#check @CoverageLedgerClassification
#check @CoverageLedgerRow
#check @coverageClassOf
#check @leanModuleOf
#check @theoremIdOf
#check @frictionNoteOf
#check @ledgerRowOf
#check @rdrsDirectUniverseRows
#check @blockedFamilies
#check @projectionEscapeFamilies
#check @constructionEscapeFamilies
#check @notDirectFamilies
#check @needsProofFamilies
#check @blockedFamilies_length
#check @projectionEscapeFamilies_length
#check @constructionEscapeFamilies_length
#check @notDirectFamilies_length
#check @needsProofFamilies_length
#check @coverage_partition_total
#check @coverageClassOf_total
#check @rdrsDirectUniverseRows_length
#check @ledgerRow_classification_correct
#check @CoverageSeedClosed
#check @rdrs_coverage_ledger_seed_closed
#check @rdrs_coverage_ledger_seed_anchor

-- Concrete row: standardKBO is blocked
theorem reach_standardKBO_blocked :
    coverageClassOf .standardKBO = .blocked := rfl

-- Concrete row: dpSubtermCriterion is projectionEscape
theorem reach_dpSubtermCriterion_projectionEscape :
    coverageClassOf .dpSubtermCriterion = .projectionEscape := rfl

-- Concrete row: acRPO is constructionEscape
theorem reach_acRPO_constructionEscape :
    coverageClassOf .acRPO = .constructionEscape := rfl

-- Concrete row: semanticLabeling is notDirect
theorem reach_semanticLabeling_notDirect :
    coverageClassOf .semanticLabeling = .notDirect := rfl

-- Concrete row: nonlinearHigherDegreePolynomial is needsDirectUniverseProof
theorem reach_nonlinearHigherDegree_conditional :
    coverageClassOf .nonlinearHigherDegreePolynomial = .needsDirectUniverseProof := rfl

-- Concrete row: ledger row for standardKBO names the correct module
theorem reach_ledgerRow_standardKBO_module :
    (ledgerRowOf .standardKBO).leanModule = "Meta.SymbolicComparatorBarrier" := rfl

-- Concrete row: classification agrees with coverageClassOf (by rfl)
theorem reach_ledgerRow_classification_rfl :
    ∀ f : RDRSMethodFamily,
      (ledgerRowOf f).classification = coverageClassOf f :=
  ledgerRow_classification_correct

-- Seed closure certificate fields are accessible
theorem reach_coverage_seed_universeTotal :
    ∀ f : RDRSMethodFamily,
      coverageClassOf f = .blocked
        ∨ coverageClassOf f = .projectionEscape
        ∨ coverageClassOf f = .constructionEscape
        ∨ coverageClassOf f = .notDirect
        ∨ coverageClassOf f = .needsDirectUniverseProof :=
  rdrs_coverage_ledger_seed_closed.universeCoverage

theorem reach_coverage_seed_blocked21 :
    blockedFamilies.length = 21 :=
  rdrs_coverage_ledger_seed_closed.blockedCount

theorem reach_coverage_seed_partition76 :
    blockedFamilies.length + projectionEscapeFamilies.length +
      constructionEscapeFamilies.length + notDirectFamilies.length +
        needsProofFamilies.length = 76 :=
  rdrs_coverage_ledger_seed_closed.partitionTotal

theorem reach_coverage_seed_rows76 :
    rdrsDirectUniverseRows.length = 76 :=
  rdrs_coverage_ledger_seed_closed.rowCountCorrect
