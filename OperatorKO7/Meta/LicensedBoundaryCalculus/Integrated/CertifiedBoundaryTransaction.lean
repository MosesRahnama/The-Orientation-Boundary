import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7SemanticAdequacy
import OperatorKO7.Meta.LicensedBoundaryCalculus.Execution.LedgerSoundness
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralProfile

/-!
# Integrated boundary transactions with semantic adequacy

The construction data contain a partial morphism, semantic data, a semantic
adequacy certificate, and one typed raw-edge input. The execution result,
trace, ledger, structural profile, and semantic profile are computed from
those fields. The caller still supplies the costs and alternative counts inside
`SemanticConstructionData`; trace and ledger values are not separate inputs.

## Audit slots

Relation: exact admitted relation certified by semantic adequacy.
Closure: local semantic normalization and one certified edge execution.
Trust: kernel-only finite profile and ledger computation.
Scope: one finite certified semantic model and one raw edge execution.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v d a

/-- Minimal input for a certified integrated transaction. -/
structure CertifiedBoundaryConstructionData
    (A : ARS.{u}) (B : ARS.{v}) [Fintype A.Carrier] [Fintype B.Carrier]
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  morphism : PartialLicensedReductionMorphism A B
  semantics : SemanticConstructionData A Defect Action
  semanticAdequacy : SemanticAdequacyCertificate morphism semantics
  executionInput : BoundaryExecutionInput morphism

/-- Wrapper around certified construction data. Its quantitative profile may
depend on the caller-supplied inputs inside `SemanticConstructionData`. -/
structure CertifiedIntegratedBoundaryTransaction
    (A : ARS.{u}) (B : ARS.{v}) [Fintype A.Carrier] [Fintype B.Carrier]
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  construction : CertifiedBoundaryConstructionData A B Defect Action

namespace CertifiedIntegratedBoundaryTransaction

noncomputable section

variable {A : ARS.{u}} {B : ARS.{v}}
variable [Fintype A.Carrier] [Fintype B.Carrier]
variable {Defect : Type d} {Action : Type a}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Convenience constructor for `CertifiedIntegratedBoundaryTransaction`. The
structure constructor remains public as well. -/
def build (data : CertifiedBoundaryConstructionData A B Defect Action) :
    CertifiedIntegratedBoundaryTransaction A B Defect Action :=
  ⟨data⟩

def morphism
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    PartialLicensedReductionMorphism A B :=
  transaction.construction.morphism

def semanticData
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    SemanticConstructionData A Defect Action :=
  transaction.construction.semantics

def executionInput
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    BoundaryExecutionInput transaction.morphism :=
  transaction.construction.executionInput

def executionResult
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    BoundaryExecutionResult transaction.morphism transaction.executionInput :=
  execute transaction.morphism transaction.executionInput

def eventTrace
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    EventTrace :=
  transaction.executionResult.trace

noncomputable def ledger
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    EventLedger :=
  transaction.executionResult.ledger

noncomputable def structuralProfile
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    PartialLicensedReductionMorphism.StructuralProfile :=
  PartialLicensedReductionMorphism.structuralProfile transaction.morphism

noncomputable def semanticProfile
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    SemanticProfile :=
  OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile
    transaction.semanticData

/-- The semantic relation is exactly the admitted relation. -/
theorem semantic_relation_iff
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action)
    (x y : A.Carrier) :
    transaction.semanticData.scope.relation x y ↔
      transaction.morphism.admitted x y :=
  transaction.construction.semanticAdequacy.relationExact x y

/-- Projection of the full semantic adequacy evidence. -/
def semanticAdequacy
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :=
  transaction.construction.semanticAdequacy

/-- Every transaction built from this wrapper satisfies `TraceAdequacy`. -/
theorem execution_adequate
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    TraceAdequacy transaction.morphism transaction.executionInput
      transaction.executionResult :=
  execute_trace_adequate transaction.morphism transaction.executionInput

/-- The transaction ledger is computed from its trace. -/
theorem ledger_eq_countEvents
    (transaction : CertifiedIntegratedBoundaryTransaction A B Defect Action) :
    transaction.ledger = countEvents transaction.eventTrace :=
  rfl

/-! ## Concrete KO7 fixture -/

open KO7DistinctionAdapter
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

/-- The rejected diagonal branch as a certified execution input. -/
def ko7EdgeRefusalInput_fixture : BoundaryExecutionInput licenseMorphism where
  source := .source
  proposedTarget := .diffVerdict
  rawEdge := LocalRaw.diff
  stateEvidence := .proved ⟨trivial, trivial⟩
  edgeEvidence := .refuted (by intro h; cases h)

def ko7CertifiedConstruction_fixture :
    CertifiedBoundaryConstructionData rawARS licensedARS
      CanonicalDefect RepairAction where
  morphism := licenseMorphism
  semantics := licensedData
  semanticAdequacy := ko7LicensedSemanticAdequacy
  executionInput := ko7EdgeRefusalInput_fixture

def ko7CertifiedTransaction_fixture :
    CertifiedIntegratedBoundaryTransaction rawARS licensedARS
      CanonicalDefect RepairAction :=
  build ko7CertifiedConstruction_fixture

theorem ko7_certified_transaction_nonvacuous_fixture :
    ko7CertifiedTransaction_fixture.executionResult.decision = .refuseEdge ∧
      ko7CertifiedTransaction_fixture.ledger .edgeRefusal = 1 ∧
      ko7CertifiedTransaction_fixture.semanticProfile = licensedExactProfile := by
  refine ⟨rfl, ?_, ?_⟩
  · change
      countEvents
        [⟨.domainCheck⟩, ⟨.domainCheck⟩,
          ⟨.edgeCheck⟩, ⟨.edgeRefusal⟩] .edgeRefusal = 1
    simp [countEvents, singletonEventLedger]
  · change
      OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile licensedData =
        licensedExactProfile
    exact licensed_semanticProfile_exact

#check @build
#check @semantic_relation_iff
#check @semanticAdequacy
#check @execution_adequate
#check @ledger_eq_countEvents
#check ko7_certified_transaction_nonvacuous_fixture
#print axioms semantic_relation_iff
#print axioms semanticAdequacy
#print axioms execution_adequate
#print axioms ledger_eq_countEvents
#print axioms ko7_certified_transaction_nonvacuous_fixture

end
end CertifiedIntegratedBoundaryTransaction
end OperatorKO7.Meta.LicensedBoundaryCalculus
