import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.Builders

/-!
# Semantic-profile reconstruction no-go

Two transactions can have the same partial morphism and event trace while
carrying different exact semantic construction data.  Their derived semantic
profiles then differ.  Consequently no extractor from only morphism and trace
can recover every semantic profile, even on one fixed finite ARS.

## Audit slots

Relation: the same two-state chain relation in both fixtures.
Closure: the same local normalization witness in both fixtures.
Trust: kernel-only finite computation.
Scope: impossibility of morphism-and-trace-only semantic reconstruction.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace IntegratedBuilders

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- The same orientation semantics with two certificate alternatives. -/
def orientationSemanticData_twoAlternatives :
    SemanticConstructionData chainARS_fixture Unit Unit where
  scope := orientationScope
  defects := ∅
  closes := orientationCloses
  coverable := orientationCoverable
  actionCost := fun _ => 1
  witnessAdequacy := baseAdequacy
  fixedLengthAlternatives := 2
  prefixCodeAlternatives := 2

/-- Same morphism and trace as the orientation fixture, but distinct semantic
certificate data. -/
def orientationConstruction_twoAlternatives_fixture :
    BoundaryConstructionData chainARS_fixture chainARS_fixture Unit Unit where
  morphism := PartialLicensedReductionMorphism.id chainARS_fixture
  semantics := orientationSemanticData_twoAlternatives
  semantic_relation_iff := fun _ _ => Iff.rfl
  eventTrace := orientationConstruction.eventTrace

def orientationTransaction_twoAlternatives_fixture :
    IntegratedBoundaryTransaction chainARS_fixture chainARS_fixture Unit Unit :=
  IntegratedBoundaryTransaction.build orientationConstruction_twoAlternatives_fixture

theorem orientation_twoAlternatives_same_morphism_fixture :
    orientationTransaction_twoAlternatives_fixture.morphism =
      orientationTransaction_fixture.morphism :=
  rfl

theorem orientation_twoAlternatives_same_trace_fixture :
    orientationTransaction_twoAlternatives_fixture.eventTrace =
      orientationTransaction_fixture.eventTrace :=
  rfl

theorem orientation_twoAlternatives_fixedLengthFloor_eq_one :
    (orientationTransaction_twoAlternatives_fixture.semanticProfile
      ).fixedLengthCertificateFloor = 1 := by
  change Nat.clog 2 2 = 1
  norm_num [Nat.clog]

theorem orientation_semanticProfiles_differ_fixture :
    orientationTransaction_twoAlternatives_fixture.semanticProfile ≠
      orientationTransaction_fixture.semanticProfile := by
  intro heq
  have hfield := congrArg SemanticProfile.fixedLengthCertificateFloor heq
  have htwo := orientation_twoAlternatives_fixedLengthFloor_eq_one
  have hone :
      (orientationTransaction_fixture.semanticProfile
        ).fixedLengthCertificateFloor = 0 := by
    rw [orientation_transaction_profile_exact]
    rfl
  rw [htwo, hone] at hfield
  omega

/-- Non-vacuity bundle: morphism and trace agree, while the computed semantic
profiles do not. -/
theorem same_morphism_trace_different_profile_fixture :
    orientationTransaction_twoAlternatives_fixture.morphism =
        orientationTransaction_fixture.morphism ∧
      orientationTransaction_twoAlternatives_fixture.eventTrace =
        orientationTransaction_fixture.eventTrace ∧
      orientationTransaction_twoAlternatives_fixture.semanticProfile ≠
        orientationTransaction_fixture.semanticProfile :=
  ⟨orientation_twoAlternatives_same_morphism_fixture,
    orientation_twoAlternatives_same_trace_fixture,
    orientation_semanticProfiles_differ_fixture⟩

/-- No function of only the morphism and trace recovers the semantic profile of
every transaction, already for the fixed chain carrier and `Unit` semantics. -/
theorem no_morphism_trace_only_semanticProfile_fixture :
    ¬ (∃ extract :
        PartialLicensedReductionMorphism chainARS_fixture chainARS_fixture ->
          EventTrace -> SemanticProfile,
      ∀ transaction :
          IntegratedBoundaryTransaction chainARS_fixture chainARS_fixture Unit Unit,
        extract transaction.morphism transaction.eventTrace =
          transaction.semanticProfile) := by
  rintro ⟨extract, hextract⟩
  have horiginal := hextract orientationTransaction_fixture
  have htwo := hextract orientationTransaction_twoAlternatives_fixture
  have hprofiles :
      orientationTransaction_twoAlternatives_fixture.semanticProfile =
        orientationTransaction_fixture.semanticProfile := by
    calc
      orientationTransaction_twoAlternatives_fixture.semanticProfile =
          extract orientationTransaction_twoAlternatives_fixture.morphism
            orientationTransaction_twoAlternatives_fixture.eventTrace :=
        htwo.symm
      _ = extract orientationTransaction_fixture.morphism
            orientationTransaction_fixture.eventTrace := by
        rw [orientation_twoAlternatives_same_morphism_fixture,
          orientation_twoAlternatives_same_trace_fixture]
      _ = orientationTransaction_fixture.semanticProfile := horiginal
  exact orientation_semanticProfiles_differ_fixture hprofiles

#check orientationTransaction_twoAlternatives_fixture
#check same_morphism_trace_different_profile_fixture
#check no_morphism_trace_only_semanticProfile_fixture
#print axioms orientation_twoAlternatives_same_morphism_fixture
#print axioms orientation_twoAlternatives_same_trace_fixture
#print axioms orientation_twoAlternatives_fixedLengthFloor_eq_one
#print axioms orientation_semanticProfiles_differ_fixture
#print axioms same_morphism_trace_different_profile_fixture
#print axioms no_morphism_trace_only_semanticProfile_fixture

end IntegratedBuilders
end OperatorKO7.Meta.LicensedBoundaryCalculus
