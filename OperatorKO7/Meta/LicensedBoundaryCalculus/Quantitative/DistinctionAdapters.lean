import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticProfile
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7CriticalPairDefect
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank

/-!
# Finite adapters for the KO7 distinction cone

The three-node local cone is embedded into the LBC abstract-reduction and
partial-morphism interfaces without changing either relation.  Raw and
licensed semantic construction data are then built from the existing defect,
repair, witness, and terminal-support objects.

## Formal scope

Relation: `LocalRaw` and `LocalLicensed` at `eqW(void,void)`.
Closure: root-local reflexive-transitive reachability on the finite cone.
Trust: kernel-only; all adapter equalities are definitional.
Scope: the local three-node cone, not global KO7 context closure.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace KO7DistinctionAdapter

open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

abbrev CanonicalDefect :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.CanonicalDefect
abbrev RepairAction :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.RepairAction

/-- Raw local equality-witness cone with explicit audit coordinates. -/
def rawARS : ARS where
  Carrier := EqWBreakerNode
  step := LocalRaw
  scope :=
    { location := .root
      closure := .reflexiveTransitive
      admission := .full
      layer := .original }

/-- Licensed local cone with the diagonal difference branch removed. -/
def licensedARS : ARS where
  Carrier := EqWBreakerNode
  step := LocalLicensed
  scope :=
    { location := .root
      closure := .reflexiveTransitive
      admission := .guarded
      layer := .original }

instance rawARS_fintype : Fintype rawARS.Carrier := by
  change Fintype EqWBreakerNode
  infer_instance

instance licensedARS_fintype : Fintype licensedARS.Carrier := by
  change Fintype EqWBreakerNode
  infer_instance

/-- The raw relation viewed as a total-domain partial identity morphism. -/
def rawIdentityMorphism :
    PartialLicensedReductionMorphism rawARS rawARS :=
  PartialLicensedReductionMorphism.id rawARS

/-- The canonical disequality license as a total-domain, edge-restricting,
identity-on-states partial morphism. -/
def licenseMorphism : PartialLicensedReductionMorphism rawARS licensedARS where
  domain := fun _ => True
  admitted := LocalLicensed
  admitted_sub_raw := fun h =>
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone.licensed_subrelation h
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := fun x => x.val
  map_step := fun h => h

/-- Raw semantic scope at the canonical equality-witness source. -/
def rawScope : SemanticScope rawARS :=
  SemanticScope.raw rawARS EqWBreakerNode.source .local .external 1

/-- Licensed semantic scope induced by the actual license morphism. -/
def licensedScope : SemanticScope rawARS :=
  SemanticScope.licensed licenseMorphism EqWBreakerNode.source
    .local .licensed 0

/-- Empty defect coverage after licensing. -/
def licensedCloses (_ : RepairAction) : Finset CanonicalDefect := ∅

theorem licensedCoverable :
    IsRepairCover (∅ : Finset CanonicalDefect)
      licensedCloses Finset.univ := by
  intro b hb
  simp at hb

/-- Raw construction data. The two alternative-count fields are stored as
`2`; downstream adequacy theorems compare them with relation-derived counts.
The defect, repair, cost, and witness fields come from the local cone objects. -/
def rawData :
    SemanticConstructionData rawARS CanonicalDefect RepairAction where
  scope := rawScope
  defects :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.bad
  closes :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.closes
  coverable :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.coverable
  actionCost :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.actionCost
  witnessAdequacy :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank.ko7Adequacy
  fixedLengthAlternatives := 2
  prefixCodeAlternatives := 2

/-- Licensed construction data with both alternative-count fields stored as
`1` after removal of the unique local defect. -/
def licensedData :
    SemanticConstructionData rawARS CanonicalDefect RepairAction where
  scope := licensedScope
  defects := ∅
  closes := licensedCloses
  coverable := licensedCoverable
  actionCost :=
    OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7RepairCover.actionCost
  witnessAdequacy := baseAdequacy
  fixedLengthAlternatives := 1
  prefixCodeAlternatives := 1

/-- The raw scope stores the previously mechanized raw relation. -/
theorem rawScope_relation_iff (x y : EqWBreakerNode) :
    rawScope.relation x y ↔ LocalRaw x y :=
  Iff.rfl

/-- The licensed scope stores the previously mechanized licensed relation. -/
theorem licensedScope_relation_iff (x y : EqWBreakerNode) :
    licensedScope.relation x y ↔ LocalLicensed x y :=
  Iff.rfl

/-- Existing raw normalization transports definitionally into the scope. -/
theorem rawScope_normalizing :
    NormalizingAt rawScope.relation rawScope.source :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.raw_normalizingAt_source

/-- Existing licensed normalization transports definitionally into the scope. -/
theorem licensedScope_normalizing :
    NormalizingAt licensedScope.relation licensedScope.source :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7TerminalMultiplicity.licensed_normalizingAt_source

/-- The license morphism actually rejects the raw difference edge. -/
theorem difference_edge_rejected_fixture :
    rawARS.step .source .diffVerdict ∧
      ¬ licenseMorphism.admitted .source .diffVerdict := by
  constructor
  · exact LocalRaw.diff
  · change ¬ LocalLicensed .source .diffVerdict
    intro h
    cases h

#check rawData
#check licensedData
#check rawIdentityMorphism
#check rawScope_normalizing
#check licensedScope_normalizing
#check difference_edge_rejected_fixture
#print axioms rawScope_relation_iff
#print axioms licensedScope_relation_iff
#print axioms rawScope_normalizing
#print axioms licensedScope_normalizing
#print axioms difference_edge_rejected_fixture

end KO7DistinctionAdapter
end OperatorKO7.Meta.LicensedBoundaryCalculus
