import OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict
import OperatorKO7.Meta.RDRSCoverageLedger
import OperatorKO7.Meta.RDRSTerminationMethodAtlas

/-!
# Exact crosswalk for Paper A's two declared inventory surfaces

Paper A exposes two finite universes with different semantics:

* the fourteen proof-bearing direct-profile families in
  `KO7ObservationVerdict`; and
* the separate 76-row RDRS method atlas.

This module closes their union without conflating them.  A direct-profile row
carries an actual candidate and relation-correct non-orientation proofs for
both the KO7 root relation `Step` and `SelfEmbeddingStep`.  An atlas row carries
its exact eight-way atlas status and six-way U6 classification, membership in
both 76-row ledgers, and a proof that it is not temporarily unclassified.

The atlas branch is deliberately not upgraded to candidate-profile coverage:
its source enum contains method names and classifications, not the typed
measure/order data required to construct a `Candidate` or prove orientation
failure for every member of the named method family.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.KO7DeclaredInventoryCoverage

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSTerminationMethodAtlas
open OperatorKO7.RDRSCoverageLedger.Full
open OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

/-! ## Proof-bearing direct-profile branch -/

/-- Exact proposition carried by one of the fourteen direct-profile tags.

Relation: KO7 root `Step` and `SelfEmbeddingStep`, separately.
Property: relation-relative non-orientation of the tag's concrete
proof-bearing representative.
Scope: the fourteen `DeclaredFamilyTag` constructors only.
-/
def DirectProfileCovered (tag : DeclaredFamilyTag) : Prop :=
  (∃ entry : DeclaredDirectUniverse,
      DeclaredFamilyMatches tag entry ∧
        (candidateOfDeclaredDirectUniverse entry).orienter = entry.1 ∧
        ¬ directProfile .recursor (candidateOfDeclaredDirectUniverse entry) ∧
        ¬ directProfile .selfEmbedding
          (candidateOfDeclaredDirectUniverse entry)) ∧
    (∀ entry : DeclaredDirectUniverse,
      DeclaredFamilyMatches tag entry →
        (candidateOfDeclaredDirectUniverse entry).orienter = entry.1 ∧
        ¬ directProfile .recursor (candidateOfDeclaredDirectUniverse entry) ∧
        ¬ directProfile .selfEmbedding
          (candidateOfDeclaredDirectUniverse entry))

/-- Every exact direct-profile tag has a concrete relation-correct receipt. -/
theorem directProfileCovered (tag : DeclaredFamilyTag) :
    DirectProfileCovered tag := by
  constructor
  · refine ⟨declaredFamilyCandidate tag,
      declaredFamilyCandidate_matches_tag tag, ?_⟩
    exact candidateProfile_covers_declared_direct_universe
      (declaredFamilyCandidate tag)
  · intro entry _
    exact candidateProfile_covers_declared_direct_universe entry

/-! ## Exact 76-row atlas-classification branch -/

/-- No row in the closed 76-family atlas occupies the residual U6 bucket. -/
theorem u6ClassOf_ne_temporaryUnclassified (family : RDRSMethodFamily) :
    u6ClassOf family ≠ .temporaryUnclassified := by
  cases family <;> decide

/-- Typed receipt for one 76-row atlas family.

This is an exact classification receipt, not a semantic candidate or a
family-wide non-orientation theorem.  The distinction is load-bearing because
the atlas row stores no evaluator or codomain order.
-/
structure AtlasClassificationReceipt (family : RDRSMethodFamily) : Prop where
  universeMember : family ∈ allMethodFamilies
  atlasRowMember : rowOf family ∈ rdrsTerminationMethodAtlas
  atlasStatusExact : (rowOf family).status = statusOf family
  atlasReasonExact :
    (rowOf family).reason = reasonOfStatus (statusOf family)
  atlasSurfaceExact :
    (rowOf family).surface = surfaceOfStatus (statusOf family)
  coverageRowMember : coverageLedgerRowOf family ∈ rdrsFullCoverageLedger
  coverageFamilyExact : (coverageLedgerRowOf family).family = family
  coverageClassExact :
    (coverageLedgerRowOf family).classification = u6ClassOf family
  classificationNotTemporary : u6ClassOf family ≠ .temporaryUnclassified

/-- Every exact atlas family has a non-residual typed classification receipt. -/
theorem atlasClassificationReceipt (family : RDRSMethodFamily) :
    AtlasClassificationReceipt family where
  universeMember := allMethodFamilies_complete family
  atlasRowMember := rdrsTerminationMethodAtlas_family_mem family
  atlasStatusExact := rowOf_status family
  atlasReasonExact := rowOf_reason family
  atlasSurfaceExact := rowOf_surface family
  coverageRowMember :=
    List.mem_map_of_mem (f := coverageLedgerRowOf)
      (allMethodFamilies_complete family)
  coverageFamilyExact := ledgerRow_family_correct family
  coverageClassExact := ledgerRow_classification_correct family
  classificationNotTemporary := u6ClassOf_ne_temporaryUnclassified family

/-- Exact five-way non-residual U6 partition for every atlas family. -/
theorem atlasClassification_nonresidual_partition
    (family : RDRSMethodFamily) :
    u6ClassOf family = .payloadSensitiveBlocked ∨
      u6ClassOf family = .projectionTransactionEscape ∨
      u6ClassOf family = .constructionEscape ∨
      u6ClassOf family = .transformEscape ∨
      u6ClassOf family = .notDirect := by
  cases family <;> decide

/-- The exact bucket counts for the 76-row atlas, with an empty residual. -/
theorem atlasClassification_exact_counts :
    payloadSensitiveBlockedFamilies.length = 26 ∧
      projectionTransactionEscapeFamilies.length = 9 ∧
      constructionEscapeFamilies.length = 8 ∧
      transformEscapeFamilies.length = 13 ∧
      notDirectFamiliesU6.length = 20 ∧
      temporaryUnclassifiedFamilies.length = 0 := by
  exact ⟨payloadSensitiveBlocked_count,
    projectionTransactionEscape_count,
    constructionEscape_count,
    transformEscape_count,
    notDirect_count_U6,
    temporary_unclassified_count⟩

/-! ## Disjoint union and total coverage theorem -/

/-- The complete declared inventory surface used by this bridge.  The sum is
intentional: it prevents a 76-row atlas classification from elaborating as a
fourteen-family direct candidate. -/
inductive PaperADeclaredInventoryRow where
  | directProfile (tag : DeclaredFamilyTag)
  | methodAtlas (family : RDRSMethodFamily)
  deriving DecidableEq, Repr

/-- Fourteen proof-bearing direct-profile rows. -/
def directProfileInventoryRows : List PaperADeclaredInventoryRow :=
  declaredFamilyLedger.map PaperADeclaredInventoryRow.directProfile

/-- The separate 76 classified method-atlas rows. -/
def methodAtlasInventoryRows : List PaperADeclaredInventoryRow :=
  allMethodFamilies.map PaperADeclaredInventoryRow.methodAtlas

/-- Complete 90-row disjoint inventory: 14 direct-profile rows plus 76 atlas
classification rows. -/
def paperADeclaredInventoryLedger : List PaperADeclaredInventoryRow :=
  directProfileInventoryRows ++ methodAtlasInventoryRows

theorem directProfileInventoryRows_length :
    directProfileInventoryRows.length = 14 := by
  simpa [directProfileInventoryRows] using declaredFamilyLedger_length

theorem methodAtlasInventoryRows_length :
    methodAtlasInventoryRows.length = 76 := by
  simpa [methodAtlasInventoryRows] using allMethodFamilies_length

theorem paperADeclaredInventoryLedger_length :
    paperADeclaredInventoryLedger.length = 90 := by
  simp [paperADeclaredInventoryLedger,
    directProfileInventoryRows_length,
    methodAtlasInventoryRows_length]

theorem paperADeclaredInventoryLedger_nodup :
    paperADeclaredInventoryLedger.Nodup := by
  decide

theorem paperADeclaredInventoryLedger_complete
    (row : PaperADeclaredInventoryRow) :
    row ∈ paperADeclaredInventoryLedger := by
  cases row with
  | directProfile tag =>
      simp [paperADeclaredInventoryLedger, directProfileInventoryRows,
        methodAtlasInventoryRows, declaredFamilyLedger_complete tag]
  | methodAtlas family =>
      simp [paperADeclaredInventoryLedger, directProfileInventoryRows,
        methodAtlasInventoryRows, allMethodFamilies_complete family]

/-- Exact coverage proposition for the disjoint inventory.  Only the direct
branch claims relation-correct candidate non-orientation; the atlas branch
claims exactly the classifications its typed ledgers contain. -/
def PaperADeclaredInventoryRow.Covered :
    PaperADeclaredInventoryRow → Prop
  | .directProfile tag => DirectProfileCovered tag
  | .methodAtlas family => AtlasClassificationReceipt family

/-- Maximum honest closure of the current artifacts: all 14 direct rows have
candidate/no-orientation receipts and all 76 atlas rows have exact,
non-residual classification receipts. -/
theorem paperADeclaredInventory_coverage_total
    (row : PaperADeclaredInventoryRow) : row.Covered := by
  cases row with
  | directProfile tag => exact directProfileCovered tag
  | methodAtlas family => exact atlasClassificationReceipt family

/-- Eliminator exposing the exact branch and its corresponding proof burden. -/
theorem paperADeclaredInventory_profile_or_atlas_classified
    (row : PaperADeclaredInventoryRow) :
    (∃ tag : DeclaredFamilyTag,
      row = .directProfile tag ∧ DirectProfileCovered tag) ∨
    (∃ family : RDRSMethodFamily,
      row = .methodAtlas family ∧ AtlasClassificationReceipt family) := by
  cases row with
  | directProfile tag =>
      exact Or.inl ⟨tag, rfl, directProfileCovered tag⟩
  | methodAtlas family =>
      exact Or.inr ⟨family, rfl, atlasClassificationReceipt family⟩

/-- The two inventory branches are definitionally disjoint.  In particular,
an atlas classification is not silently treated as a direct candidate. -/
theorem directProfileRow_ne_methodAtlasRow
    (tag : DeclaredFamilyTag) (family : RDRSMethodFamily) :
    PaperADeclaredInventoryRow.directProfile tag ≠
      PaperADeclaredInventoryRow.methodAtlas family := by
  intro h
  cases h

/-- One paper-facing closure certificate bundling enumeration and proof scope. -/
theorem paperADeclaredInventory_exactProvedScope :
    directProfileInventoryRows.length = 14 ∧
      methodAtlasInventoryRows.length = 76 ∧
      paperADeclaredInventoryLedger.length = 90 ∧
      paperADeclaredInventoryLedger.Nodup ∧
      (∀ row : PaperADeclaredInventoryRow,
        row ∈ paperADeclaredInventoryLedger ∧ row.Covered) := by
  refine ⟨directProfileInventoryRows_length,
    methodAtlasInventoryRows_length,
    paperADeclaredInventoryLedger_length,
    paperADeclaredInventoryLedger_nodup, ?_⟩
  intro row
  exact ⟨paperADeclaredInventoryLedger_complete row,
    paperADeclaredInventory_coverage_total row⟩

/-- Structured closeout certificate for the exact two-surface inventory.
Every field is propositional: the certificate adds no new method semantics. -/
structure PaperADeclaredInventoryClosed : Prop where
  directProfileRowCount : directProfileInventoryRows.length = 14
  methodAtlasRowCount : methodAtlasInventoryRows.length = 76
  totalRowCount : paperADeclaredInventoryLedger.length = 90
  noDuplicateTypedRows : paperADeclaredInventoryLedger.Nodup
  rowsComplete : ∀ row : PaperADeclaredInventoryRow,
    row ∈ paperADeclaredInventoryLedger
  rowsCoveredAtExactScope : ∀ row : PaperADeclaredInventoryRow, row.Covered
  branchesDisjoint : ∀ (tag : DeclaredFamilyTag)
    (family : RDRSMethodFamily),
    PaperADeclaredInventoryRow.directProfile tag ≠
      PaperADeclaredInventoryRow.methodAtlas family
  payloadSensitiveBlockedCount : payloadSensitiveBlockedFamilies.length = 26
  projectionTransactionEscapeCount :
    projectionTransactionEscapeFamilies.length = 9
  constructionEscapeCount : constructionEscapeFamilies.length = 8
  transformEscapeCount : transformEscapeFamilies.length = 13
  notDirectCount : notDirectFamiliesU6.length = 20
  temporaryUnclassifiedCount : temporaryUnclassifiedFamilies.length = 0

/-- Kernel-facing closeout for all facts currently justified by the combined
14-row direct-profile and 76-row classification artifacts. -/
theorem paperA_declared_inventory_closed : PaperADeclaredInventoryClosed where
  directProfileRowCount := directProfileInventoryRows_length
  methodAtlasRowCount := methodAtlasInventoryRows_length
  totalRowCount := paperADeclaredInventoryLedger_length
  noDuplicateTypedRows := paperADeclaredInventoryLedger_nodup
  rowsComplete := paperADeclaredInventoryLedger_complete
  rowsCoveredAtExactScope := paperADeclaredInventory_coverage_total
  branchesDisjoint := directProfileRow_ne_methodAtlasRow
  payloadSensitiveBlockedCount := payloadSensitiveBlocked_count
  projectionTransactionEscapeCount := projectionTransactionEscape_count
  constructionEscapeCount := constructionEscape_count
  transformEscapeCount := transformEscape_count
  notDirectCount := notDirect_count_U6
  temporaryUnclassifiedCount := temporary_unclassified_count

end OperatorKO7.Meta.OperationalInexpressibility.KO7DeclaredInventoryCoverage
