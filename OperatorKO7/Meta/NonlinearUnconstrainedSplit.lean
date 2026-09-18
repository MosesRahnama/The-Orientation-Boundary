import OperatorKO7.Meta.NonlinearDominanceCriteria
import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.NonlinearMethodLawCarrier

/-!
# NonlinearUnconstrainedSplit

## Formal Scope

NonlinearUnconstrainedRow is a three-constructor policy taxonomy, and the inventory theorem exhausts that defined type. No classifier from an external unconstrained nonlinear-method domain is provided.
-/

namespace OperatorKO7.NonlinearUnconstrainedSplit

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearDominanceCriteria
open _root_.OperatorKO7.NonlinearMethodLawCarrier

/-- Three tags used to subdivide the nonlinear-unconstrained metadata row. -/
inductive NonlinearUnconstrainedRow where
  | transparentWithDominanceBoundary
  | crossCoupledGlobalWitness
  | arbitraryRelationLawBoundary
deriving DecidableEq, Repr

/-- Status tags assigned to the three metadata rows. -/
inductive NonlinearUnconstrainedStatus where
  | blockedUnderDominanceHypotheses
  | licensedEscape (route : ConstructionRoute)
  | exactLawCarrierDichotomy
deriving DecidableEq, Repr

/-- Enumeration of every constructor of `NonlinearUnconstrainedRow`. -/
def nonlinearUnconstrainedRows : List NonlinearUnconstrainedRow :=
  [.transparentWithDominanceBoundary,
    .crossCoupledGlobalWitness,
    .arbitraryRelationLawBoundary]

/-- Status values used by `nonlinearUnconstrainedRowStatus`. -/
def nonlinearUnconstrainedStatuses : List NonlinearUnconstrainedStatus :=
  [.blockedUnderDominanceHypotheses,
    .licensedEscape .W1,
    .exactLawCarrierDichotomy]

/-- Constructor-to-status assignment. -/
def nonlinearUnconstrainedRowStatus :
    NonlinearUnconstrainedRow → NonlinearUnconstrainedStatus
  | .transparentWithDominanceBoundary => .blockedUnderDominanceHypotheses
  | .crossCoupledGlobalWitness => .licensedEscape .W1
  | .arbitraryRelationLawBoundary => .exactLawCarrierDichotomy

/-- Membership characterization for the three-constructor row type. -/
theorem nonlinearUnconstrainedRows_complete_exact (row : NonlinearUnconstrainedRow) :
    row ∈ nonlinearUnconstrainedRows ↔
      row = .transparentWithDominanceBoundary
        ∨ row = .crossCoupledGlobalWitness
        ∨ row = .arbitraryRelationLawBoundary := by
  cases row <;> simp [nonlinearUnconstrainedRows]

/-- The finite unconstrained nonlinear split row list has no duplicates. -/
theorem nonlinearUnconstrainedRows_nodup : nonlinearUnconstrainedRows.Nodup := by
  decide

/-- The finite unconstrained nonlinear split row list has specified size three. -/
theorem nonlinearUnconstrainedRows_length : nonlinearUnconstrainedRows.length = 3 := by
  rfl

/-- specified status membership characterization for the unconstrained nonlinear split. -/
theorem nonlinearUnconstrainedStatuses_complete_exact
    (status : NonlinearUnconstrainedStatus) :
    status ∈ nonlinearUnconstrainedStatuses ↔
      status = .blockedUnderDominanceHypotheses
        ∨ status = .licensedEscape .W1
        ∨ status = .exactLawCarrierDichotomy := by
  cases status with
  | blockedUnderDominanceHypotheses =>
      simp [nonlinearUnconstrainedStatuses]
  | licensedEscape route =>
      cases route <;> simp [nonlinearUnconstrainedStatuses]
  | exactLawCarrierDichotomy =>
      simp [nonlinearUnconstrainedStatuses]

/-- The finite unconstrained nonlinear split status list has no duplicates. -/
theorem nonlinearUnconstrainedStatuses_nodup : nonlinearUnconstrainedStatuses.Nodup := by
  decide

/-- The finite unconstrained nonlinear split status list has specified size three. -/
theorem nonlinearUnconstrainedStatuses_length : nonlinearUnconstrainedStatuses.length = 3 := by
  rfl

/-- Every constructor receives one of the listed status tags. -/
theorem nonlinearUnconstrainedRow_has_listed_status (row : NonlinearUnconstrainedRow) :
    nonlinearUnconstrainedRowStatus row ∈ nonlinearUnconstrainedStatuses := by
  cases row <;> simp [nonlinearUnconstrainedRowStatus, nonlinearUnconstrainedStatuses]

/-- Support proposition selected for each constructor tag. -/
def NonlinearUnconstrainedRowSupported : NonlinearUnconstrainedRow → Prop
  | .transparentWithDominanceBoundary =>
      TransparentPolynomialDominanceCriteriaCatalog
  | .crossCoupledGlobalWitness =>
      poly_w1_success.route = .W1
        ∧ poly_w1_success.importClass = .globalPolynomial
        ∧ PermittedW1Import .globalPolynomial
  | .arbitraryRelationLawBoundary =>
      nonlinearUnconstrainedRowStatus .arbitraryRelationLawBoundary = .exactLawCarrierDichotomy
        ∧ ∀ (R : NonlinearRelation),
            arbitrary_relation_law_boundary R

/-- The transparent dominance-hypothesis row is supported directly by the dominance-criteria catalog. -/
theorem transparentWithDominanceBoundary_supported :
    NonlinearUnconstrainedRowSupported .transparentWithDominanceBoundary :=
  transparent_polynomial_dominance_criteria_catalog

/-- The cross-coupled global witness row is directly the existing W1 polynomial witness. -/
theorem crossCoupledGlobalWitness_supported :
    NonlinearUnconstrainedRowSupported .crossCoupledGlobalWitness := by
  exact ⟨rfl, rfl, poly_w1_success_requires_global_polynomial_import⟩

/-- The unsupported arbitrary relation row keeps the explicit boundary label and here carries the method-law dichotomy. -/
theorem arbitrary_relation_law_supported_unconditional :
    NonlinearUnconstrainedRowSupported .arbitraryRelationLawBoundary := by
  exact ⟨rfl,
    arbitrary_relation_law_no_first_order_method_or_licensed_escape⟩

/-- The unsupported arbitrary relation row is closed by the exact law-carrier dichotomy. -/
theorem arbitraryRelationLawBoundary_supported :
    NonlinearUnconstrainedRowSupported .arbitraryRelationLawBoundary :=
  arbitrary_relation_law_supported_unconditional

/-- Non-overclaim: the transparent dominance-hypothesis row is not itself a licensed escape row. -/
theorem transparentWithDominanceBoundary_not_licensedEscape :
    nonlinearUnconstrainedRowStatus .transparentWithDominanceBoundary ≠ .licensedEscape .W1 := by
  decide

/-- Non-overclaim: the cross-coupled global witness row is not claimed as conditionally blocked. -/
theorem crossCoupledGlobalWitness_not_dominanceBlocked :
    nonlinearUnconstrainedRowStatus .crossCoupledGlobalWitness ≠ .blockedUnderDominanceHypotheses := by
  decide

/-- Non-overclaim: the unsupported arbitrary relation row is not claimed as blocked by dominance. -/
theorem arbitraryRelationLawBoundary_not_dominanceBlocked :
    nonlinearUnconstrainedRowStatus .arbitraryRelationLawBoundary ≠ .blockedUnderDominanceHypotheses := by
  decide

/-- Non-overclaim: the unsupported arbitrary relation row is not claimed as a licensed escape. -/
theorem arbitraryRelationLawBoundary_not_licensedEscape :
    nonlinearUnconstrainedRowStatus .arbitraryRelationLawBoundary ≠ .licensedEscape .W1 := by
  decide

/-- Catalog over the constructors of the locally defined row type. -/
abbrev NonlinearUnconstrainedSplitCatalog : Prop :=
  ∀ row : NonlinearUnconstrainedRow,
    row ∈ nonlinearUnconstrainedRows
      ∧ NonlinearUnconstrainedRowSupported row
      ∧ nonlinearUnconstrainedRowStatus row ∈ nonlinearUnconstrainedStatuses

/-- Every constructor of the local row type belongs to the list and has its
selected support proposition. This does not classify an external method domain. -/
theorem nonlinear_unconstrained_split_catalog :
    NonlinearUnconstrainedSplitCatalog := by
  intro row
  refine ⟨(nonlinearUnconstrainedRows_complete_exact row).2 ?_, ?_,
    nonlinearUnconstrainedRow_has_listed_status row⟩
  · cases row <;> simp
  · cases row with
    | transparentWithDominanceBoundary =>
        exact transparentWithDominanceBoundary_supported
    | crossCoupledGlobalWitness =>
        exact crossCoupledGlobalWitness_supported
    | arbitraryRelationLawBoundary =>
        exact arbitraryRelationLawBoundary_supported

/-- Package of the parent status tag and local-constructor catalog. -/
structure NonlinearUnconstrainedSplitCertificate where
  parentStatus : nonlinearResidualStatus .unconstrainedNonlinearDirect = .exactLawCarrierBoundary
  splitCatalog : NonlinearUnconstrainedSplitCatalog

/-- Construct the package from the parent status equality and local catalog. -/
theorem nonlinear_unconstrained_split_certificate :
    NonlinearUnconstrainedSplitCertificate := by
  exact {
    parentStatus := rfl
    splitCatalog := nonlinear_unconstrained_split_catalog
  }

/-- The unconstrained split certificate projects the parent open-row status. -/
theorem nonlinear_unconstrained_split_certificate_projects_parent_status :
    nonlinearResidualStatus .unconstrainedNonlinearDirect = .exactLawCarrierBoundary :=
  nonlinear_unconstrained_split_certificate.parentStatus

/-- Project the local-constructor catalog from the package. -/
theorem nonlinear_unconstrained_split_certificate_projects_split_catalog :
    NonlinearUnconstrainedSplitCatalog :=
  nonlinear_unconstrained_split_certificate.splitCatalog

end OperatorKO7.NonlinearUnconstrainedSplit
