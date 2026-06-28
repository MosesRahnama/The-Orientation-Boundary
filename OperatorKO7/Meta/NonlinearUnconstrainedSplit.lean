import OperatorKO7.Meta.NonlinearDominanceCriteria
import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.NonlinearMethodLawCarrier

namespace OperatorKO7.NonlinearUnconstrainedSplit

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.NonlinearResidualTaxonomy
open OperatorKO7.NonlinearDominanceCriteria
open _root_.OperatorKO7.NonlinearMethodLawCarrier

/-- Exact sub-boundaries carried by the still-open nonlinear unconstrained row. -/
inductive NonlinearUnconstrainedRow where
  | transparentWithDominanceConditional
  | crossCoupledGlobalWitness
  | unsupportedArbitraryRelation
deriving DecidableEq, Repr

/-- Status vocabulary for the theorem-visible unconstrained nonlinear split. -/
inductive NonlinearUnconstrainedStatus where
  | conditionallyBlockedByDominance
  | licensedEscape (route : ConstructionRoute)
  | openUnsupportedBoundary
deriving DecidableEq, Repr

/-- The finite unconstrained nonlinear split row list formalized in this sprint. -/
def nonlinearUnconstrainedRows : List NonlinearUnconstrainedRow :=
  [.transparentWithDominanceConditional,
    .crossCoupledGlobalWitness,
    .unsupportedArbitraryRelation]

/-- The finite status list realized by the unconstrained nonlinear split. -/
def nonlinearUnconstrainedStatuses : List NonlinearUnconstrainedStatus :=
  [.conditionallyBlockedByDominance,
    .licensedEscape .W1,
    .openUnsupportedBoundary]

/-- Exact status projection for each unconstrained nonlinear sub-boundary. -/
def nonlinearUnconstrainedRowStatus :
    NonlinearUnconstrainedRow → NonlinearUnconstrainedStatus
  | .transparentWithDominanceConditional => .conditionallyBlockedByDominance
  | .crossCoupledGlobalWitness => .licensedEscape .W1
  | .unsupportedArbitraryRelation => .openUnsupportedBoundary

/-- Exact row membership characterization for the unconstrained nonlinear split. -/
theorem nonlinearUnconstrainedRows_complete_exact (row : NonlinearUnconstrainedRow) :
    row ∈ nonlinearUnconstrainedRows ↔
      row = .transparentWithDominanceConditional
        ∨ row = .crossCoupledGlobalWitness
        ∨ row = .unsupportedArbitraryRelation := by
  cases row <;> simp [nonlinearUnconstrainedRows]

/-- The finite unconstrained nonlinear split row list has no duplicates. -/
theorem nonlinearUnconstrainedRows_nodup : nonlinearUnconstrainedRows.Nodup := by
  decide

/-- The finite unconstrained nonlinear split row list has exact size three. -/
theorem nonlinearUnconstrainedRows_length : nonlinearUnconstrainedRows.length = 3 := by
  rfl

/-- Exact status membership characterization for the unconstrained nonlinear split. -/
theorem nonlinearUnconstrainedStatuses_complete_exact
    (status : NonlinearUnconstrainedStatus) :
    status ∈ nonlinearUnconstrainedStatuses ↔
      status = .conditionallyBlockedByDominance
        ∨ status = .licensedEscape .W1
        ∨ status = .openUnsupportedBoundary := by
  cases status with
  | conditionallyBlockedByDominance =>
      simp [nonlinearUnconstrainedStatuses]
  | licensedEscape route =>
      cases route <;> simp [nonlinearUnconstrainedStatuses]
  | openUnsupportedBoundary =>
      simp [nonlinearUnconstrainedStatuses]

/-- The finite unconstrained nonlinear split status list has no duplicates. -/
theorem nonlinearUnconstrainedStatuses_nodup : nonlinearUnconstrainedStatuses.Nodup := by
  decide

/-- The finite unconstrained nonlinear split status list has exact size three. -/
theorem nonlinearUnconstrainedStatuses_length : nonlinearUnconstrainedStatuses.length = 3 := by
  rfl

/-- Every unconstrained nonlinear split row lands in the finite status list. -/
theorem nonlinearUnconstrainedRow_has_listed_status (row : NonlinearUnconstrainedRow) :
    nonlinearUnconstrainedRowStatus row ∈ nonlinearUnconstrainedStatuses := by
  cases row <;> simp [nonlinearUnconstrainedRowStatus, nonlinearUnconstrainedStatuses]

/-- Theorem-backed support payload carried by each unconstrained nonlinear split row. -/
def NonlinearUnconstrainedRowSupported : NonlinearUnconstrainedRow → Prop
  | .transparentWithDominanceConditional =>
      TransparentPolynomialDominanceCriteriaCatalog
  | .crossCoupledGlobalWitness =>
      poly_w1_success.route = .W1
        ∧ poly_w1_success.importClass = .globalPolynomial
        ∧ PermittedW1Import .globalPolynomial
  | .unsupportedArbitraryRelation =>
      nonlinearUnconstrainedRowStatus .unsupportedArbitraryRelation = .openUnsupportedBoundary
        ∧ ∀ (R : NonlinearRelation),
            unsupported_arbitrary_relation_boundary R

/-- The transparent conditional row is supported exactly by the dominance-criteria catalog. -/
theorem transparentWithDominanceConditional_supported :
    NonlinearUnconstrainedRowSupported .transparentWithDominanceConditional :=
  transparent_polynomial_dominance_criteria_catalog

/-- The cross-coupled global witness row is exactly the existing W1 polynomial witness. -/
theorem crossCoupledGlobalWitness_supported :
    NonlinearUnconstrainedRowSupported .crossCoupledGlobalWitness := by
  exact ⟨rfl, rfl, poly_w1_success_requires_global_polynomial_import⟩

/-- The unsupported arbitrary relation row keeps the explicit boundary label and now carries the method-law dichotomy. -/
theorem unsupported_arbitrary_relation_supported_unconditional :
    NonlinearUnconstrainedRowSupported .unsupportedArbitraryRelation := by
  exact ⟨rfl,
    unsupported_arbitrary_relation_no_first_order_method_or_licensed_escape⟩

/-- The unsupported arbitrary relation row stays explicitly open. -/
theorem unsupportedArbitraryRelation_supported :
    NonlinearUnconstrainedRowSupported .unsupportedArbitraryRelation :=
  unsupported_arbitrary_relation_supported_unconditional

/-- Non-overclaim: the transparent conditional row is not itself a licensed escape row. -/
theorem transparentWithDominanceConditional_not_licensedEscape :
    nonlinearUnconstrainedRowStatus .transparentWithDominanceConditional ≠ .licensedEscape .W1 := by
  decide

/-- Non-overclaim: the cross-coupled global witness row is not claimed as conditionally blocked. -/
theorem crossCoupledGlobalWitness_not_conditionallyBlocked :
    nonlinearUnconstrainedRowStatus .crossCoupledGlobalWitness ≠ .conditionallyBlockedByDominance := by
  decide

/-- Non-overclaim: the unsupported arbitrary relation row is not claimed as blocked by dominance. -/
theorem unsupportedArbitraryRelation_not_conditionallyBlocked :
    nonlinearUnconstrainedRowStatus .unsupportedArbitraryRelation ≠ .conditionallyBlockedByDominance := by
  decide

/-- Non-overclaim: the unsupported arbitrary relation row is not claimed as a licensed escape. -/
theorem unsupportedArbitraryRelation_not_licensedEscape :
    nonlinearUnconstrainedRowStatus .unsupportedArbitraryRelation ≠ .licensedEscape .W1 := by
  decide

/-- Exact split catalog for the currently open unconstrained nonlinear row. -/
abbrev NonlinearUnconstrainedSplitCatalog : Prop :=
  ∀ row : NonlinearUnconstrainedRow,
    row ∈ nonlinearUnconstrainedRows
      ∧ NonlinearUnconstrainedRowSupported row
      ∧ nonlinearUnconstrainedRowStatus row ∈ nonlinearUnconstrainedStatuses

/-- The unconstrained nonlinear row is split exactly into the listed theorem-visible sub-boundaries. -/
theorem nonlinear_unconstrained_split_catalog :
    NonlinearUnconstrainedSplitCatalog := by
  intro row
  refine ⟨(nonlinearUnconstrainedRows_complete_exact row).2 ?_, ?_,
    nonlinearUnconstrainedRow_has_listed_status row⟩
  · cases row <;> simp
  · cases row with
    | transparentWithDominanceConditional =>
        exact transparentWithDominanceConditional_supported
    | crossCoupledGlobalWitness =>
        exact crossCoupledGlobalWitness_supported
    | unsupportedArbitraryRelation =>
        exact unsupportedArbitraryRelation_supported

/-- Certificate packaging the parent open-row status and its exact sub-boundary split. -/
structure NonlinearUnconstrainedSplitCertificate where
  parentStatus : nonlinearResidualStatus .unconstrainedNonlinearDirect = .openResidualClass
  splitCatalog : NonlinearUnconstrainedSplitCatalog

/-- The open unconstrained nonlinear row is sharpened by an exact theorem-visible split. -/
theorem nonlinear_unconstrained_split_certificate :
    NonlinearUnconstrainedSplitCertificate := by
  exact {
    parentStatus := rfl
    splitCatalog := nonlinear_unconstrained_split_catalog
  }

/-- The unconstrained split certificate projects the parent open-row status. -/
theorem nonlinear_unconstrained_split_certificate_projects_parent_status :
    nonlinearResidualStatus .unconstrainedNonlinearDirect = .openResidualClass :=
  nonlinear_unconstrained_split_certificate.parentStatus

/-- The unconstrained split certificate projects the exact sub-boundary catalog. -/
theorem nonlinear_unconstrained_split_certificate_projects_split_catalog :
    NonlinearUnconstrainedSplitCatalog :=
  nonlinear_unconstrained_split_certificate.splitCatalog

end OperatorKO7.NonlinearUnconstrainedSplit
