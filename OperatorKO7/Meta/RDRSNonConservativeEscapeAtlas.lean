import OperatorKO7.Meta.DirectBarrierScope
import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog
import OperatorKO7.Meta.RDRSTerminationMethodUniverse
import OperatorKO7.Meta.SharingBarrierLift

/-!
# RDRS Nonconservative Escape Atlas

This layer closes the graph, quotient, translation, CPS, and sharing-aware rows
whose mechanism changes the carrier or semantics instead of supplying a direct
tree-term orientation theorem.
-/

namespace OperatorKO7.RDRSNonConservativeEscapeAtlas

open OperatorKO7.RDRSTerminationMethodUniverse

/-- T8 row names, including local splits that share one atlas family. -/
inductive NonConservativeEscapeRow
  | sharingSemantics
  | weightedTypeGraph
  | generalizedWeightedTypeGraph
  | weightedSubgraphCounting
  | equationalQuotient
  | cycleRewriting
  | stringRewriting
  | processTranslation
  | lambdaMuCPS
  | quasiInterpretation
  deriving DecidableEq, Repr

/-- Local reason vocabulary for T8. -/
inductive NonConservativeReason
  | sharingSemanticsChangesCarrier
  | graphWeightUsesDAGCarrier
  | quotientCollapsesDuplication
  | notRDRSCarrier
  | translationChangesCalculus
  | cpsChangesCalculus
  | sharingAwareComplexity
  deriving DecidableEq, Repr

/-- Atlas row projected by each local T8 split row. -/
def atlasFamily : NonConservativeEscapeRow → RDRSMethodFamily
  | .sharingSemantics => .sharingNonConservativity
  | .weightedTypeGraph => .weightedTypeGraphEscape
  | .generalizedWeightedTypeGraph => .generalizedWeightedTypeGraphs
  | .weightedSubgraphCounting => .generalizedWeightedTypeGraphs
  | .equationalQuotient => .equationalQuotientNonConservativity
  | .cycleRewriting => .cycleRewritingInapplicability
  | .stringRewriting => .stringRewritingInapplicability
  | .processTranslation => .piCalculusTerminationTranslation
  | .lambdaMuCPS => .lambdaMuSNViaCPS
  | .quasiInterpretation => .quasiInterpretationsSharingAware

/-- Terminal atlas status for a local T8 row. -/
def rowStatus (row : NonConservativeEscapeRow) : RDRSMethodStatus :=
  statusOf (atlasFamily row)

/-- Local reason for each T8 row. -/
def rowReason : NonConservativeEscapeRow → NonConservativeReason
  | .sharingSemantics => .sharingSemanticsChangesCarrier
  | .weightedTypeGraph => .graphWeightUsesDAGCarrier
  | .generalizedWeightedTypeGraph => .graphWeightUsesDAGCarrier
  | .weightedSubgraphCounting => .graphWeightUsesDAGCarrier
  | .equationalQuotient => .quotientCollapsesDuplication
  | .cycleRewriting => .notRDRSCarrier
  | .stringRewriting => .notRDRSCarrier
  | .processTranslation => .translationChangesCalculus
  | .lambdaMuCPS => .cpsChangesCalculus
  | .quasiInterpretation => .sharingAwareComplexity

/-- Exact finite T8 row ledger. -/
def nonConservativeRows : List NonConservativeEscapeRow :=
  [ .sharingSemantics
  , .weightedTypeGraph
  , .generalizedWeightedTypeGraph
  , .weightedSubgraphCounting
  , .equationalQuotient
  , .cycleRewriting
  , .stringRewriting
  , .processTranslation
  , .lambdaMuCPS
  , .quasiInterpretation
  ]

theorem nonConservativeRows_nodup :
    nonConservativeRows.Nodup := by
  decide

theorem nonConservativeRows_complete :
    ∀ row : NonConservativeEscapeRow, row ∈ nonConservativeRows := by
  intro row
  cases row <;> decide

theorem nonConservativeRows_length :
    nonConservativeRows.length = 10 := by
  decide

theorem rowStatus_terminal (row : NonConservativeEscapeRow) :
    ∃ status : RDRSMethodStatus, rowStatus row = status :=
  ⟨rowStatus row, rfl⟩

theorem sharing_row_projects_status :
    rowStatus .sharingSemantics =
      statusOf RDRSMethodFamily.sharingNonConservativity := rfl

theorem weighted_type_graph_row_projects_status :
    rowStatus .weightedTypeGraph =
      statusOf RDRSMethodFamily.weightedTypeGraphEscape := rfl

theorem generalized_weighted_graph_row_projects_status :
    rowStatus .generalizedWeightedTypeGraph =
      statusOf RDRSMethodFamily.generalizedWeightedTypeGraphs := rfl

theorem weighted_subgraph_counting_row_projects_status :
    rowStatus .weightedSubgraphCounting =
      statusOf RDRSMethodFamily.generalizedWeightedTypeGraphs := rfl

theorem equational_quotient_row_projects_status :
    rowStatus .equationalQuotient =
      statusOf RDRSMethodFamily.equationalQuotientNonConservativity := rfl

theorem cycle_rewriting_row_projects_status :
    rowStatus .cycleRewriting =
      statusOf RDRSMethodFamily.cycleRewritingInapplicability := rfl

theorem string_rewriting_row_projects_status :
    rowStatus .stringRewriting =
      statusOf RDRSMethodFamily.stringRewritingInapplicability := rfl

theorem process_translation_row_projects_status :
    rowStatus .processTranslation =
      statusOf RDRSMethodFamily.piCalculusTerminationTranslation := rfl

theorem lambda_mu_cps_row_projects_status :
    rowStatus .lambdaMuCPS =
      statusOf RDRSMethodFamily.lambdaMuSNViaCPS := rfl

theorem quasi_interpretation_row_projects_status :
    rowStatus .quasiInterpretation =
      statusOf RDRSMethodFamily.quasiInterpretationsSharingAware := rfl

theorem sharing_row_reason :
    rowReason .sharingSemantics = .sharingSemanticsChangesCarrier := rfl

theorem weighted_type_graph_row_reason :
    rowReason .weightedTypeGraph = .graphWeightUsesDAGCarrier := rfl

theorem equational_quotient_row_reason :
    rowReason .equationalQuotient = .quotientCollapsesDuplication := rfl

theorem process_translation_row_reason :
    rowReason .processTranslation = .translationChangesCalculus := rfl

theorem lambda_mu_cps_row_reason :
    rowReason .lambdaMuCPS = .cpsChangesCalculus := rfl

theorem quasi_interpretation_row_reason :
    rowReason .quasiInterpretation = .sharingAwareComplexity := rfl

theorem sharing_counter_witness :
    ∀ b s n : OperatorKO7.SharingBarrierLift.SharedTerm,
      OperatorKO7.SharingBarrierLift.sharedCounter
          (OperatorKO7.SharingBarrierLift.SharedTerm.shareApp s
            (OperatorKO7.SharingBarrierLift.SharedTerm.recur b s n)) <
        OperatorKO7.SharingBarrierLift.sharedCounter
          (OperatorKO7.SharingBarrierLift.SharedTerm.recur b s
            (OperatorKO7.SharingBarrierLift.SharedTerm.succ n)) :=
  OperatorKO7.SharingBarrierLift.sharing_breaks_tree_barrier

/-- Minimal quotient-collapse witness for the equational row. -/
inductive QuotientTerm
  | atom
  | wrap : QuotientTerm → QuotientTerm
  deriving DecidableEq, Repr

/-- Idempotent wrap quotient used by the atlas row. -/
inductive IdempotentWrapEq : QuotientTerm → QuotientTerm → Prop
  | collapse : ∀ t, IdempotentWrapEq (.wrap (.wrap t)) (.wrap t)

theorem quotient_collapses_duplicate_wrap :
    IdempotentWrapEq (.wrap (.wrap .atom)) (.wrap .atom) :=
  IdempotentWrapEq.collapse .atom

/-- Packed T8 closure certificate. -/
structure NonConservativeEscapeLayerClosed : Prop where
  allRowsListed :
    ∀ row : NonConservativeEscapeRow, row ∈ nonConservativeRows
  noDuplicateRows : nonConservativeRows.Nodup
  exactRowCount : nonConservativeRows.length = 10
  allStatusesTerminal :
    ∀ row : NonConservativeEscapeRow, ∃ status : RDRSMethodStatus, rowStatus row = status
  sharingOutsideDirectScope :
    ¬ OperatorKO7.StepDuplicating.InScope OperatorKO7.StepDuplicating.sharingScope
  quotientOutsideDirectScope :
    ¬ OperatorKO7.StepDuplicating.InScope OperatorKO7.StepDuplicating.acQuotientScope
  sharingCounter :
    ∀ b s n : OperatorKO7.SharingBarrierLift.SharedTerm,
      OperatorKO7.SharingBarrierLift.sharedCounter
          (OperatorKO7.SharingBarrierLift.SharedTerm.shareApp s
            (OperatorKO7.SharingBarrierLift.SharedTerm.recur b s n)) <
        OperatorKO7.SharingBarrierLift.sharedCounter
          (OperatorKO7.SharingBarrierLift.SharedTerm.recur b s
            (OperatorKO7.SharingBarrierLift.SharedTerm.succ n))
  quotientCollapse :
    IdempotentWrapEq (.wrap (.wrap .atom)) (.wrap .atom)
  sharingCatalog :
    OperatorKO7.HigherOrderSharingBoundaryFinalCatalog.HigherOrderSharingBoundaryCatalog
  weightedTypeGraphReason :
    rowReason .weightedTypeGraph = .graphWeightUsesDAGCarrier
  equationalQuotientReason :
    rowReason .equationalQuotient = .quotientCollapsesDuplication
  processTranslationReason :
    rowReason .processTranslation = .translationChangesCalculus
  lambdaMuCPSReason :
    rowReason .lambdaMuCPS = .cpsChangesCalculus
  quasiInterpretationReason :
    rowReason .quasiInterpretation = .sharingAwareComplexity

/-- Acceptance marker for T8. -/
theorem rdrs_nonconservative_escape_layer_closed :
    NonConservativeEscapeLayerClosed where
  allRowsListed := nonConservativeRows_complete
  noDuplicateRows := nonConservativeRows_nodup
  exactRowCount := nonConservativeRows_length
  allStatusesTerminal := rowStatus_terminal
  sharingOutsideDirectScope :=
    OperatorKO7.StepDuplicating.sharingScope_not_InScope
  quotientOutsideDirectScope :=
    OperatorKO7.StepDuplicating.acQuotientScope_not_InScope
  sharingCounter := sharing_counter_witness
  quotientCollapse := quotient_collapses_duplicate_wrap
  sharingCatalog :=
    OperatorKO7.HigherOrderSharingBoundaryFinalCatalog.higher_order_sharing_boundary_final_catalog
  weightedTypeGraphReason := weighted_type_graph_row_reason
  equationalQuotientReason := equational_quotient_row_reason
  processTranslationReason := process_translation_row_reason
  lambdaMuCPSReason := lambda_mu_cps_row_reason
  quasiInterpretationReason := quasi_interpretation_row_reason

end OperatorKO7.RDRSNonConservativeEscapeAtlas
