import OperatorKO7.Meta.DirectBarrierScope
import OperatorKO7.Meta.HigherOrderRewriting_FinalCatalog
import OperatorKO7.Meta.RDRSTerminationMethodUniverse
import OperatorKO7.Meta.TypedBarrierSurvival

/-!
# RDRS Type And Computability No-Barrier Zones

This layer closes the RDRS rows whose method families accept the recursor by
their typed or computability rule, plus the resource-typing rows that reject the
term before any orientation question is reached.
-/

namespace OperatorKO7.RDRSNoBarrierZones

open OperatorKO7.RDRSTerminationMethodUniverse

/-- T6 row names, including local splits that share one atlas family. -/
inductive TypeComputabilityRow
  | horpo
  | cpo
  | generalSchema
  | idts
  | sizedTypes
  | coqGuard
  | agdaSizedTypes
  | bellantoniCookBasic
  | bellantoniCookMinus
  | lfpl
  | lightAffineLogic
  | lightLinearLogic
  | softLinearLogic
  | ramifiedRecursion
  | higherOrderDP
  | typeIntroduction
  | manySortedDP
  | orderSortedDP
  | contextSensitiveDP
  | sizeChangeTermination
  deriving DecidableEq, Repr

/-- Local reason vocabulary for the no-barrier and typing-barrier split. -/
inductive TypeComputabilityReason
  | byDefinition
  | typingLayerBarrier
  | typedProjectionRoute
  deriving DecidableEq, Repr

/-- Atlas row projected by each local T6 split row. -/
def atlasFamily : TypeComputabilityRow → RDRSMethodFamily
  | .horpo => .horpoAdmittance
  | .cpo => .cpoAdmittance
  | .generalSchema => .generalSchemaAdmittance
  | .idts => .generalSchemaAdmittance
  | .sizedTypes => .sizedTypesAdmittance
  | .coqGuard => .coqGuardAdmittance
  | .agdaSizedTypes => .sizedTypesAdmittance
  | .bellantoniCookBasic => .bellantoniCookSplit
  | .bellantoniCookMinus => .bellantoniCookSplit
  | .lfpl => .linearLogicTypingBarrier
  | .lightAffineLogic => .linearLogicTypingBarrier
  | .lightLinearLogic => .linearLogicTypingBarrier
  | .softLinearLogic => .linearLogicTypingBarrier
  | .ramifiedRecursion => .ramifiedRecursionTypingBarrier
  | .higherOrderDP => .dpProcessorClassification
  | .typeIntroduction => .typeIntroduction
  | .manySortedDP => .manySortedPersistence
  | .orderSortedDP => .orderSortedDP
  | .contextSensitiveDP => .contextSensitiveDP
  | .sizeChangeTermination => .sizeChangeTerminationEscape

/-- Terminal atlas status for a local T6 row. -/
def rowStatus (row : TypeComputabilityRow) : RDRSMethodStatus :=
  statusOf (atlasFamily row)

/-- Local reason for each T6 row. -/
def rowReason : TypeComputabilityRow → TypeComputabilityReason
  | .horpo => .byDefinition
  | .cpo => .byDefinition
  | .generalSchema => .byDefinition
  | .idts => .byDefinition
  | .sizedTypes => .byDefinition
  | .coqGuard => .byDefinition
  | .agdaSizedTypes => .byDefinition
  | .bellantoniCookBasic => .byDefinition
  | .bellantoniCookMinus => .typingLayerBarrier
  | .lfpl => .typingLayerBarrier
  | .lightAffineLogic => .typingLayerBarrier
  | .lightLinearLogic => .typingLayerBarrier
  | .softLinearLogic => .typingLayerBarrier
  | .ramifiedRecursion => .typingLayerBarrier
  | .higherOrderDP => .typedProjectionRoute
  | .typeIntroduction => .typedProjectionRoute
  | .manySortedDP => .typedProjectionRoute
  | .orderSortedDP => .typedProjectionRoute
  | .contextSensitiveDP => .typedProjectionRoute
  | .sizeChangeTermination => .typedProjectionRoute

/-- Exact finite T6 row ledger. -/
def typeComputabilityRows : List TypeComputabilityRow :=
  [ .horpo
  , .cpo
  , .generalSchema
  , .idts
  , .sizedTypes
  , .coqGuard
  , .agdaSizedTypes
  , .bellantoniCookBasic
  , .bellantoniCookMinus
  , .lfpl
  , .lightAffineLogic
  , .lightLinearLogic
  , .softLinearLogic
  , .ramifiedRecursion
  , .higherOrderDP
  , .typeIntroduction
  , .manySortedDP
  , .orderSortedDP
  , .contextSensitiveDP
  , .sizeChangeTermination
  ]

theorem typeComputabilityRows_nodup : typeComputabilityRows.Nodup := by
  decide

theorem typeComputabilityRows_complete :
    ∀ row : TypeComputabilityRow, row ∈ typeComputabilityRows := by
  intro row
  cases row <;> decide

theorem typeComputabilityRows_length :
    typeComputabilityRows.length = 20 := by
  decide

theorem rowStatus_terminal (row : TypeComputabilityRow) :
    ∃ status : RDRSMethodStatus, rowStatus row = status :=
  ⟨rowStatus row, rfl⟩

theorem horpo_row_projects_status :
    rowStatus .horpo = statusOf RDRSMethodFamily.horpoAdmittance := rfl

theorem cpo_row_projects_status :
    rowStatus .cpo = statusOf RDRSMethodFamily.cpoAdmittance := rfl

theorem general_schema_row_projects_status :
    rowStatus .generalSchema = statusOf RDRSMethodFamily.generalSchemaAdmittance := rfl

theorem idts_row_projects_status :
    rowStatus .idts = statusOf RDRSMethodFamily.generalSchemaAdmittance := rfl

theorem sized_types_row_projects_status :
    rowStatus .sizedTypes = statusOf RDRSMethodFamily.sizedTypesAdmittance := rfl

theorem coq_guard_row_projects_status :
    rowStatus .coqGuard = statusOf RDRSMethodFamily.coqGuardAdmittance := rfl

theorem agda_sized_types_row_projects_status :
    rowStatus .agdaSizedTypes = statusOf RDRSMethodFamily.sizedTypesAdmittance := rfl

theorem bc_basic_row_reason :
    rowReason .bellantoniCookBasic = .byDefinition := rfl

theorem bc_minus_row_reason :
    rowReason .bellantoniCookMinus = .typingLayerBarrier := rfl

theorem lfpl_row_reason :
    rowReason .lfpl = .typingLayerBarrier := rfl

theorem lal_row_reason :
    rowReason .lightAffineLogic = .typingLayerBarrier := rfl

theorem lll_row_reason :
    rowReason .lightLinearLogic = .typingLayerBarrier := rfl

theorem soft_linear_row_reason :
    rowReason .softLinearLogic = .typingLayerBarrier := rfl

theorem ramified_recursion_row_reason :
    rowReason .ramifiedRecursion = .typingLayerBarrier := rfl

theorem higher_order_dp_row_reason :
    rowReason .higherOrderDP = .typedProjectionRoute := rfl

theorem type_projection_rows_reason
    (row : TypeComputabilityRow)
    (h :
      row = .typeIntroduction ∨
      row = .manySortedDP ∨
      row = .orderSortedDP ∨
      row = .contextSensitiveDP ∨
      row = .sizeChangeTermination) :
    rowReason row = .typedProjectionRoute := by
  rcases h with h | h | h | h | h
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl

/-- Simple first-order typing alone still leaves the direct additive barrier. -/
theorem simple_typed_direct_barrier_survives :
    ∀ M : OperatorKO7.TypedBarrierSurvival.AdditiveMeasure,
      ¬ (∀ (b : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.res)
           (s : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.step)
           (n : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.cnt),
        M.evalRes
            (OperatorKO7.TypedBarrierSurvival.Term.wrap s
              (OperatorKO7.TypedBarrierSurvival.Term.recur b s n)) <
          M.evalRes
            (OperatorKO7.TypedBarrierSurvival.Term.recur b s
              (OperatorKO7.TypedBarrierSurvival.Term.succ n))) :=
  OperatorKO7.TypedBarrierSurvival.no_additive_orients_typed_recSucc

/-- Packed T6 closure certificate. -/
structure TypeComputabilityNoBarrierZonesClosed : Prop where
  allRowsListed :
    ∀ row : TypeComputabilityRow, row ∈ typeComputabilityRows
  noDuplicateRows : typeComputabilityRows.Nodup
  exactRowCount : typeComputabilityRows.length = 20
  allStatusesTerminal :
    ∀ row : TypeComputabilityRow, ∃ status : RDRSMethodStatus, rowStatus row = status
  computabilityOutsideDirectScope :
    ¬ OperatorKO7.StepDuplicating.InScope OperatorKO7.StepDuplicating.computabilityScope
  higherOrderCatalog :
    OperatorKO7.HigherOrderRewritingFinalCatalog.HigherOrderRewritingCatalog
  simpleTypingStillDirect :
    ∀ M : OperatorKO7.TypedBarrierSurvival.AdditiveMeasure,
      ¬ (∀ (b : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.res)
           (s : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.step)
           (n : OperatorKO7.TypedBarrierSurvival.Term OperatorKO7.TypedBarrierSurvival.Ty.cnt),
        M.evalRes
            (OperatorKO7.TypedBarrierSurvival.Term.wrap s
              (OperatorKO7.TypedBarrierSurvival.Term.recur b s n)) <
          M.evalRes
            (OperatorKO7.TypedBarrierSurvival.Term.recur b s
              (OperatorKO7.TypedBarrierSurvival.Term.succ n)))
  bcMinusTypingLayer : rowReason .bellantoniCookMinus = .typingLayerBarrier
  lfplTypingLayer : rowReason .lfpl = .typingLayerBarrier
  lalTypingLayer : rowReason .lightAffineLogic = .typingLayerBarrier
  lllTypingLayer : rowReason .lightLinearLogic = .typingLayerBarrier
  softLinearTypingLayer : rowReason .softLinearLogic = .typingLayerBarrier
  ramifiedTypingLayer : rowReason .ramifiedRecursion = .typingLayerBarrier

/-- Acceptance marker for T6. -/
theorem rdrs_type_computability_no_barrier_zones_closed :
    TypeComputabilityNoBarrierZonesClosed where
  allRowsListed := typeComputabilityRows_complete
  noDuplicateRows := typeComputabilityRows_nodup
  exactRowCount := typeComputabilityRows_length
  allStatusesTerminal := rowStatus_terminal
  computabilityOutsideDirectScope :=
    OperatorKO7.StepDuplicating.computabilityScope_not_InScope
  higherOrderCatalog :=
    OperatorKO7.HigherOrderRewritingFinalCatalog.higher_order_rewriting_final_catalog
  simpleTypingStillDirect := simple_typed_direct_barrier_survives
  bcMinusTypingLayer := bc_minus_row_reason
  lfplTypingLayer := lfpl_row_reason
  lalTypingLayer := lal_row_reason
  lllTypingLayer := lll_row_reason
  softLinearTypingLayer := soft_linear_row_reason
  ramifiedTypingLayer := ramified_recursion_row_reason

end OperatorKO7.RDRSNoBarrierZones
