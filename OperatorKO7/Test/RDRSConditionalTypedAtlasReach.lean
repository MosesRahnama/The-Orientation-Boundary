import OperatorKO7.Meta.RDRSConditionalTypedAtlas

/-!
# Reach test: RDRSConditionalTypedAtlas

Sanity checks that the 13-row T7 closure resolves and that mechanism
classification matches the dispatch-required boundary.

Bible compliance:
- W2: `set_option autoImplicit false` set below.
- Reach / smoke test; not a release-facing theorem module.
  All theorems pin existing aggregate facts by structural equality
  on the closed 13-row enum; Trust: kernel-only `rfl` and existing
  upstream lemma applications.
-/

set_option autoImplicit false

namespace RDRSConditionalTypedAtlasReach

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSConditionalTypedAtlas

#check ConditionalTypedRow
#check ConditionalTypedMechanism
#check TypingBarrierHypothesis
#check atlasFamily
#check rowStatus
#check rowMechanism
#check typingBarrierHypothesis
#check conditionalTypedRows
#check conditionalTypedRows_length
#check conditionalTypedRows_nodup
#check conditionalTypedRows_complete
#check mechanism_status_alignment
#check ConditionalTypedAtlasClosed
#check rdrs_conditional_typed_layer_closed

/-- Spot-check: the row count is exactly 13. -/
theorem reach_row_count :
    conditionalTypedRows.length = 13 :=
  conditionalTypedRows_length

/-- Spot-check: every definitional-admitter row resolves to
`definitional_admitter` via `statusOf`. -/
theorem reach_definitional_admitter_rows_status :
    rowStatus .horpoAdmittance = .definitional_admitter ∧
    rowStatus .cpoAdmittance = .definitional_admitter ∧
    rowStatus .generalSchemaAdmittance = .definitional_admitter ∧
    rowStatus .sizedTypesAdmittance = .definitional_admitter ∧
    rowStatus .coqGuardAdmittance = .definitional_admitter :=
  ⟨horpoAdmittance_status, cpoAdmittance_status, generalSchemaAdmittance_status,
   sizedTypesAdmittance_status, coqGuardAdmittance_status⟩

/-- Spot-check: every typing-barrier row resolves to `conditional_barrier`
and carries an explicit typing-barrier hypothesis. -/
theorem reach_typing_barrier_rows :
    rowStatus .bellantoniCookSplit = .conditional_barrier ∧
    rowStatus .linearLogicTypingBarrier = .conditional_barrier ∧
    rowStatus .ramifiedRecursionTypingBarrier = .conditional_barrier ∧
    typingBarrierHypothesis .bellantoniCookSplit =
      some .nonDuplicatingFragment ∧
    typingBarrierHypothesis .linearLogicTypingBarrier =
      some .linearityForbidsDuplication ∧
    typingBarrierHypothesis .ramifiedRecursionTypingBarrier =
      some .ramificationForbidsCrossLevel :=
  ⟨bellantoniCookSplit_status, linearLogicTypingBarrier_status,
   ramifiedRecursionTypingBarrier_status, bellantoniCookSplit_hypothesis,
   linearLogicTypingBarrier_hypothesis,
   ramifiedRecursionTypingBarrier_hypothesis⟩

/-- Spot-check: CTRS/LCTRS/integer rows hit the dispatch-mandated statuses. -/
theorem reach_ctrs_lctrs_integer_rows :
    rowStatus .twoDDPForCTRS = .conditional_escape ∧
    rowStatus .operationalTerminationCTRS = .import_dependent ∧
    rowStatus .integerTermRewriting = .conditional_escape ∧
    rowStatus .lctrs = .conditional_escape ∧
    rowStatus .higherOrderLCTRS = .conditional_escape :=
  ⟨twoDDPForCTRS_status, operationalTerminationCTRS_status,
   integerTermRewriting_status, lctrs_status, higherOrderLCTRS_status⟩

/-- Spot-check: the packed closure certificate reaches all leaves. -/
theorem reach_closure_certificate_reaches_row_count :
    rdrs_conditional_typed_layer_closed.exactRowCount =
      conditionalTypedRows_length := rfl

end RDRSConditionalTypedAtlasReach
