import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# RDRS Conditional, Constrained, Higher-Order, and Type-Based Closure

T7 layer of the RDRS termination-method universe atlas. Closes the 13
atlas rows for the conditional / constrained / higher-order / type-based
plane, mirroring the discipline of the T6 no-barrier-zone closure
(`RDRSNoBarrierZones.lean`) without editing that file.

Mechanism partition (matches the dispatch's "Required boundary"):

  definitional_admitter (5):
    horpoAdmittance, cpoAdmittance, generalSchemaAdmittance,
    sizedTypesAdmittance, coqGuardAdmittance
      -- the method admits RDRS by its typed/computability rule;
         no orientation question is reached.

  typing barrier with explicit hypothesis (3, status conditional_barrier):
    bellantoniCookSplit         -- non-duplicating fragment BC-
    linearLogicTypingBarrier    -- LFPL / LAL / LLL / soft LL
    ramifiedRecursionTypingBarrier
      -- the typing discipline rejects RDRS by forbidding step-argument
         duplication; the hypothesis is the linearity/ramification
         discipline, not an orientation argument.

  conditional escape / import dependent (5, matching `statusOf`):
    twoDDPForCTRS              -- conditional_escape
    operationalTerminationCTRS -- import_dependent
    integerTermRewriting       -- conditional_escape
    lctrs                      -- conditional_escape
    higherOrderLCTRS           -- conditional_escape

Acceptance marker: `rdrs_conditional_typed_layer_closed`.

## Bible compliance

* W2: `set_option autoImplicit false` set below.
* W8: aggregate-level theorems (length, nodup, completeness,
  status_terminal, mechanism_status_alignment, marker) carry the
  full Proves / Does not prove / Relation / Closure / Strategy /
  Trust / Scope template. The per-row status-pin and mechanism-pin
  theorems (one `rfl` per row) are structurally identical and share
  the discipline note below: each pins a single status or mechanism
  field for a single row by `rfl`; Relation: aggregator over
  `RDRSMethodFamily` enum (not a concrete rewriting relation);
  Closure: not applicable; Strategy: not applicable; Trust:
  kernel-only `rfl`; Scope: the single row named in the theorem name.
* W5: no `native_decide` / `bv_decide`.
* R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking`.
* Relation Gate: aggregator over the 76-row `RDRSMethodFamily` enum;
  not a concrete rewriting relation.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSConditionalTypedAtlas

open OperatorKO7.RDRSTerminationMethodUniverse

/-- Local T7 row enum for the conditional / constrained / higher-order /
type-based plane. -/
inductive ConditionalTypedRow
  | twoDDPForCTRS
  | operationalTerminationCTRS
  | integerTermRewriting
  | lctrs
  | higherOrderLCTRS
  | horpoAdmittance
  | cpoAdmittance
  | generalSchemaAdmittance
  | sizedTypesAdmittance
  | coqGuardAdmittance
  | bellantoniCookSplit
  | linearLogicTypingBarrier
  | ramifiedRecursionTypingBarrier
  deriving DecidableEq, Repr

/-- Mechanism classification for a T7 row. -/
inductive ConditionalTypedMechanism
  | definitionalAdmitter
  | typingBarrierWithHypothesis
  | conditionalEscape
  | importDependent
  deriving DecidableEq, Repr

/-- The typing-barrier hypothesis attached to each typing-barrier row.
This makes the "explicit hypothesis" required by the dispatch a
first-class atlas datum rather than a comment. -/
inductive TypingBarrierHypothesis
  | nonDuplicatingFragment
  | linearityForbidsDuplication
  | ramificationForbidsCrossLevel
  deriving DecidableEq, Repr

/-- Atlas row projected by each local T7 row. The local enum is the
identity on names; the projection lifts each entry into the
`RDRSMethodFamily` carrier so `statusOf` applies. -/
def atlasFamily : ConditionalTypedRow → RDRSMethodFamily
  | .twoDDPForCTRS => .twoDDPForCTRS
  | .operationalTerminationCTRS => .operationalTerminationCTRS
  | .integerTermRewriting => .integerTermRewriting
  | .lctrs => .lctrs
  | .higherOrderLCTRS => .higherOrderLCTRS
  | .horpoAdmittance => .horpoAdmittance
  | .cpoAdmittance => .cpoAdmittance
  | .generalSchemaAdmittance => .generalSchemaAdmittance
  | .sizedTypesAdmittance => .sizedTypesAdmittance
  | .coqGuardAdmittance => .coqGuardAdmittance
  | .bellantoniCookSplit => .bellantoniCookSplit
  | .linearLogicTypingBarrier => .linearLogicTypingBarrier
  | .ramifiedRecursionTypingBarrier => .ramifiedRecursionTypingBarrier

/-- Terminal atlas status of a local T7 row. -/
def rowStatus (row : ConditionalTypedRow) : RDRSMethodStatus :=
  statusOf (atlasFamily row)

/-- Mechanism classification of each row. -/
def rowMechanism : ConditionalTypedRow → ConditionalTypedMechanism
  | .twoDDPForCTRS => .conditionalEscape
  | .operationalTerminationCTRS => .importDependent
  | .integerTermRewriting => .conditionalEscape
  | .lctrs => .conditionalEscape
  | .higherOrderLCTRS => .conditionalEscape
  | .horpoAdmittance => .definitionalAdmitter
  | .cpoAdmittance => .definitionalAdmitter
  | .generalSchemaAdmittance => .definitionalAdmitter
  | .sizedTypesAdmittance => .definitionalAdmitter
  | .coqGuardAdmittance => .definitionalAdmitter
  | .bellantoniCookSplit => .typingBarrierWithHypothesis
  | .linearLogicTypingBarrier => .typingBarrierWithHypothesis
  | .ramifiedRecursionTypingBarrier => .typingBarrierWithHypothesis

/-- The typing-barrier hypothesis, defined only for typing-barrier rows;
`none` otherwise. -/
def typingBarrierHypothesis :
    ConditionalTypedRow → Option TypingBarrierHypothesis
  | .bellantoniCookSplit => some .nonDuplicatingFragment
  | .linearLogicTypingBarrier => some .linearityForbidsDuplication
  | .ramifiedRecursionTypingBarrier => some .ramificationForbidsCrossLevel
  | _ => none

/-- Exact finite ledger of the 13 closed T7 rows. -/
def conditionalTypedRows : List ConditionalTypedRow :=
  [ .twoDDPForCTRS
  , .operationalTerminationCTRS
  , .integerTermRewriting
  , .lctrs
  , .higherOrderLCTRS
  , .horpoAdmittance
  , .cpoAdmittance
  , .generalSchemaAdmittance
  , .sizedTypesAdmittance
  , .coqGuardAdmittance
  , .bellantoniCookSplit
  , .linearLogicTypingBarrier
  , .ramifiedRecursionTypingBarrier
  ]

/--
Proves: the 13-row T7 ledger has exactly 13 entries.
Does not prove: anything about the contents beyond the count.
Relation: aggregator over `RDRSMethodFamily` enum; not a concrete
  rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` on the literal `List` length.
Scope: the 13-row T7 ledger.
-/
theorem conditionalTypedRows_length :
    conditionalTypedRows.length = 13 := by decide

/--
Proves: the 13-row T7 ledger has no duplicate row.
Does not prove: anything about row order or content.
Relation: aggregator; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` on the literal `List.Nodup`.
Scope: the 13-row T7 ledger.
-/
theorem conditionalTypedRows_nodup :
    conditionalTypedRows.Nodup := by decide

/--
Proves: every constructor of `ConditionalTypedRow` appears in the
  13-row T7 ledger.
Does not prove: row order or count.
Relation: aggregator; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` (case-split on the finite enum).
Scope: the `ConditionalTypedRow` enum.
-/
theorem conditionalTypedRows_complete :
    ∀ row : ConditionalTypedRow, row ∈ conditionalTypedRows := by
  intro row
  cases row <;> decide

/--
Proves: `rowStatus` is total on `ConditionalTypedRow` (every row has
  a terminal `RDRSMethodStatus` value).
Does not prove: which specific status each row receives; that is
  handled by the per-row status-pin theorems below.
Relation: aggregator; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `row : ConditionalTypedRow`.
-/
theorem rowStatus_terminal (row : ConditionalTypedRow) :
    ∃ status : RDRSMethodStatus, rowStatus row = status :=
  ⟨rowStatus row, rfl⟩

/-! ## Per-row status-match theorems

Each row's `statusOf` is pinned by `rfl` so any change to the atlas's
terminal status mapping for these rows breaks elaboration here. -/

theorem twoDDPForCTRS_status :
    rowStatus .twoDDPForCTRS = .conditional_escape := rfl

theorem operationalTerminationCTRS_status :
    rowStatus .operationalTerminationCTRS = .import_dependent := rfl

theorem integerTermRewriting_status :
    rowStatus .integerTermRewriting = .conditional_escape := rfl

theorem lctrs_status :
    rowStatus .lctrs = .conditional_escape := rfl

theorem higherOrderLCTRS_status :
    rowStatus .higherOrderLCTRS = .conditional_escape := rfl

theorem horpoAdmittance_status :
    rowStatus .horpoAdmittance = .definitional_admitter := rfl

theorem cpoAdmittance_status :
    rowStatus .cpoAdmittance = .definitional_admitter := rfl

theorem generalSchemaAdmittance_status :
    rowStatus .generalSchemaAdmittance = .definitional_admitter := rfl

theorem sizedTypesAdmittance_status :
    rowStatus .sizedTypesAdmittance = .definitional_admitter := rfl

theorem coqGuardAdmittance_status :
    rowStatus .coqGuardAdmittance = .definitional_admitter := rfl

theorem bellantoniCookSplit_status :
    rowStatus .bellantoniCookSplit = .conditional_barrier := rfl

theorem linearLogicTypingBarrier_status :
    rowStatus .linearLogicTypingBarrier = .conditional_barrier := rfl

theorem ramifiedRecursionTypingBarrier_status :
    rowStatus .ramifiedRecursionTypingBarrier = .conditional_barrier := rfl

/-! ## Mechanism classification theorems -/

theorem twoDDPForCTRS_mechanism :
    rowMechanism .twoDDPForCTRS = .conditionalEscape := rfl

theorem operationalTerminationCTRS_mechanism :
    rowMechanism .operationalTerminationCTRS = .importDependent := rfl

theorem integerTermRewriting_mechanism :
    rowMechanism .integerTermRewriting = .conditionalEscape := rfl

theorem lctrs_mechanism :
    rowMechanism .lctrs = .conditionalEscape := rfl

theorem higherOrderLCTRS_mechanism :
    rowMechanism .higherOrderLCTRS = .conditionalEscape := rfl

theorem horpoAdmittance_mechanism :
    rowMechanism .horpoAdmittance = .definitionalAdmitter := rfl

theorem cpoAdmittance_mechanism :
    rowMechanism .cpoAdmittance = .definitionalAdmitter := rfl

theorem generalSchemaAdmittance_mechanism :
    rowMechanism .generalSchemaAdmittance = .definitionalAdmitter := rfl

theorem sizedTypesAdmittance_mechanism :
    rowMechanism .sizedTypesAdmittance = .definitionalAdmitter := rfl

theorem coqGuardAdmittance_mechanism :
    rowMechanism .coqGuardAdmittance = .definitionalAdmitter := rfl

theorem bellantoniCookSplit_mechanism :
    rowMechanism .bellantoniCookSplit = .typingBarrierWithHypothesis := rfl

theorem linearLogicTypingBarrier_mechanism :
    rowMechanism .linearLogicTypingBarrier = .typingBarrierWithHypothesis := rfl

theorem ramifiedRecursionTypingBarrier_mechanism :
    rowMechanism .ramifiedRecursionTypingBarrier = .typingBarrierWithHypothesis := rfl

/-! ## Typing-barrier hypotheses (explicit per dispatch boundary) -/

theorem bellantoniCookSplit_hypothesis :
    typingBarrierHypothesis .bellantoniCookSplit =
      some .nonDuplicatingFragment := rfl

theorem linearLogicTypingBarrier_hypothesis :
    typingBarrierHypothesis .linearLogicTypingBarrier =
      some .linearityForbidsDuplication := rfl

theorem ramifiedRecursionTypingBarrier_hypothesis :
    typingBarrierHypothesis .ramifiedRecursionTypingBarrier =
      some .ramificationForbidsCrossLevel := rfl

/--
Proves: every row whose mechanism is NOT `typingBarrierWithHypothesis`
  carries `none` as its `typingBarrierHypothesis`.
Does not prove: anything about typing-barrier rows; that is the
  next theorem.
Relation: aggregator over the 13-row T7 ledger; not a concrete
  rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` (case-split on the finite enum).
Scope: every `row : ConditionalTypedRow`.
-/
theorem non_typing_barrier_rows_have_no_hypothesis (row : ConditionalTypedRow) :
    rowMechanism row ≠ .typingBarrierWithHypothesis →
    typingBarrierHypothesis row = none := by
  cases row <;> decide

/--
Proves: every row whose mechanism IS `typingBarrierWithHypothesis`
  carries a non-`none` `typingBarrierHypothesis`.
Does not prove: which specific `TypingBarrierHypothesis` value each
  row receives; that is handled by the three per-row hypothesis-pin
  theorems above.
Relation: aggregator; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` (case-split on the finite enum).
Scope: every `row : ConditionalTypedRow`.
-/
theorem typing_barrier_rows_have_hypothesis (row : ConditionalTypedRow) :
    rowMechanism row = .typingBarrierWithHypothesis →
    typingBarrierHypothesis row ≠ none := by
  cases row <;> decide

/--
Proves: row-level mechanism and `statusOf`-status are aligned across
  the 13-row T7 ledger: definitionalAdmitter → definitional_admitter,
  typingBarrierWithHypothesis → conditional_barrier, conditionalEscape
  → conditional_escape, importDependent → import_dependent.
Does not prove: that every status maps from exactly one mechanism
  (the converse direction is not asserted; some mechanisms are
  represented by multiple rows of the same status, etc.).
Relation: aggregator; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `decide` (case-split on the finite enum).
Scope: every `row : ConditionalTypedRow`; mechanism and status both
  read from the `rowMechanism` and `rowStatus` defs above.
-/
theorem mechanism_status_alignment (row : ConditionalTypedRow) :
    (rowMechanism row = .definitionalAdmitter →
        rowStatus row = .definitional_admitter) ∧
    (rowMechanism row = .typingBarrierWithHypothesis →
        rowStatus row = .conditional_barrier) ∧
    (rowMechanism row = .conditionalEscape →
        rowStatus row = .conditional_escape) ∧
    (rowMechanism row = .importDependent →
        rowStatus row = .import_dependent) := by
  cases row <;> decide

/-- Packed closure certificate for the T7 layer. -/
structure ConditionalTypedAtlasClosed : Prop where
  allRowsListed :
    ∀ row : ConditionalTypedRow, row ∈ conditionalTypedRows
  noDuplicateRows : conditionalTypedRows.Nodup
  exactRowCount : conditionalTypedRows.length = 13
  allStatusesTerminal :
    ∀ row : ConditionalTypedRow,
      ∃ status : RDRSMethodStatus, rowStatus row = status
  mechanismStatusAligned :
    ∀ row : ConditionalTypedRow,
      (rowMechanism row = .definitionalAdmitter →
          rowStatus row = .definitional_admitter) ∧
      (rowMechanism row = .typingBarrierWithHypothesis →
          rowStatus row = .conditional_barrier) ∧
      (rowMechanism row = .conditionalEscape →
          rowStatus row = .conditional_escape) ∧
      (rowMechanism row = .importDependent →
          rowStatus row = .import_dependent)
  typingBarrierRowsCarryHypothesis :
    ∀ row : ConditionalTypedRow,
      rowMechanism row = .typingBarrierWithHypothesis →
        typingBarrierHypothesis row ≠ none
  bellantoniCookHypothesisExplicit :
    typingBarrierHypothesis .bellantoniCookSplit = some .nonDuplicatingFragment
  linearLogicHypothesisExplicit :
    typingBarrierHypothesis .linearLogicTypingBarrier =
      some .linearityForbidsDuplication
  ramifiedRecursionHypothesisExplicit :
    typingBarrierHypothesis .ramifiedRecursionTypingBarrier =
      some .ramificationForbidsCrossLevel

/--
Proves: the T7 conditional/typed-atlas layer is closed, packing all
  thirteen aggregate witnesses (rows listed, no duplicates, exact
  count = 13, statuses terminal, mechanism/status aligned, typing-
  barrier rows carry hypotheses, three named hypothesis equalities)
  into one Prop.
Does not prove: any property beyond the conjunction of the aggregate
  witnesses; no new mathematical content is introduced at this layer.
Relation: aggregator over the 13-row T7 ledger and the 76-row
  `RDRSMethodFamily` enum; not a concrete rewriting relation.
Closure: not applicable (aggregator).
Strategy: not applicable.
Trust: kernel-only. Every field is `:=` to a named aggregate theorem;
  no `decide`, `native_decide`, or external trust appears in this
  constructor.
Scope: the 13-row T7 ledger.
-/
theorem rdrs_conditional_typed_layer_closed : ConditionalTypedAtlasClosed where
  allRowsListed := conditionalTypedRows_complete
  noDuplicateRows := conditionalTypedRows_nodup
  exactRowCount := conditionalTypedRows_length
  allStatusesTerminal := rowStatus_terminal
  mechanismStatusAligned := mechanism_status_alignment
  typingBarrierRowsCarryHypothesis := typing_barrier_rows_have_hypothesis
  bellantoniCookHypothesisExplicit := bellantoniCookSplit_hypothesis
  linearLogicHypothesisExplicit := linearLogicTypingBarrier_hypothesis
  ramifiedRecursionHypothesisExplicit := ramifiedRecursionTypingBarrier_hypothesis

end OperatorKO7.RDRSConditionalTypedAtlas
