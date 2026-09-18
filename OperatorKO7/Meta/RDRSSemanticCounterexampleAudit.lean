import OperatorKO7.Meta.RDRSSemanticClassifier
import OperatorKO7.Meta.RDRSSemanticRawUniversalAdjudication
import OperatorKO7.Meta.RDRSSemanticProjectionTransactionAudit

set_option autoImplicit false

/-!
# RDRS Semantic Counterexample Audit (Milestone S6)

Roadmap source:
`OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S6 -- Exhaustiveness Against Known Semantic Escapes.

Classifies the nine known reviewer counterexample / escape rows
required by the roadmap against the S5 classifier's six labels. The
audit produces a closed coverage table with `decide`-proved bucket
counts and a zero-residual `TEMPORARY_UNCLASSIFIED` proof.

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  closed enum of nine audit rows; not a rewriting relation.
Closure:   N/A.
Strategy:  not applicable.
Trust:     kernel-only.
Scope:     nine roadmap-mandated rows. The classification of each row
           is justified in this docstring by the structural shape of
           the row's evidence kind; the audit does NOT prove an SN
           or full-DP claim for any row. No `Prop := True`
           exclusions, no fake directness evidence, no semantic
           quotient counted as projection escape.
```

## Row dispositions

```
[row]                                 [class]                                     [why]
counterFirstLex                        SemanticNotDirect                            payload-blind alternative orients
                                                                                     (counter-only descent); not decisive
                                                                                     payload-sensitive (S2 proved).
termAlgebraRewriteClosure              SemanticNotDirect                            term-algebra / rewrite-closure
                                                                                     oracle excluded by SemanticDirectMeasure
                                                                                     directness gate.
nonlinearCounterPayloadCoupling        SemanticNotDirect                            nonlinear payload coupling outside
                                                                                     direct-discipline grammar.
dpProjection                           SemanticProjectionTransactionEscape          backed by the S6.5 real payload-
                                                                                     forgetting projection of counterFirstLex_R
                                                                                     (pi = Prod.fst, with honest seed-collapse
                                                                                     and projected orientation). Not source-side
                                                                                     direct descent; not a full DP-soundness
                                                                                     theorem.
argumentFiltering                      SemanticProjectionTransactionEscape          argument filtering coincides with the same
                                                                                     payload-forgetting projection on
                                                                                     counterFirstLex_R (filter second
                                                                                     coordinate). Backed by the S6.5
                                                                                     not-plain-erasure shape (sigma + phi + wf +
                                                                                     projected orientation).
fullMonotoneAlgebra                    SemanticConstructionEscape                   monotone-algebra interpretation is a
                                                                                     construction, not a closed-grammar
                                                                                     direct measure.
mspoWitness                            SemanticConstructionEscape                   MSPO is a path-order construction,
                                                                                     not in the direct grammar.
fullWpoGwpoWitness                     SemanticConstructionEscape                   WPO / gWPO is a weighted path-order
                                                                                     construction, not in the direct
                                                                                     grammar.
semanticLabeling                       SemanticTransformEscape                      labeling renames symbols (transforms
                                                                                     the system); not a source-side direct
                                                                                     measure.
```

K-check 7 honesty: each row classification is about which CLASSIFIER
BRANCH the shape lands in, not about source-system SN. The
`projectionEscape` rows do not claim source SN; they claim the row
produces a static projection-transaction shape (cf. S4 / U3
`dpWitnessTransport_sound`). The `construction` and `transform` rows
are not in the direct-payload-sensitive grammar at all; the
`notDirect` rows fail the directness gate.
-/

namespace OperatorKO7.RDRSSemanticCounterexampleAudit

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticClassifier
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticProjectionTransaction
open OperatorKO7.RDRSSemanticRawUniversalAdjudication
open OperatorKO7.RDRSSemanticProjectionTransactionAudit
open OperatorKO7.RDRSSeedCollapse

/-! ### Audit row enum -/

/--
Proves: closed enum of the nine roadmap-mandated audit rows.
Does not prove: any property of the rows beyond their identity.
Relation: enum metadata; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive with nine constants.
-/
inductive SemanticAuditRow where
  | counterFirstLex
  | termAlgebraRewriteClosure
  | nonlinearCounterPayloadCoupling
  | dpProjection
  | argumentFiltering
  | fullMonotoneAlgebra
  | mspoWitness
  | fullWpoGwpoWitness
  | semanticLabeling
  deriving DecidableEq, Repr

/--
Proves: classification function from `SemanticAuditRow` to the S5
  `SemanticCertificateClass`. Each row is mapped to exactly one
  productive label; no row maps to `TEMPORARY_UNCLASSIFIED`.
Does not prove: that the classified label is the "correct" one in
  any semantic sense beyond the structural shape recorded in the
  module header.
Relation: closed enum projection.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`match`).
Scope: closed.
-/
def auditClassify : SemanticAuditRow → SemanticCertificateClass
  | .counterFirstLex                  => .SemanticNotDirect
  | .termAlgebraRewriteClosure        => .SemanticNotDirect
  | .nonlinearCounterPayloadCoupling  => .SemanticNotDirect
  | .dpProjection                     => .SemanticProjectionTransactionEscape
  | .argumentFiltering                => .SemanticProjectionTransactionEscape
  | .fullMonotoneAlgebra              => .SemanticConstructionEscape
  | .mspoWitness                      => .SemanticConstructionEscape
  | .fullWpoGwpoWitness               => .SemanticConstructionEscape
  | .semanticLabeling                 => .SemanticTransformEscape

/--
Proves: the canonical list of all nine audit rows.
Does not prove: anything about the rows beyond their enumeration.
Relation: data definition.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed list of nine entries.
-/
def allAuditRows : List SemanticAuditRow :=
  [ .counterFirstLex,
    .termAlgebraRewriteClosure,
    .nonlinearCounterPayloadCoupling,
    .dpProjection,
    .argumentFiltering,
    .fullMonotoneAlgebra,
    .mspoWitness,
    .fullWpoGwpoWitness,
    .semanticLabeling ]

/-! ### Per-bucket extractors -/

/-- Rows classified `SemanticPayloadSensitiveBlocked`. -/
def blockedRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked)

/-- Rows classified `SemanticProjectionTransactionEscape`. -/
def projectionEscapeRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.SemanticProjectionTransactionEscape)

/-- Rows classified `SemanticConstructionEscape`. -/
def constructionEscapeRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.SemanticConstructionEscape)

/-- Rows classified `SemanticTransformEscape`. -/
def transformEscapeRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.SemanticTransformEscape)

/-- Rows classified `SemanticNotDirect`. -/
def notDirectRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.SemanticNotDirect)

/-- Rows classified `TEMPORARY_UNCLASSIFIED` (must be empty). -/
def temporaryUnclassifiedRows : List SemanticAuditRow :=
  allAuditRows.filter
    (fun r => auditClassify r ==
      SemanticCertificateClass.TEMPORARY_UNCLASSIFIED)

/-! ### Bucket counts (`decide`-proved) -/

/--
Proves: nine total audit rows.
Does not prove: anything beyond the count.
Relation: list length.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: closed list.
-/
theorem allAuditRows_length : allAuditRows.length = 9 := by decide

/-- Blocked rows count: 0 (no S6 row is a decisive payload-sensitive
descent; all S3-barrier instances are handled by manuscript /
LEDGER, not by the counterexample audit). -/
theorem blockedRows_length : blockedRows.length = 0 := by decide

/-- Projection-escape rows count: 2 (`dpProjection`, `argumentFiltering`). -/
theorem projectionEscapeRows_length : projectionEscapeRows.length = 2 := by decide

/-- Construction-escape rows count: 3 (`fullMonotoneAlgebra`,
`mspoWitness`, `fullWpoGwpoWitness`). -/
theorem constructionEscapeRows_length : constructionEscapeRows.length = 3 := by decide

/-- Transform-escape rows count: 1 (`semanticLabeling`). -/
theorem transformEscapeRows_length : transformEscapeRows.length = 1 := by decide

/-- Not-direct rows count: 3 (`counterFirstLex`,
`termAlgebraRewriteClosure`, `nonlinearCounterPayloadCoupling`). -/
theorem notDirectRows_length : notDirectRows.length = 3 := by decide

/-- Temporary-unclassified rows count: 0 (zero residual). -/
theorem temporaryUnclassifiedRows_length :
    temporaryUnclassifiedRows.length = 0 := by decide

/--
Proves: the six bucket counts partition the nine audit rows
  (`0 + 2 + 3 + 1 + 3 + 0 = 9`).
Does not prove: anything beyond the arithmetic identity.
Relation: list-length arithmetic.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: closed list.
-/
theorem audit_partition_total :
    blockedRows.length + projectionEscapeRows.length
      + constructionEscapeRows.length + transformEscapeRows.length
      + notDirectRows.length + temporaryUnclassifiedRows.length = 9 := by
  decide

/-! ### Totality and zero-unclassified for the audit pass -/

/--
Proves: every audit row classifies into one of the five productive
  labels. The classifier is total over the audit row enum.
Does not prove: that arbitrary Lean evidence behind a row classifies;
  only that the row identifier itself does.
Relation: closed-enum partition.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: every `r : SemanticAuditRow`.
-/
theorem audit_classify_total (r : SemanticAuditRow) :
    auditClassify r = SemanticCertificateClass.SemanticPayloadSensitiveBlocked
      ∨ auditClassify r =
          SemanticCertificateClass.SemanticProjectionTransactionEscape
      ∨ auditClassify r =
          SemanticCertificateClass.SemanticConstructionEscape
      ∨ auditClassify r =
          SemanticCertificateClass.SemanticTransformEscape
      ∨ auditClassify r =
          SemanticCertificateClass.SemanticNotDirect := by
  cases r <;> decide

/--
Proves: no audit row is classified `TEMPORARY_UNCLASSIFIED`.
Does not prove: anything stronger about the classifications.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: every `r : SemanticAuditRow`.
-/
theorem audit_no_temporary_unclassified (r : SemanticAuditRow) :
    auditClassify r ≠ SemanticCertificateClass.TEMPORARY_UNCLASSIFIED := by
  cases r <;> decide

/-! ### Per-row classification theorems (`rfl`) -/

/-- `counterFirstLex` is classified `SemanticNotDirect`. -/
theorem counterFirstLex_class :
    auditClassify .counterFirstLex =
      SemanticCertificateClass.SemanticNotDirect := rfl

/-- `termAlgebraRewriteClosure` is classified `SemanticNotDirect`. -/
theorem termAlgebraRewriteClosure_class :
    auditClassify .termAlgebraRewriteClosure =
      SemanticCertificateClass.SemanticNotDirect := rfl

/-- `nonlinearCounterPayloadCoupling` is classified `SemanticNotDirect`. -/
theorem nonlinearCounterPayloadCoupling_class :
    auditClassify .nonlinearCounterPayloadCoupling =
      SemanticCertificateClass.SemanticNotDirect := rfl

/-- `dpProjection` is classified `SemanticProjectionTransactionEscape`. -/
theorem dpProjection_class :
    auditClassify .dpProjection =
      SemanticCertificateClass.SemanticProjectionTransactionEscape := rfl

/-- `argumentFiltering` is classified `SemanticProjectionTransactionEscape`. -/
theorem argumentFiltering_class :
    auditClassify .argumentFiltering =
      SemanticCertificateClass.SemanticProjectionTransactionEscape := rfl

/-- `fullMonotoneAlgebra` is classified `SemanticConstructionEscape`. -/
theorem fullMonotoneAlgebra_class :
    auditClassify .fullMonotoneAlgebra =
      SemanticCertificateClass.SemanticConstructionEscape := rfl

/-- `mspoWitness` is classified `SemanticConstructionEscape`. -/
theorem mspoWitness_class :
    auditClassify .mspoWitness =
      SemanticCertificateClass.SemanticConstructionEscape := rfl

/-- `fullWpoGwpoWitness` is classified `SemanticConstructionEscape`. -/
theorem fullWpoGwpoWitness_class :
    auditClassify .fullWpoGwpoWitness =
      SemanticCertificateClass.SemanticConstructionEscape := rfl

/-- `semanticLabeling` is classified `SemanticTransformEscape`. -/
theorem semanticLabeling_class :
    auditClassify .semanticLabeling =
      SemanticCertificateClass.SemanticTransformEscape := rfl

/-! ### Capstone closeout -/

/--
Proves: closeout structure for the S6 audit. Bundles totality, zero
  residual, the six bucket counts, the partition equality, and the
  total row count into a single `Prop`.
Does not prove: any property of arbitrary Lean evidence behind a
  row.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the closed nine-row audit.
-/
structure SemanticCounterexampleAuditClosed : Prop where
  totality :
    ∀ r : SemanticAuditRow,
      auditClassify r =
          SemanticCertificateClass.SemanticPayloadSensitiveBlocked
        ∨ auditClassify r =
            SemanticCertificateClass.SemanticProjectionTransactionEscape
        ∨ auditClassify r =
            SemanticCertificateClass.SemanticConstructionEscape
        ∨ auditClassify r =
            SemanticCertificateClass.SemanticTransformEscape
        ∨ auditClassify r =
            SemanticCertificateClass.SemanticNotDirect
  zeroResidual :
    ∀ r : SemanticAuditRow,
      auditClassify r ≠ SemanticCertificateClass.TEMPORARY_UNCLASSIFIED
  blockedCount             : blockedRows.length = 0
  projectionEscapeCount    : projectionEscapeRows.length = 2
  constructionEscapeCount  : constructionEscapeRows.length = 3
  transformEscapeCount     : transformEscapeRows.length = 1
  notDirectCount           : notDirectRows.length = 3
  temporaryCount           : temporaryUnclassifiedRows.length = 0
  partitionTotal           :
    blockedRows.length + projectionEscapeRows.length
      + constructionEscapeRows.length + transformEscapeRows.length
      + notDirectRows.length + temporaryUnclassifiedRows.length = 9
  rowCount                 : allAuditRows.length = 9

/--
Proves: the S6 audit is closed. All nine rows classify into a
  productive label; the residual is zero; the bucket counts agree
  with `decide`-proved arithmetic.
Does not prove: source-system SN for any row; the audit is at the
  classifier layer only.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (each field is `decide`-proved or `rfl`).
Scope: the closed nine-row audit.
-/
theorem semantic_counterexample_audit_closed :
    SemanticCounterexampleAuditClosed where
  totality                  := audit_classify_total
  zeroResidual              := audit_no_temporary_unclassified
  blockedCount              := blockedRows_length
  projectionEscapeCount     := projectionEscapeRows_length
  constructionEscapeCount   := constructionEscapeRows_length
  transformEscapeCount      := transformEscapeRows_length
  notDirectCount            := notDirectRows_length
  temporaryCount            := temporaryUnclassifiedRows_length
  partitionTotal            := audit_partition_total
  rowCount                  := allAuditRows_length

/-- Audit anchor for the S6 counterexample-audit surface. -/
def rdrs_semantic_counterexample_audit_anchor : String :=
  "OperatorKO7.RDRSSemanticCounterexampleAudit.semantic_counterexample_audit_closed"

/--
Proves: the `counterFirstLex` row is backed by the actual S2 worked
  instance; it is raw payload-sensitive but not decisive payload-sensitive.
Does not prove: that every counter-first lex variant has the same
  classification.
Relation: concrete `counterFirstLex_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named S6 audit row only.
-/
theorem counterFirstLex_row_evidence :
    auditClassify .counterFirstLex =
        SemanticCertificateClass.SemanticNotDirect ∧
      PayloadSensitiveRaw
        OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_R
        OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_M ∧
      ¬ PayloadSensitiveDecisive
        OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_R
        OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_M := by
  refine ⟨rfl, ?_⟩
  exact
    OperatorKO7.RDRSSemanticPayloadSensitivity.counter_first_lex_is_raw_payload_sensitive_not_decisive_payload_sensitive

/--
Proves: the term-algebra rewrite-closure row is backed by the S0 raw
  semantic countermodel's orientation theorem, while the row is classified
  outside the direct branch.
Does not prove: that arbitrary term-algebra witnesses fail directness;
  S1 treats directness as certificate evidence.
Relation: S0 raw semantic countermodel.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: named S6 audit row.
-/
theorem termAlgebraRewriteClosure_row_evidence :
    auditClassify .termAlgebraRewriteClosure =
        SemanticCertificateClass.SemanticNotDirect ∧
      Orients termAlgebraOracle_R
        termAlgebraOracle_M.μ
        termAlgebraOracle_M.ltA := by
  exact ⟨rfl, termAlgebraOracle_orients⟩

/--
Proves: the nonlinear counter-payload coupling row is backed by the S0
  raw semantic countermodel's orientation theorem and is classified outside
  the direct branch.
Does not prove: a general theorem over all nonlinear couplings.
Relation: S0 raw semantic countermodel.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: named S6 audit row.
-/
theorem nonlinearCounterPayloadCoupling_row_evidence :
    auditClassify .nonlinearCounterPayloadCoupling =
        SemanticCertificateClass.SemanticNotDirect ∧
      Orients nonlinearCouple_R
        nonlinearCouple_M.μ
        nonlinearCouple_M.ltA := by
  exact ⟨rfl, nonlinearCouple_orients⟩

/--
Proves: the DP projection row has projection-transaction class and is
  backed by the **real payload-forgetting projection** of
  `counterFirstLex_R`: `pi = Prod.fst` genuinely forgets the payload
  coordinate, the seed-collapse `(carrier n = (n, 0); collapse (n, _)
  = n)` records the forgetting, and the projected order is the
  well-founded `Nat.lt`. The row is witnessed by the S6.5 audit's
  `counterFirstLex_dpSemanticTransactionEscape` and the witness-
  transport content (`lifted_orients`) discharging the source-step
  orientation transport.
Does not prove: source-system SN, full DP-framework soundness, or any
  claim about other DP projections; the row is backed by ONE concrete
  payload-forgetting projection of `counterFirstLex_R`. Per the S6.5
  roadmap, this replaces the previous `trivialNatStep` placeholder
  evidence in which `pi = id` did not actually forget anything.
Relation: `counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step orientation.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named S6 audit row only.
-/
theorem dpProjection_row_evidence :
    auditClassify .dpProjection =
        SemanticCertificateClass.SemanticProjectionTransactionEscape ∧
      Orients
        OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_R
        counterFirstLex_dpSemanticTransactionEscape.liftedMeasure
        counterFirstLex_dpSemanticTransactionEscape.transaction.semanticMeasure.ltA :=
  ⟨rfl, counterFirstLex_dpSemanticTransactionEscape.lifted_orients⟩

/--
Proves: the argument-filtering row has projection-transaction class
  and is backed by the same payload-forgetting projection of
  `counterFirstLex_R` (argument filtering and DP projection coincide on
  the canonical `counterFirstLex_R` witness: filtering the second
  argument is exactly `pi = Prod.fst`). The witness exposes a
  non-vacuous semantic projection-transaction escape in the strict
  S4 sense, including all four obligations (sigma, phi, wf, projected
  orientation) per
  `semantic_projection_transaction_escape_sound_hardened`.
Does not prove: a general theorem over arbitrary argument-filtering
  schemes; only the canonical `counterFirstLex_R` instance.
Relation: `counterFirstLex_R : RDRSStep Unit Nat Nat (Nat × Nat)`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: the named S6 audit row only.
-/
theorem argumentFiltering_row_evidence :
    auditClassify .argumentFiltering =
        SemanticCertificateClass.SemanticProjectionTransactionEscape ∧
      (Nonempty (SemanticMeasureData
        counterFirstLex_dpSemanticTransactionEscape.transaction.T') ∧
      (∃ (PayloadCarrier : Type)
          (sc : SeedCollapse PayloadCarrier (Nat × Nat)),
          Nonempty (FactorsThroughSeedCollapse sc
            counterFirstLex_dpSemanticTransactionEscape.transaction.pi)) ∧
      WellFounded
        counterFirstLex_dpSemanticTransactionEscape.transaction.semanticMeasure.ltA ∧
      Orients
        counterFirstLex_dpSemanticTransactionEscape.transaction.Rproj
        counterFirstLex_dpSemanticTransactionEscape.transaction.semanticMeasure.μ
        counterFirstLex_dpSemanticTransactionEscape.transaction.semanticMeasure.ltA) :=
  ⟨rfl,
    semantic_projection_escape_not_plain_erasure
      counterFirstLex_dpSemanticTransactionEscape⟩

end OperatorKO7.RDRSSemanticCounterexampleAudit
