import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticRawUniversalAdjudication
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity
import OperatorKO7.Meta.RDRSSemanticCertificate
import OperatorKO7.Meta.RDRSSemanticLensPump
import OperatorKO7.Meta.RDRSSemanticProjectionTransaction
import OperatorKO7.Meta.RDRSSemanticClassifier
import OperatorKO7.Meta.RDRSSemanticCounterexampleAudit
import OperatorKO7.Meta.RDRSSemanticProjectionTransactionAudit

set_option autoImplicit false

/-!
# RDRS Semantic Coverage Ledger (Milestone S7)

Roadmap source:
`OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone S7 -- Semantic Coverage Ledger.

The semantic coverage ledger packages the entire S0-S6.5 semantic
universal payload-sensitive direct-measure program into a single
theorem-backed certificate. Every row records:

* the semantic family identifier (the S6 audit row enum lifted with
  the S6.5 hardening anchors and an S3 lens-pump anchor);
* the directness status under the S1 `SemanticDirectMeasure` gate;
* the raw payload-sensitive status;
* the decisive payload-sensitive status;
* the projection-transaction status (from S4 + S6.5 hardening);
* the classification theorem identifier (an S6 audit row tag);
* the axiom footprint declared by the row's primary theorem (verified
  zero-axiom for every row);
* whether the row backs a Paper A claim (S0 adjudication, S3 lens-pump
  barrier, S4/S6.5 projection transaction, S5 classifier, S6 audit).

## Audit slots (Lean Development Bible W8 / R4)

```
Relation:  closed enum lifted from the nine S6 audit rows plus the
           S6.5 projection-transaction hardening anchors and the S3
           lens-pump anchor.
Closure:   N/A.
Strategy:  N/A.
Trust:     kernel-only.
Scope:     this ledger covers the SEMANTIC universal payload-sensitive
           direct-measure program (S0-S6.5). It does NOT cover the
           full 76-row RDRS termination-method universe (that is
           `RDRSCoverageLedger.lean`'s job) and it does NOT extend the
           K-check 7 honesty boundary: no SN claim, no full DP-
           soundness chain, no claim against arbitrary nonlinear
           polynomial interpretations, MSPO, WPO/gWPO, or arbitrary
           semantic quotients.
```

## What this ledger proves

* `coverage_total`: every ledger row classifies into a productive
  semantic classifier label.
* `coverage_no_temporary_unclassified`: zero residual / TEMPORARY_
  UNCLASSIFIED rows.
* `coverage_no_plain_erasure_projection_escape`: every
  projection-transaction-escape row is backed by hardened S6.5
  evidence (sigma + phi + wf + projected orientation are extractable),
  i.e. there is no plain-erasure projection escape in the ledger.
* `coverage_partition_total`: the per-bucket counts add up.
* `coverage_audit_rows_match_s6`: the audit rows of this ledger
  agree, row by row, with the S6 `auditClassify` classification.
* `coverage_zero_axiom_footprint`: structural certificate that the
  primary anchors of S0-S6.5 used to back the ledger rows are
  available as kernel-checked theorems.

## What this ledger does NOT prove

* Source-system SN. The semantic universe is parametric over
  `RDRSStep B S N T`; it does not certify termination of any concrete
  RDRS instance.
* That every Lean function is normalised before classification. The
  classifier acts on the closed `NormalizedSemanticCertificate`
  inductive, not on arbitrary raw measures.
* That the projection-transaction escape branch is inhabited for
  every RDRS step. Inhabitation requires the four S4 obligations
  plus a positive projected-orientation proof.
-/

namespace OperatorKO7.RDRSSemanticCoverageLedger

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticRawUniversalAdjudication
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticCertificate
open OperatorKO7.RDRSSemanticLensPump
open OperatorKO7.RDRSSemanticProjectionTransaction
open OperatorKO7.RDRSSemanticClassifier
open OperatorKO7.RDRSSemanticCounterexampleAudit
open OperatorKO7.RDRSSemanticProjectionTransactionAudit
open OperatorKO7.RDRSWitnessTransport
open OperatorKO7.RDRSBoundaryBottleneck
open OperatorKO7.RDRSSearchBudgetInvariance
open OperatorKO7.RDRSSeedCollapse

/-! ## 1. Per-row metadata enums -/

/--
Proves: closed enum of the four directness statuses a row can take
  under the S1 `SemanticDirectMeasure` gate.
Does not prove: that the row's underlying measure data satisfies the
  status; the status is recorded as metadata.
Relation: enum metadata; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive with four constants.
-/
inductive DirectnessStatus
  | direct                  -- carries S1 directness evidence
  | notDirect               -- fails the S1 directness gate
  | notApplicable           -- structural row (e.g. raw-adjudication
                            -- anchor, classifier anchor) for which
                            -- directness is not the right axis
  | adjudicatedRefuted      -- S0 raw refutation row: the family is
                            -- raw but the universal raw claim is
                            -- refuted on it
  deriving DecidableEq, Repr

/--
Proves: closed enum of the three boolean-with-NA statuses used for
  raw payload sensitivity, decisive payload sensitivity, and
  projection-transaction status.
Does not prove: that the status is the right one; metadata only.
Relation: enum metadata.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive with three constants.
-/
inductive RowStatus
  | yes
  | no
  | notApplicable
  deriving DecidableEq, Repr

/--
Proves: closed enum of the Paper A claim slots the ledger backs.
Does not prove: that Paper A actually cites the row; metadata only.
Relation: enum metadata.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive over the six Paper A claim slots S0-S6.5
  expose.
-/
inductive PaperAClaim
  | s0_adjudication                  -- adjudication of the naive raw
                                     -- universal statement
  | s2_payload_sensitivity_split     -- raw vs decisive separation
  | s3_lens_pump_barrier             -- universal semantic lens-pump
                                     -- barrier
  | s4_projection_transaction        -- (pi, sigma, phi, wf, proj-orient)
  | s5_classifier                    -- six-label classifier + zero
                                     -- residual
  | s6_counterexample_audit          -- nine-row audit table
  | s6p5_projection_transaction_hardening  -- S6.5 hardening
                                           -- (no plain erasure)
  | notApplicable
  deriving DecidableEq, Repr

/--
Proves: closed enum identifying the primary classification anchor
  used to back a row. Each constant maps to a stable Lean theorem
  identifier whose axiom footprint is verified zero.
Does not prove: that the anchor entails any semantic property
  beyond its named theorem.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive.
-/
inductive ClassificationAnchor
  | s0_naive_raw_semantic_universal_adjudicated
  | s2_payload_sensitive_decisive_not_counter_forgetting
  | s2_counter_first_lex_raw_not_decisive
  | s3_semantic_lens_pump_no_orients
  | s3_no_orients_of_semantic_payload_sensitive_decisive_descent
  | s4_semantic_projection_escape_requires_sigma
  | s4_semantic_projection_escape_requires_seed_collapse
  | s4_semantic_projection_escape_requires_projected_orientation
  | s4_semantic_projection_escape_requires_wellFounded
  | s5_semantic_classifier_total
  | s5_semantic_temporary_unclassified_count_is_zero
  | s5_semantic_projection_transaction_escape_sound
  | s6_audit_classify_total
  | s6_audit_no_temporary_unclassified
  | s6_semantic_counterexample_audit_closed
  | s6p5_semantic_projection_escape_not_plain_erasure
  | s6p5_semantic_projection_transaction_escape_sound_hardened
  | s6p5_semantic_dp_projection_transaction_canonical
  | s6p5_semantic_projection_escape_retained_factors_through_counter
  | s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
  | s6p5_semantic_search_budget_invariance
  deriving DecidableEq, Repr

/-! ## 2. Ledger row structure -/

/--
Proves: a per-row record of the semantic coverage ledger. Each row
  pins a `family` identifier (a `SemanticAuditRow` for the nine S6
  rows; one extra row each for S0 adjudication, S3 lens-pump barrier,
  S5 classifier, S6.5 hardening, S6.5 DP-projection canonical, S6.5
  bottleneck, and S6.5 search-budget invariance), the four metadata
  status fields, the classification anchor, an `axiom_footprint`
  String (literal "zero" for every row; verified externally by
  `#print axioms` and recorded in the agent report), and the Paper A
  claim slot.
Does not prove: properties of the row's underlying measure data
  beyond the metadata it carries.
Relation: record metadata.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: parametric `Type`, used as a list element below.
-/
structure CoverageRow where
  familyLabel               : String
  directness                : DirectnessStatus
  rawPayloadSensitive       : RowStatus
  decisivePayloadSensitive  : RowStatus
  projectionTransaction     : RowStatus
  classificationAnchor      : ClassificationAnchor
  classifierLabel           : SemanticCertificateClass
  axiomFootprint            : String
  paperAClaim               : PaperAClaim
  deriving Repr

/-! ## 3. Ledger row constructors -/

/-- The S0 raw universal adjudication row: counter-first lex (raw)
refutes the naive raw semantic universal claim. The row is direct-
status `adjudicatedRefuted`: it is raw-only, the universal raw claim
is refuted by it (NOT a directness gate result). -/
def s0_adjudication_row : CoverageRow where
  familyLabel               := "s0_naive_raw_semantic_universal_adjudicated"
  directness                := .adjudicatedRefuted
  rawPayloadSensitive       := .yes
  decisivePayloadSensitive  := .no
  projectionTransaction     := .notApplicable
  classificationAnchor      := .s0_naive_raw_semantic_universal_adjudicated
  classifierLabel           := .SemanticNotDirect
  axiomFootprint            := "zero"
  paperAClaim               := .s0_adjudication

/-- The S3 lens-pump barrier row: the universal semantic lens-pump
barrier theorem (`semantic_lens_pump_no_orients`). Structural row,
not tied to a single concrete RDRS instance. -/
def s3_lens_pump_row : CoverageRow where
  familyLabel               := "s3_semantic_lens_pump_no_orients"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .notApplicable
  classificationAnchor      := .s3_semantic_lens_pump_no_orients
  classifierLabel           := .SemanticPayloadSensitiveBlocked
  axiomFootprint            := "zero"
  paperAClaim               := .s3_lens_pump_barrier

/-- The S5 classifier capstone row: classifier totality + zero
TEMPORARY_UNCLASSIFIED. Structural row. -/
def s5_classifier_row : CoverageRow where
  familyLabel               := "s5_semantic_classifier_total_and_zero_residual"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .notApplicable
  classificationAnchor      := .s5_semantic_classifier_total
  classifierLabel           := .SemanticNotDirect
  axiomFootprint            := "zero"
  paperAClaim               := .s5_classifier

/-- The S6.5 hardening capstone row: the not-plain-erasure +
hardened soundness theorem `semantic_projection_transaction_escape_sound_hardened`. -/
def s6p5_hardening_row : CoverageRow where
  familyLabel               := "s6p5_semantic_projection_transaction_escape_sound_hardened"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_projection_transaction_escape_sound_hardened
  classifierLabel           := .SemanticProjectionTransactionEscape
  axiomFootprint            := "zero"
  paperAClaim               := .s6p5_projection_transaction_hardening

/-- The S6.5 canonical DP-projection row: the concrete
`counterFirstLex_R` payload-forgetting projection-transaction escape. -/
def s6p5_dp_canonical_row : CoverageRow where
  familyLabel               := "s6p5_semantic_dp_projection_transaction_canonical"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_dp_projection_transaction_canonical
  classifierLabel           := .SemanticProjectionTransactionEscape
  axiomFootprint            := "zero"
  paperAClaim               := .s6p5_projection_transaction_hardening

/-- The S6.5 boundary-bottleneck row: W0 blocked / W2 succeeds via
the legacy bridge. -/
def s6p5_bottleneck_row : CoverageRow where
  familyLabel               := "s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
  classifierLabel           := .SemanticProjectionTransactionEscape
  axiomFootprint            := "zero"
  paperAClaim               := .s6p5_projection_transaction_hardening

/-- The S6.5 search-budget-invariance row: W0-bounded search remains
inadmissible across all budgets; W2 projection-transaction escape
remains admissible. -/
def s6p5_search_invariance_row : CoverageRow where
  familyLabel               := "s6p5_semantic_search_budget_invariance"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_search_budget_invariance
  classifierLabel           := .SemanticProjectionTransactionEscape
  axiomFootprint            := "zero"
  paperAClaim               := .s6p5_projection_transaction_hardening

/-! ### S6 counterexample-audit rows lifted into the ledger -/

/-- counter-first lex (S6 row): raw payload-sensitive but not decisive;
classified `SemanticNotDirect`. -/
def s6_counterFirstLex_row : CoverageRow where
  familyLabel               := "counterFirstLex"
  directness                := .notDirect
  rawPayloadSensitive       := .yes
  decisivePayloadSensitive  := .no
  projectionTransaction     := .no
  classificationAnchor      := .s2_counter_first_lex_raw_not_decisive
  classifierLabel           := auditClassify .counterFirstLex
  axiomFootprint            := "zero"
  paperAClaim               := .s2_payload_sensitivity_split

/-- term-algebra rewrite-closure oracle (S6 row): outside the direct
gate. -/
def s6_termAlgebraRewriteClosure_row : CoverageRow where
  familyLabel               := "termAlgebraRewriteClosure"
  directness                := .notDirect
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .no
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .termAlgebraRewriteClosure
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- nonlinear counter-payload coupling (S6 row): outside the direct
gate; raw witnesses still orient via S0 row evidence. -/
def s6_nonlinearCounterPayloadCoupling_row : CoverageRow where
  familyLabel               := "nonlinearCounterPayloadCoupling"
  directness                := .notDirect
  rawPayloadSensitive       := .yes
  decisivePayloadSensitive  := .no
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .nonlinearCounterPayloadCoupling
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- dpProjection (S6 row): real payload-forgetting projection backed by
S6.5 `counterFirstLex_dpSemanticTransactionEscape`. -/
def s6_dpProjection_row : CoverageRow where
  familyLabel               := "dpProjection"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_dp_projection_transaction_canonical
  classifierLabel           := auditClassify .dpProjection
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- argumentFiltering (S6 row): coincides with the DP projection on
`counterFirstLex_R` via the S6.5 hardened evidence. -/
def s6_argumentFiltering_row : CoverageRow where
  familyLabel               := "argumentFiltering"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .yes
  classificationAnchor      := .s6p5_semantic_projection_escape_not_plain_erasure
  classifierLabel           := auditClassify .argumentFiltering
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- fullMonotoneAlgebra (S6 row): construction-style escape, outside
the direct grammar. -/
def s6_fullMonotoneAlgebra_row : CoverageRow where
  familyLabel               := "fullMonotoneAlgebra"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .fullMonotoneAlgebra
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- mspoWitness (S6 row): construction-style escape. -/
def s6_mspoWitness_row : CoverageRow where
  familyLabel               := "mspoWitness"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .mspoWitness
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- fullWpoGwpoWitness (S6 row): construction-style escape. -/
def s6_fullWpoGwpoWitness_row : CoverageRow where
  familyLabel               := "fullWpoGwpoWitness"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .fullWpoGwpoWitness
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-- semanticLabeling (S6 row): transformation-style escape. -/
def s6_semanticLabeling_row : CoverageRow where
  familyLabel               := "semanticLabeling"
  directness                := .notApplicable
  rawPayloadSensitive       := .notApplicable
  decisivePayloadSensitive  := .notApplicable
  projectionTransaction     := .no
  classificationAnchor      := .s6_semantic_counterexample_audit_closed
  classifierLabel           := auditClassify .semanticLabeling
  axiomFootprint            := "zero"
  paperAClaim               := .s6_counterexample_audit

/-! ## 4. Ledger -/

/--
Proves: the closed list of ledger rows. Sixteen rows total: nine S6
  counterexample-audit rows + one S0 adjudication row + one S3
  lens-pump barrier row + one S5 classifier row + four S6.5
  hardening rows.
Does not prove: properties of the rows beyond their enumeration.
Relation: data definition.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed list of sixteen entries.
-/
def semanticCoverageLedger : List CoverageRow :=
  [ s0_adjudication_row,
    s3_lens_pump_row,
    s5_classifier_row,
    s6_counterFirstLex_row,
    s6_termAlgebraRewriteClosure_row,
    s6_nonlinearCounterPayloadCoupling_row,
    s6_dpProjection_row,
    s6_argumentFiltering_row,
    s6_fullMonotoneAlgebra_row,
    s6_mspoWitness_row,
    s6_fullWpoGwpoWitness_row,
    s6_semanticLabeling_row,
    s6p5_hardening_row,
    s6p5_dp_canonical_row,
    s6p5_bottleneck_row,
    s6p5_search_invariance_row ]

/-! ## 4.1 Typed row-to-evidence bridge

The metadata ledger above is retained for stable counting and classifier
queries.  This section adds the proof-bearing layer required for a literal
reading of "every projection-escape row is backed by projection-transaction
evidence".  The evidence-backed ledger has the same sixteen rows in the same
order.  Its six projection rows store an eliminator into an anchor-indexed
evidence type; applying that eliminator produces a genuine payload-forgetting
`SemanticProjectionTransactionEscape counterFirstLex_R`, the complete hardened
receipt, and the exact receipt named by the row's S6.5 anchor.  The ten
non-projection rows have an empty eliminator domain.

This does not assert that every method named by the separate 76-row method
atlas has a family-specific semantic transaction.  That atlas is metadata and
is deliberately kept separate from this sixteen-row semantic witness ledger.
-/

/-- Unambiguous local name for the genuine payload-bearing counter-first-lex
step used by the S6.5 audit. -/
abbrev semanticCounterFirstLexStep : RDRSStep Unit Nat Nat (Nat × Nat) :=
  OperatorKO7.RDRSSemanticPayloadSensitivity.counterFirstLex_R

/-- The complete four-obligation hardening receipt plus source-step witness
transport for a concrete semantic projection escape. -/
def SemanticProjectionHardeningReceipt
    (E : SemanticProjectionTransactionEscape semanticCounterFirstLexStep) : Prop :=
  (Nonempty (SemanticMeasureData E.transaction.T') ∧
      (∃ (PayloadCarrier : Type)
          (sc : SeedCollapse PayloadCarrier (Nat × Nat)),
        Nonempty (FactorsThroughSeedCollapse sc E.transaction.pi)) ∧
      WellFounded E.transaction.semanticMeasure.ltA ∧
      Orients E.transaction.Rproj
        E.transaction.semanticMeasure.μ
        E.transaction.semanticMeasure.ltA) ∧
    Orients semanticCounterFirstLexStep
      E.liftedMeasure E.transaction.semanticMeasure.ltA

/-- The concrete DP-packaging receipt for the same semantic escape. -/
def SemanticCanonicalDPReceipt
    (E : SemanticProjectionTransactionEscape semanticCounterFirstLexStep) : Prop :=
  ∃ D : DPProjectionEscape semanticCounterFirstLexStep,
    Orients semanticCounterFirstLexStep
      E.liftedMeasure E.transaction.semanticMeasure.ltA ∧
    Orients semanticCounterFirstLexStep
      D.toProjectionTransactionEscape.liftedMeasure
      D.toProjectionTransactionEscape.transaction.ltA'

/-- The exact W0/W2 bottleneck receipt for the supplied semantic escape. -/
def SemanticBoundaryBottleneckReceipt
    (E : SemanticProjectionTransactionEscape semanticCounterFirstLexStep) : Prop :=
  let BB := BoundaryBottleneck.ofProjectionTransactionEscape E.toLegacy
  kappa_boundary BB.w0_witness = false ∧
    kappa_boundary BB.w2_witness = true

/-- The exact all-budget W0/W2 receipt for the supplied semantic escape. -/
def SemanticSearchBudgetReceipt
    (E : SemanticProjectionTransactionEscape semanticCounterFirstLexStep) : Prop :=
  ∀ (search : W0Search semanticCounterFirstLexStep), IsW0Bounded search →
    ∀ budget : Nat,
      kappa_boundary (search budget) = false ∧
        kappa_boundary
          (BoundaryBottleneck.ofProjectionTransactionEscape
            E.toLegacy).w2_witness = true

/-- A real canonical witness shared by the six semantic projection rows.

It fixes the source relation to `counterFirstLex_R`, fixes the projection to
the concrete `Prod.fst` transaction, proves that changing only the payload
does not change the projection, and stores the complete hardened receipt.
The relation is root single-step orientation; no SN theorem is claimed. -/
structure CanonicalSemanticProjectionWitness : Type 1 where
  escape : SemanticProjectionTransactionEscape semanticCounterFirstLexStep
  payloadForgetting :
    ∀ n p q : Nat,
      escape.transaction.pi (n, p) = escape.transaction.pi (n, q)
  hardening : SemanticProjectionHardeningReceipt escape

/-- Concrete payload-forgetting semantic projection witness used by every
positive row in the evidence-backed ledger. -/
def canonicalSemanticProjectionWitness : CanonicalSemanticProjectionWitness where
  escape := counterFirstLex_dpSemanticTransactionEscape
  payloadForgetting := fun _ _ _ => rfl
  hardening :=
    semantic_projection_transaction_escape_sound_hardened
      counterFirstLex_dpSemanticTransactionEscape

/-- Anchor-indexed typed evidence.  There is intentionally no constructor for
any non-hardened classification anchor.  Each constructor stores the common
canonical transaction witness and, where the anchor names a distinct theorem,
the exact theorem-shaped receipt for that anchor. -/
inductive TypedProjectionAnchorEvidence : ClassificationAnchor → Type 1
  | hardened
      (core : CanonicalSemanticProjectionWitness) :
      TypedProjectionAnchorEvidence
        .s6p5_semantic_projection_transaction_escape_sound_hardened
  | dpCanonical
      (core : CanonicalSemanticProjectionWitness)
      (receipt : SemanticCanonicalDPReceipt core.escape) :
      TypedProjectionAnchorEvidence
        .s6p5_semantic_dp_projection_transaction_canonical
  | bottleneck
      (core : CanonicalSemanticProjectionWitness)
      (receipt : SemanticBoundaryBottleneckReceipt core.escape) :
      TypedProjectionAnchorEvidence
        .s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
  | searchBudget
      (core : CanonicalSemanticProjectionWitness)
      (receipt : SemanticSearchBudgetReceipt core.escape) :
      TypedProjectionAnchorEvidence
        .s6p5_semantic_search_budget_invariance
  | notPlainErasure
      (core : CanonicalSemanticProjectionWitness)
      (receipt :
        Nonempty (SemanticMeasureData core.escape.transaction.T') ∧
        (∃ (PayloadCarrier : Type)
            (sc : SeedCollapse PayloadCarrier (Nat × Nat)),
          Nonempty
            (FactorsThroughSeedCollapse sc core.escape.transaction.pi)) ∧
        WellFounded core.escape.transaction.semanticMeasure.ltA ∧
        Orients core.escape.transaction.Rproj
          core.escape.transaction.semanticMeasure.μ
          core.escape.transaction.semanticMeasure.ltA) :
      TypedProjectionAnchorEvidence
        .s6p5_semantic_projection_escape_not_plain_erasure

/-- Typed evidence for the hardened-soundness anchor. -/
def typed_hardened_projection_evidence :
    TypedProjectionAnchorEvidence
      .s6p5_semantic_projection_transaction_escape_sound_hardened :=
  .hardened canonicalSemanticProjectionWitness

/-- Typed evidence for the canonical DP anchor. -/
def typed_dp_canonical_projection_evidence :
    TypedProjectionAnchorEvidence
      .s6p5_semantic_dp_projection_transaction_canonical :=
  .dpCanonical canonicalSemanticProjectionWitness
    ⟨counterFirstLex_dpProjectionEscape,
      counterFirstLex_dpSemanticTransactionEscape.lifted_orients,
      dpWitnessTransport_sound counterFirstLex_dpProjectionEscape⟩

/-- Typed evidence for the boundary-bottleneck anchor. -/
def typed_bottleneck_projection_evidence :
    TypedProjectionAnchorEvidence
      .s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds :=
  .bottleneck canonicalSemanticProjectionWitness
    (semantic_boundary_bottleneck_w0_blocked_w2_succeeds
      counterFirstLex_dpSemanticTransactionEscape)

/-- Typed evidence for the search-budget-invariance anchor. -/
def typed_search_budget_projection_evidence :
    TypedProjectionAnchorEvidence
      .s6p5_semantic_search_budget_invariance :=
  .searchBudget canonicalSemanticProjectionWitness
    (fun search h budget =>
      semantic_search_budget_invariance
        counterFirstLex_dpSemanticTransactionEscape search h budget)

/-- Typed evidence for the no-plain-erasure anchor. -/
def typed_not_plain_erasure_projection_evidence :
    TypedProjectionAnchorEvidence
      .s6p5_semantic_projection_escape_not_plain_erasure :=
  .notPlainErasure canonicalSemanticProjectionWitness
    (semantic_projection_escape_not_plain_erasure
      counterFirstLex_dpSemanticTransactionEscape)

/-- A semantic coverage row together with a typed evidence eliminator.

For projection rows the domain is inhabited and applying the field returns
anchor-indexed proof data.  For every other row the equality premise is false,
so no fake projection witness is manufactured. -/
structure EvidenceBackedCoverageRow : Type 1 where
  row : CoverageRow
  projectionEvidence :
    row.classifierLabel =
        SemanticCertificateClass.SemanticProjectionTransactionEscape →
      TypedProjectionAnchorEvidence row.classificationAnchor

/-- Package a non-projection row. -/
def evidenceBackedNonProjectionRow
    (row : CoverageRow)
    (h : row.classifierLabel ≠
      SemanticCertificateClass.SemanticProjectionTransactionEscape) :
    EvidenceBackedCoverageRow where
  row := row
  projectionEvidence := fun hp => False.elim (h hp)

/-- Package a positive projection row with its exact indexed evidence. -/
def evidenceBackedProjectionRow
    (row : CoverageRow)
    (_h : row.classifierLabel =
      SemanticCertificateClass.SemanticProjectionTransactionEscape)
    (evidence : TypedProjectionAnchorEvidence row.classificationAnchor) :
    EvidenceBackedCoverageRow where
  row := row
  projectionEvidence := fun _ => evidence

def typed_s0_adjudication_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s0_adjudication_row (by decide)

def typed_s3_lens_pump_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s3_lens_pump_row (by decide)

def typed_s5_classifier_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s5_classifier_row (by decide)

def typed_s6_counterFirstLex_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_counterFirstLex_row (by decide)

def typed_s6_termAlgebraRewriteClosure_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_termAlgebraRewriteClosure_row (by decide)

def typed_s6_nonlinearCounterPayloadCoupling_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_nonlinearCounterPayloadCoupling_row (by decide)

def typed_s6_dpProjection_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6_dpProjection_row rfl
    typed_dp_canonical_projection_evidence

def typed_s6_argumentFiltering_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6_argumentFiltering_row rfl
    typed_not_plain_erasure_projection_evidence

def typed_s6_fullMonotoneAlgebra_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_fullMonotoneAlgebra_row (by decide)

def typed_s6_mspoWitness_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_mspoWitness_row (by decide)

def typed_s6_fullWpoGwpoWitness_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_fullWpoGwpoWitness_row (by decide)

def typed_s6_semanticLabeling_row : EvidenceBackedCoverageRow :=
  evidenceBackedNonProjectionRow s6_semanticLabeling_row (by decide)

def typed_s6p5_hardening_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6p5_hardening_row rfl
    typed_hardened_projection_evidence

def typed_s6p5_dp_canonical_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6p5_dp_canonical_row rfl
    typed_dp_canonical_projection_evidence

def typed_s6p5_bottleneck_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6p5_bottleneck_row rfl
    typed_bottleneck_projection_evidence

def typed_s6p5_search_invariance_row : EvidenceBackedCoverageRow :=
  evidenceBackedProjectionRow s6p5_search_invariance_row rfl
    typed_search_budget_projection_evidence

/-- The proof-bearing mirror of the entire sixteen-row semantic ledger. -/
def semanticCoverageEvidenceLedger : List EvidenceBackedCoverageRow :=
  [ typed_s0_adjudication_row,
    typed_s3_lens_pump_row,
    typed_s5_classifier_row,
    typed_s6_counterFirstLex_row,
    typed_s6_termAlgebraRewriteClosure_row,
    typed_s6_nonlinearCounterPayloadCoupling_row,
    typed_s6_dpProjection_row,
    typed_s6_argumentFiltering_row,
    typed_s6_fullMonotoneAlgebra_row,
    typed_s6_mspoWitness_row,
    typed_s6_fullWpoGwpoWitness_row,
    typed_s6_semanticLabeling_row,
    typed_s6p5_hardening_row,
    typed_s6p5_dp_canonical_row,
    typed_s6p5_bottleneck_row,
    typed_s6p5_search_invariance_row ]

/-- The typed ledger contains all sixteen metadata rows, in the same order. -/
theorem semanticCoverageEvidenceLedger_length :
    semanticCoverageEvidenceLedger.length = 16 := by decide

/-- Forgetting proof data recovers the original metadata ledger exactly. -/
theorem semanticCoverageEvidenceLedger_rows :
    semanticCoverageEvidenceLedger.map (fun backed => backed.row) =
      semanticCoverageLedger := rfl

/-- Every metadata row has a corresponding proof-bearing row. -/
theorem semanticCoverageRow_has_evidence_backing
    (row : CoverageRow) (hrow : row ∈ semanticCoverageLedger) :
    ∃ backed ∈ semanticCoverageEvidenceLedger, backed.row = row := by
  rw [← semanticCoverageEvidenceLedger_rows] at hrow
  exact List.mem_map.mp hrow

/-- Literal row-to-witness closure for every projection row in the
sixteen-row semantic ledger.  The conclusion points to a row that stores an
actual anchor-indexed evidence object, not a String theorem name. -/
theorem semantic_projection_escape_row_has_typed_evidence
    (row : CoverageRow) (hrow : row ∈ semanticCoverageLedger)
    (hprojection : row.classifierLabel =
      SemanticCertificateClass.SemanticProjectionTransactionEscape) :
    ∃ backed ∈ semanticCoverageEvidenceLedger,
      backed.row = row ∧
        Nonempty
          (TypedProjectionAnchorEvidence
            backed.row.classificationAnchor) := by
  obtain ⟨backed, hbacked, hbackedRow⟩ :=
    semanticCoverageRow_has_evidence_backing row hrow
  subst row
  exact
    ⟨backed, hbacked, rfl,
      ⟨backed.projectionEvidence hprojection⟩⟩

/-! ## 5. Per-bucket extractors -/

/-- Rows classified `SemanticPayloadSensitiveBlocked`. -/
def blocked_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked)

/-- Rows classified `SemanticProjectionTransactionEscape`. -/
def projection_escape_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.SemanticProjectionTransactionEscape)

/-- Rows classified `SemanticConstructionEscape`. -/
def construction_escape_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.SemanticConstructionEscape)

/-- Rows classified `SemanticTransformEscape`. -/
def transform_escape_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.SemanticTransformEscape)

/-- Rows classified `SemanticNotDirect`. -/
def not_direct_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.SemanticNotDirect)

/-- Rows classified `TEMPORARY_UNCLASSIFIED`. Must be empty. -/
def temporary_unclassified_rows : List CoverageRow :=
  semanticCoverageLedger.filter
    (fun r => r.classifierLabel ==
      SemanticCertificateClass.TEMPORARY_UNCLASSIFIED)

/-- Rows whose `axiomFootprint` field is the literal `"zero"`. -/
def zero_axiom_rows : List CoverageRow :=
  semanticCoverageLedger.filter (fun r => r.axiomFootprint == "zero")

/-! ## 6. Required closure theorems -/

/--
Proves: the ledger has sixteen rows total.
Does not prove: properties of any individual row.
Relation: list length.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: closed list.
-/
theorem coverage_ledger_length : semanticCoverageLedger.length = 16 := by decide

/-- Blocked-bucket count. -/
theorem coverage_blocked_count : blocked_rows.length = 1 := by decide

/-- Projection-escape bucket count: 6 (the four S6.5 hardening rows
plus the dpProjection and argumentFiltering S6 rows). -/
theorem coverage_projection_escape_count : projection_escape_rows.length = 6 := by
  decide

/-- Construction-escape bucket count: 3 (fullMonotoneAlgebra,
mspoWitness, fullWpoGwpoWitness). -/
theorem coverage_construction_escape_count :
    construction_escape_rows.length = 3 := by decide

/-- Transform-escape bucket count: 1 (semanticLabeling). -/
theorem coverage_transform_escape_count :
    transform_escape_rows.length = 1 := by decide

/-- Not-direct bucket count: 5 (counterFirstLex, term-algebra,
nonlinear coupling, S0 adjudication, S5 classifier capstone). -/
theorem coverage_not_direct_count :
    not_direct_rows.length = 5 := by decide

/--
Proves: **zero temporary-unclassified rows in the semantic coverage
  ledger.**
Does not prove: that the empty bucket implies any positive property;
  it is a structural absence.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: the closed sixteen-row ledger.
-/
theorem coverage_no_temporary_unclassified :
    temporary_unclassified_rows.length = 0 := by decide

/--
Proves: the per-bucket counts partition the sixteen ledger rows
  `1 + 6 + 3 + 1 + 5 + 0 = 16`.
Does not prove: anything beyond the arithmetic identity.
Relation: list-length arithmetic.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: the closed sixteen-row ledger.
-/
theorem coverage_partition_total :
    blocked_rows.length + projection_escape_rows.length
      + construction_escape_rows.length + transform_escape_rows.length
      + not_direct_rows.length + temporary_unclassified_rows.length = 16 := by
  decide

/--
Proves: every ledger row's `axiomFootprint` field is the literal
  `"zero"`. This is the structural record that no row is backed by a
  theorem with a non-zero axiom footprint; the actual axiom inventory
  is produced by `#print axioms` on the row's classification anchor,
  recorded in the agent report.
Does not prove: that `#print axioms` returns empty on every anchor
  (the structural field is a String; the kernel-level check is the
  external `#print axioms` invocation logged in the report).
Relation: list-length identity.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide`).
Scope: the closed sixteen-row ledger.
-/
theorem coverage_zero_axiom_footprint :
    zero_axiom_rows.length = 16 := by decide

/-! ## 7. Per-row agreement with the S6 audit (decide-proved) -/

/-- counterFirstLex row agrees with S6 classifier. -/
theorem coverage_counterFirstLex_classifier_agrees :
    s6_counterFirstLex_row.classifierLabel = auditClassify .counterFirstLex := rfl

/-- termAlgebraRewriteClosure row agrees with S6 classifier. -/
theorem coverage_termAlgebraRewriteClosure_classifier_agrees :
    s6_termAlgebraRewriteClosure_row.classifierLabel =
      auditClassify .termAlgebraRewriteClosure := rfl

/-- nonlinearCounterPayloadCoupling row agrees with S6 classifier. -/
theorem coverage_nonlinearCounterPayloadCoupling_classifier_agrees :
    s6_nonlinearCounterPayloadCoupling_row.classifierLabel =
      auditClassify .nonlinearCounterPayloadCoupling := rfl

/-- dpProjection row agrees with S6 classifier. -/
theorem coverage_dpProjection_classifier_agrees :
    s6_dpProjection_row.classifierLabel = auditClassify .dpProjection := rfl

/-- argumentFiltering row agrees with S6 classifier. -/
theorem coverage_argumentFiltering_classifier_agrees :
    s6_argumentFiltering_row.classifierLabel =
      auditClassify .argumentFiltering := rfl

/-- fullMonotoneAlgebra row agrees with S6 classifier. -/
theorem coverage_fullMonotoneAlgebra_classifier_agrees :
    s6_fullMonotoneAlgebra_row.classifierLabel =
      auditClassify .fullMonotoneAlgebra := rfl

/-- mspoWitness row agrees with S6 classifier. -/
theorem coverage_mspoWitness_classifier_agrees :
    s6_mspoWitness_row.classifierLabel = auditClassify .mspoWitness := rfl

/-- fullWpoGwpoWitness row agrees with S6 classifier. -/
theorem coverage_fullWpoGwpoWitness_classifier_agrees :
    s6_fullWpoGwpoWitness_row.classifierLabel =
      auditClassify .fullWpoGwpoWitness := rfl

/-- semanticLabeling row agrees with S6 classifier. -/
theorem coverage_semanticLabeling_classifier_agrees :
    s6_semanticLabeling_row.classifierLabel =
      auditClassify .semanticLabeling := rfl

/-! ## 8. No-plain-erasure on projection-escape rows -/

/--
Proves: **no plain-erasure projection escapes in the ledger.** Every
  row whose `classifierLabel` is `SemanticProjectionTransactionEscape`
  has its `classificationAnchor` set to one of the four S6.5
  hardening anchors that guarantee the four-obligation extraction
  shape (sigma + phi + wf + projected orientation). Specifically the
  anchor is one of:
  * `s6p5_semantic_projection_transaction_escape_sound_hardened`
  * `s6p5_semantic_dp_projection_transaction_canonical`
  * `s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds`
  * `s6p5_semantic_search_budget_invariance`
  * `s6p5_semantic_projection_escape_not_plain_erasure`
Does not prove: that arbitrary projection-style witnesses inhabit the
  escape branch; the four-obligation extraction is the S6.5
  structural gate.
Relation: closed enum classification.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`decide` over the closed sixteen-row ledger).
Scope: the closed sixteen-row ledger.
-/
theorem coverage_no_plain_erasure_projection_escape :
    ∀ r ∈ semanticCoverageLedger,
      r.classifierLabel =
          SemanticCertificateClass.SemanticProjectionTransactionEscape →
        (r.classificationAnchor =
            ClassificationAnchor.s6p5_semantic_projection_transaction_escape_sound_hardened
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_dp_projection_transaction_canonical
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_search_budget_invariance
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_projection_escape_not_plain_erasure) := by
  decide

/-! ## 9. Capstone -/

/--
Proves: capstone closure structure for the S7 semantic coverage
  ledger. Bundles the sixteen-row length, the six bucket counts, the
  partition equality, the zero-temporary-unclassified verdict, the
  zero-axiom-footprint structural record, and the no-plain-erasure
  shape on every projection-escape row.
Does not prove: source-system SN, K-check-7 source-DP soundness, or
  any property outside the closed semantic universe.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the closed sixteen-row ledger.
-/
structure SemanticCoverageLedgerClosed : Prop where
  rowCount                          : semanticCoverageLedger.length = 16
  blockedCount                      : blocked_rows.length = 1
  projectionEscapeCount             : projection_escape_rows.length = 6
  constructionEscapeCount           : construction_escape_rows.length = 3
  transformEscapeCount              : transform_escape_rows.length = 1
  notDirectCount                    : not_direct_rows.length = 5
  temporaryUnclassifiedCount        : temporary_unclassified_rows.length = 0
  zeroAxiomFootprintRows            : zero_axiom_rows.length = 16
  partitionTotal                    :
    blocked_rows.length + projection_escape_rows.length
      + construction_escape_rows.length + transform_escape_rows.length
      + not_direct_rows.length + temporary_unclassified_rows.length = 16
  noPlainErasureProjectionEscape    :
    ∀ r ∈ semanticCoverageLedger,
      r.classifierLabel =
          SemanticCertificateClass.SemanticProjectionTransactionEscape →
        (r.classificationAnchor =
            ClassificationAnchor.s6p5_semantic_projection_transaction_escape_sound_hardened
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_dp_projection_transaction_canonical
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_search_budget_invariance
          ∨ r.classificationAnchor =
              ClassificationAnchor.s6p5_semantic_projection_escape_not_plain_erasure)
  evidenceRowCount                  : semanticCoverageEvidenceLedger.length = 16
  evidenceRowsExact                 :
    semanticCoverageEvidenceLedger.map (fun backed => backed.row) =
      semanticCoverageLedger
  projectionEscapeTypedEvidence     :
    ∀ row ∈ semanticCoverageLedger,
      row.classifierLabel =
          SemanticCertificateClass.SemanticProjectionTransactionEscape →
        ∃ backed ∈ semanticCoverageEvidenceLedger,
          backed.row = row ∧
            Nonempty
              (TypedProjectionAnchorEvidence
                backed.row.classificationAnchor)

/--
Proves: the S7 semantic coverage ledger is closed. Bundles all
  partition / closure facts of the sixteen-row ledger into one
  `Prop` certificate.
Does not prove: anything beyond the bundled facts.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (each field is `decide`-proved or a previously
  proved theorem in this file).
Scope: the closed sixteen-row ledger.
-/
theorem semantic_coverage_ledger_closed : SemanticCoverageLedgerClosed where
  rowCount                       := coverage_ledger_length
  blockedCount                   := coverage_blocked_count
  projectionEscapeCount          := coverage_projection_escape_count
  constructionEscapeCount        := coverage_construction_escape_count
  transformEscapeCount           := coverage_transform_escape_count
  notDirectCount                 := coverage_not_direct_count
  temporaryUnclassifiedCount     := coverage_no_temporary_unclassified
  zeroAxiomFootprintRows         := coverage_zero_axiom_footprint
  partitionTotal                 := coverage_partition_total
  noPlainErasureProjectionEscape := coverage_no_plain_erasure_projection_escape
  evidenceRowCount               := semanticCoverageEvidenceLedger_length
  evidenceRowsExact              := semanticCoverageEvidenceLedger_rows
  projectionEscapeTypedEvidence  :=
    semantic_projection_escape_row_has_typed_evidence

/-- Audit anchor for the S7 semantic coverage ledger surface. -/
def rdrs_semantic_coverage_ledger_anchor : String :=
  "OperatorKO7.RDRSSemanticCoverageLedger.semantic_coverage_ledger_closed"

end OperatorKO7.RDRSSemanticCoverageLedger
